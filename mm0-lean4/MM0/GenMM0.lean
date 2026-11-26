import MM0.MMB

/-!
# Generating a `.mm0` file from an `.mm1` file

`.mm1` files may leave variables undeclared (mm0-rs infers them), which
`.mm0` files may not. `genMM0` writes the `.mm0` counterpart of an `.mm1`
file, keeping its text (math strings, notation) and filling in the binders:

* each `axiom` and `theorem` gets a header with all its binders, read from
  the `.mmb` file mm0-rs compiles from the `.mm1` (with names from its
  debugging index), then its hypotheses and conclusion as written, and no
  proof;
* each `def` keeps its text, with the dummies it uses declared (`{.x: s}`);
* everything else (sorts, terms, notations, delimiters) is copied as is.

This is a tool, not part of the trusted base: whatever it writes is checked
afterwards, by parsing it and by `mm0-lean verify FILE.mm0 FILE.mmb`, which
needs every statement to be exactly the one the `.mmb` proves.
-/

namespace MM0.GenMM0

open MM0.MMB

/-! ## The debugging index -/

/-- A null-terminated string. -/
partial def cstrAt (b : ByteArray) (i : Nat) (acc : Array UInt8 := #[]) : Except String String := do
  let c ← u8At b i
  if c == 0 then
    match String.fromUTF8? (ByteArray.mk acc) with
    | some s => return s
    | none => throw "bad UTF-8 in a name"
  else cstrAt b (i + 1) (acc.push c.toUInt8)

def strListAt (b : ByteArray) (p : Nat) : Except String (Array String) := do
  if p == 0 then return #[]
  let n ← u64At b p
  let mut out := #[]
  for k in [0:n] do
    let q ← u64At b (p + 8 + 8 * k)
    let s ← if q == 0 then pure "_" else cstrAt b q
    out := out.push s
  return out

structure Index where
  sortNames : Array String
  termNames : Array String
  thmNames : Array String
  termVars : Array (Array String)
  thmVars : Array (Array String)

def readIndex (b : ByteArray) (f : File) : Except String Index := do
  let pIndex ← u64At b 32
  if pIndex == 0 then throw "the .mmb file has no debugging index (compile without --strip)"
  let n ← u64At b pIndex
  let mut names := 0
  let mut vars := 0
  for k in [0:n] do
    let e := pIndex + 8 + 16 * k
    let ty ← u32At b e
    let ptr ← u64At b (e + 8)
    if ty == 0x656D614E then names := ptr
    if ty == 0x4E726156 then vars := ptr
  if names == 0 || vars == 0 then throw "the index has no Name or VarN table"
  let name (i : Nat) : Except String String := do
    let q ← u64At b (names + 16 * i + 8)
    if q == 0 then pure "_" else cstrAt b q
  let ns := f.sorts.size
  let nt := f.terms.size
  let nh := f.thms.size
  let sortNames ← (Array.range ns).mapM name
  let termNames ← (Array.range nt).mapM fun i => name (ns + i)
  let thmNames ← (Array.range nh).mapM fun i => name (ns + nt + i)
  let termVars ← (Array.range nt).mapM fun i => do strListAt b (← u64At b (vars + 8 * i))
  let thmVars ← (Array.range nh).mapM fun i => do strListAt b (← u64At b (vars + 8 * (nt + i)))
  return { sortNames, termNames, thmNames, termVars, thmVars }

/-! ## Splitting the `.mm1` text into statements -/

/-- The statements of a file, as text (with their trailing `;`), skipping
comments between them. A statement ends at a `;` outside math strings,
comments and string literals. -/
def statements (src : String) : Array String := Id.run do
  let cs := src.toList.toArray
  let mut out := #[]
  let mut cur := ""
  let mut i := 0
  let mut inMath := false
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    let c := cs[i]!
    if !inMath && c == '-' && i + 1 < cs.size && cs[i+1]! == '-' then
      -- comment to end of line: drop it
      while i < cs.size && cs[i]! != '\n' do i := i + 1
      if cur.trimAscii.isEmpty then cur := "" else cur := cur.push '\n'
      i := i + 1
      continue
    if c == '$' then inMath := !inMath
    cur := cur.push c
    if !inMath && c == ';' then
      out := out.push cur.trimAscii.toString
      cur := ""
    i := i + 1
  return out

/-- The first word of a statement. -/
def keyword (s : String) : String :=
  (s.splitOn " " |>.head!).splitOn "\n" |>.head!

/-- The math strings of a statement, in order, up to its proof (`=` outside
math strings, after the binders). -/
def mathStrings (s : String) : Array String := Id.run do
  let cs := s.toList.toArray
  let mut out := #[]
  let mut cur := ""
  let mut inMath := false
  let mut depth := 0
  let mut seenColon := false
  for c in cs do
    if inMath then
      if c == '$' then out := out.push cur; cur := ""; inMath := false
      else cur := cur.push c
    else
      if c == '$' then inMath := true
      else if c == '(' || c == '{' then depth := depth + 1
      else if c == ')' || c == '}' then depth := depth - 1
      else if c == ':' && depth == 0 then seenColon := true
      else if c == '=' && depth == 0 && seenColon then break
  return out

/-- The math strings of a statement's hypothesis binders, `(h: $ … $)`. These
come first among `mathStrings` (binders precede the arrow type). -/
def numHypBinders (s : String) : Nat := Id.run do
  -- count `$` math strings that occur inside parentheses before the top-level `:`
  let cs := s.toList.toArray
  let mut n := 0
  let mut depth := 0
  let mut inMath := false
  for c in cs do
    if inMath then
      if c == '$' then inMath := false
    else
      if c == '$' then
        inMath := true
        if depth > 0 then n := n + 1
      else if c == '(' || c == '{' then depth := depth + 1
      else if c == ')' || c == '}' then depth := depth - 1
      else if c == ':' && depth == 0 then break
  return n

/-! ## Notations -/

/-- A notation `.mm0` can parse: prefix and infix operators, and general
notations that begin with a constant. -/
inductive Nota
  | prefix (tk : String)
  | infix (tk : String)
  /-- The literals: `.inl tk` for a constant, `.inr k` for argument `k`. -/
  | general (lits : List (String ⊕ Nat))

/-- The words of a statement, with `$ … $` kept as one word. -/
def words (s : String) : List String := Id.run do
  let mut out := #[]
  let mut cur := ""
  let mut inMath := false
  for c in s.toList do
    if inMath then
      cur := cur.push c
      if c == '$' then out := out.push cur; cur := ""; inMath := false
    else if c == '$' then
      if cur ≠ "" then out := out.push cur
      cur := "$"; inMath := true
    else if c == ' ' || c == '\n' || c == '(' || c == ')' || c == ':' || c == ';' then
      if cur ≠ "" then out := out.push cur
      cur := ""
      if c != ' ' && c != '\n' then out := out.push (String.singleton c)
    else cur := cur.push c
  if cur ≠ "" then out := out.push cur
  return out.toList

def mathTok (w : String) : String := (w.drop 1 |>.dropEnd 1).trimAscii.toString

/-- The notations of the `.mm1` text, by term name, and the general ones
`.mm0` cannot parse (they begin with a variable). -/
def notations (stmts : Array String) : List (String × Nota) × List String := Id.run do
  let mut out := []
  let mut dropped := []
  for s in stmts do
    match words s with
    | "prefix" :: t :: ":" :: tk :: _ => out := (t, .prefix (mathTok tk)) :: out
    | "infixl" :: t :: ":" :: tk :: _ | "infixr" :: t :: ":" :: tk :: _ =>
      out := (t, .infix (mathTok tk)) :: out
    | "notation" :: t :: "(" :: rest =>
      let vars := rest.takeWhile (· != ")")
      let lits := (rest.dropWhile (· != "=")).drop 1
      -- literals: `( $tk$ : prec )` or a variable name; stop at a trailing `:` or `;`
      let rec go : List String → List (String ⊕ Nat)
        | "(" :: tk :: ":" :: _ :: ")" :: ws => .inl (mathTok tk) :: go ws
        | w :: ws => if w == ":" || w == ";" then [] else
            match vars.idxOf? w with
            | some k => .inr k :: go ws
            | none => go ws
        | [] => []
      let ls := go lits
      match ls with
      | .inl _ :: _ => out := (t, .general ls) :: out
      | _ => dropped := t :: dropped
    | _ => pure ()
  return (out, dropped)

/-! ## Printing -/

structure Ctx' where
  idx : Index
  notas : List (String × Nota)
  names : Array String

/-- Print an expression with the notations `.mm0` can parse; arguments that
are not atoms are parenthesized. -/
partial def render (c : Ctx') : SExpr → String × Bool
  | .var v => (c.names[v]?.getD s!"v{v}", true)
  | .app t es =>
    let name := c.idx.termNames[t]?.getD s!"t{t}"
    let arg (e : SExpr) := let (s, atom) := render c e; if atom then s else s!"({s})"
    match c.notas.lookup name, es with
    | _, [] => match c.notas.lookup name with
      | some (.prefix tk) => (tk, true)
      | _ => (name, true)
    | some (.prefix tk), _ => (" ".intercalate (tk :: es.map arg), false)
    | some (.infix tk), [a, b] => (s!"{arg a} {tk} {arg b}", false)
    | some (.general lits), _ =>
      (" ".intercalate (lits.map fun
        | .inl tk => tk
        | .inr k => (es[k]?.map arg).getD "?"), false)
    | _, _ => (" ".intercalate (name :: es.map arg), false)

def math (c : Ctx') (e : SExpr) : String := s!"$ {(render c e).1} $"

/-! ## Writing binders -/

def depsText (names : Array String) (args : Array Arg) (d : Nat) : String :=
  let boundIdx := (List.range args.size).filter fun j => args[j]!.bound
  String.join ((List.range boundIdx.length).filterMap fun j =>
    if d / 2 ^ j % 2 == 1 then boundIdx[j]?.map fun k => " " ++ names[k]?.getD s!"v{k}" else none)

def binderText (idx : Index) (names : Array String) (args : Array Arg) (i : Nat) : String :=
  let x := names[i]?.getD s!"v{i}"
  let a := args[i]!
  let s := idx.sortNames[a.sort]?.getD s!"s{a.sort}"
  if a.bound then s!"\{{x}: {s}}" else s!"({x}: {s}{depsText names args a.deps})"

/-! ## The generator -/
/-- The statement kind of each term and theorem, by `.mmb` index (`0x05`
term or public def, `0x0D` local def; `0x02` axiom, `0x06` theorem, `0x0E`
local theorem). In `.mm1`, a plain `theorem` is local: a lemma of the proof
file, not part of the `.mm0` interface. -/
def stmtKinds (f : File) : Except String (Array Nat × Array Nat) := do
  let mut pos := f.proof
  let mut terms := #[]
  let mut thms := #[]
  for _ in [0:10000000] do
    let (cmd, data, _) ← cmdAt f.bytes pos
    if cmd == 0 then break
    if cmd == 0x05 || cmd == 0x0D then terms := terms.push cmd
    if cmd == 0x02 || cmd == 0x06 || cmd == 0x0E then thms := thms.push cmd
    pos := pos + data
  return (terms, thms)

/-- Precedence levels that general notations ending in a variable, or
`infixr` operators, use as right-associative. mm0-c rejects an `infixl` at
such a level ("precedence level is both left and right assoc"). -/
def rightLevels (stmts : Array String) : List String := Id.run do
  let mut out := []
  for s in stmts do
    match words s with
    | "infixr" :: _ :: ":" :: _ :: "prec" :: p :: _ => out := p :: out
    | "notation" :: _ :: "(" :: rest =>
      match (rest.dropWhile (· != "=")).drop 1 with
      | "(" :: _ :: ":" :: p :: ")" :: _ => out := p :: out
      | _ => pure ()
    | _ => pure ()
  return out


/-- Write the `.mm0` counterpart of an `.mm1` source, given the `.mmb` file
mm0-rs compiled from it. -/
def genMM0 (src : String) (b : ByteArray) : Except String String := do
  let f ← readFile b
  let idx ← readIndex b f
  let ids : IdMap := Array.range f.terms.size
  let stmts := statements src
  let (notas, dropped) := notations stmts
  let (termKinds, thmKinds) ← stmtKinds f
  let right := rightLevels stmts
  let mut fresh := 1000
  let mut out := #[]
  let mut nTerm := 0
  let mut nThm := 0
  for s in stmts do
    match keyword s with
    | "term" =>
      nTerm := nTerm + 1
      out := out.push s
    | "def" =>
      let some te := f.terms[nTerm]? | throw s!"term {nTerm} missing from the .mmb file"
      let name := idx.termNames[nTerm]?.getD s!"t{nTerm}"
      let names := idx.termVars[nTerm]?.getD #[]
      let n := te.args.size
      let (ds, body) ← decodeDef f ids te
      let bis := (List.range n).map (binderText idx names te.args)
      let dummies := (List.range ds.length).map fun k =>
        s!"\{.{names[n + k]?.getD s!"d{k}"}: {idx.sortNames[ds[k]!]?.getD ""}}"
      let ret := s!"{idx.sortNames[te.ret.sort]?.getD ""}{depsText names te.args te.ret.deps}"
      let header := " ".intercalate (name :: bis ++ dummies)
      unless termKinds[nTerm]? == some 0x0D do
        out := out.push s!"def {header}: {ret} =\n  {math ⟨idx, notas, names⟩ body};"
      nTerm := nTerm + 1
    | "axiom" | "theorem" =>
      let some te := f.thms[nThm]? | throw s!"theorem {nThm} missing from the .mmb file"
      let name := idx.thmNames[nThm]?.getD s!"t{nThm}"
      let names := idx.thmVars[nThm]?.getD #[]
      let bis := (List.range te.args.size).map (binderText idx names te.args)
      let (hs, concl) ← decodeThm f ids te
      let c : Ctx' := ⟨idx, notas, names⟩
      let arrow := " >\n  ".intercalate ((hs ++ [concl]).map (math c))
      let header := " ".intercalate (name :: bis)
      -- local theorems are lemmas of the proof file, not part of the interface
      unless thmKinds[nThm]? == some 0x0E do
        out := out.push s!"{keyword s} {header}:\n  {arrow};"
      nThm := nThm + 1
    | "notation" =>
      match words s with
      | _ :: t :: _ =>
        if dropped.contains t then
          out := out.push s!"-- `{t}` has a notation in the .mm1 file that .mm0 cannot express \
            (it begins with a variable); it is written in prefix form here."
        else
          -- rewrite with typed binders, taken from the term
          match idx.termNames.idxOf? t, notas.lookup t with
          | some k, some (.general lits) =>
            let some te := f.terms[k]? | throw s!"{t}: unknown term"
            let vars := match words s with
              | _ :: _ :: "(" :: rest => (rest.takeWhile (· != ")")).toArray
              | _ => #[]
            let bis := (List.range te.args.size).map (binderText idx vars te.args)
            let ret := s!"{idx.sortNames[te.ret.sort]?.getD ""}{depsText vars te.args te.ret.deps}"
            -- precedences: copied from the source literals
            let litText := (words s |>.dropWhile (· != "=") |>.drop 1)
            let rec go : List String → List String
              | "(" :: tk :: ":" :: p :: ")" :: ws => s!"({tk}:{p})" :: go ws
              | w :: ws => if w == ":" || w == ";" then [] else w :: go ws
              | [] => []
            let _ := lits
            out := out.push s!"notation {" ".intercalate (t :: bis)}: {ret} = {" ".intercalate (go litText)};"
          | _, _ => out := out.push s
      | _ => out := out.push s
    | "infixl" =>
      -- move off a level that is also used right-associatively; statements
      -- are printed with every compound argument parenthesized, so the
      -- level does not change what they mean
      match words s with
      | _ :: t :: ":" :: tk :: "prec" :: p :: _ =>
        if right.contains p then
          out := out.push s!"infixl {t}: {tk} prec {fresh};"
          fresh := fresh + 1
        else out := out.push s
      | _ => out := out.push s
    | _ => out := out.push s
  return "\n".intercalate out.toList ++ "\n"

end MM0.GenMM0
