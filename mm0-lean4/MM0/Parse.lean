import MM0.Spec

/-!
The `.mm0` parser and elaborator (Plan.md, M1): from the bytes of a `.mm0` file
to an `MM0.Env` (`MM0/Spec.lean`).

It follows `mm0.md` (lexing, statement grammar, secondary lexing with
delimiters, the operator-precedence grammar for math strings, coercions,
type checking, definition checking). Where `mm0.md` leaves a choice to the
verifier, it follows what `mm0-rs` and `mm0-c` do, because the differential
tests (`MM0Sanity/Fuzz.lean`) compare verdicts with them:

* notations must be declared before they are used (one pass);
* sort modifiers must come in the order `pure strict provable free`
  (`mm0-c` checks this, `mm0-rs` does not);
* a definition's dummies must not have a `strict` or `free` sort, and every
  free bound variable of its body must be in the return dependencies
  (as in `mm0-c`; `examples/mm0.mm0`'s `DefOk` is weaker, see Plan.md).
-/

namespace MM0.Parse

/-! ## Primary lexing -/

inductive Tok
  | sym (c : Char)
  | ident (s : String)
  | num (n : Nat)
  | math (s : String)
  /-- `"…"`, only for `import` (an `mm0-rs` extension, not in `mm0.md`). -/
  | str (s : String)
  deriving BEq, Repr, Inhabited

def Tok.describe : Tok → String
  | .sym c => s!"'{c}'"
  | .ident s => s!"identifier '{s}'"
  | .num n => s!"number {n}"
  | .math _ => "math string"
  | .str _ => "string"

structure Lexeme where
  tok : Tok
  pos : Nat
  deriving Inhabited

def trimWs (s : String) : String :=
  let ws (c : Char) := c == ' ' || c == '\n'
  String.ofList ((s.toList.dropWhile ws).reverse.dropWhile ws).reverse

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'
def isSymbol (c : Char) : Bool := "*.:;()>{}=_".contains c
/-- Characters allowed in a math string: printable ASCII except `$`, and the
two whitespace characters. -/
def isMathChar (c : Char) : Bool :=
  c == ' ' || c == '\n' || (c.toNat ≥ 0x21 && c.toNat ≤ 0x7e && c != '$')

def lex (src : String) : Except String (Array Lexeme) := Id.run do
  let cs := src.toList.toArray
  let n := cs.size
  let mut i := 0
  let mut out : Array Lexeme := #[]
  -- Fuel: each iteration consumes at least one character.
  for _ in [0:n+1] do
    if i ≥ n then break
    let c := cs[i]!
    if c == ' ' || c == '\n' then
      i := i + 1
    else if c == '-' && i + 1 < n && cs[i+1]! == '-' then
      -- line comment, up to and including the newline
      let mut j := i + 2
      while j < n && cs[j]! != '\n' do j := j + 1
      i := j + 1
    else if c == '$' then
      let mut j := i + 1
      while j < n && cs[j]! != '$' do
        if !isMathChar cs[j]! then
          return .error s!"{j}: invalid character in math string"
        j := j + 1
      if j ≥ n then return .error s!"{i}: unclosed math string"
      out := out.push ⟨.math (String.ofList (cs.toList.drop (i+1) |>.take (j - i - 1))), i⟩
      i := j + 1
    else if isIdentChar c then
      let mut j := i
      while j < n && isIdentChar cs[j]! do j := j + 1
      let w := String.ofList (cs.toList.drop i |>.take (j - i))
      if c.isDigit then
        if w.all Char.isDigit && (w == "0" || c != '0') then
          out := out.push ⟨.num w.toNat!, i⟩
        else
          return .error s!"{i}: invalid number or identifier '{w}'"
      else if w == "_" then
        out := out.push ⟨.sym '_', i⟩
      else
        out := out.push ⟨.ident w, i⟩
      i := j
    else if c == '"' then
      let mut j := i + 1
      while j < n && cs[j]! != '"' && cs[j]! != '\n' do j := j + 1
      if j ≥ n || cs[j]! != '"' then return .error s!"{i}: unclosed string"
      out := out.push ⟨.str (String.ofList (cs.toList.drop (i+1) |>.take (j - i - 1))), i⟩
      i := j + 1
    else if isSymbol c then
      out := out.push ⟨.sym c, i⟩
      i := i + 1
    else
      return .error s!"{i}: invalid character (code {c.toNat})"
  return .ok out

/-! ## Statements -/

inductive Prec
  | num (n : Nat)
  | max
  deriving BEq, Repr, Inhabited

def Prec.le : Prec → Prec → Bool
  | _, .max => true
  | .max, .num _ => false
  | .num a, .num b => a ≤ b

def Prec.succ : Prec → Prec
  | .num n => .num (n + 1)
  | .max => .max

/-- A binder's type: a sort with dependencies, or a formula (hypothesis). -/
inductive BType
  | sort (s : String) (deps : List String)
  | formula (m : String)
  deriving Repr, Inhabited

inductive BKind
  | bound
  | reg
  | dummy
  deriving BEq, Repr, Inhabited

/-- A binder; `name = none` is `_`. -/
structure RBinder where
  name : Option String
  kind : BKind
  ty : BType
  deriving Repr, Inhabited

inductive NotaLit
  | const (tk : String) (p : Prec)
  | var (x : String)
  deriving Repr, Inhabited

inductive SimpleKind
  | prefix
  | infixl
  | infixr
  deriving BEq, Repr, Inhabited

inductive Stmt
  | sort (name : String) (sd : SortData)
  | term (name : String) (bis : List RBinder) (ret : String × List String)
  | assert (thm : Bool) (name : String) (bis : List RBinder) (concl : String)
  | defn (name : String) (bis : List RBinder) (ret : String × List String)
      (body : Option String)
  | delimiter (left right : List String)
  | simple (k : SimpleKind) (term : String) (tk : String) (p : Prec)
  | coercion (term : String) (src tgt : String)
  | notation (term : String) (bis : List RBinder) (ret : String × List String)
      (lits : List NotaLit)
  | inout (input : Bool)
  | import (path : String)
  deriving Repr, Inhabited

abbrev P := StateT Nat (Except String)

def fail (msg : String) : ReaderT (Array Lexeme) P α := fun ts => do
  let i ← get
  let pos := if h : i < ts.size then ts[i].pos else
    if ts.size = 0 then 0 else ts[ts.size - 1]!.pos
  throw s!"{pos}: {msg}"

abbrev SP := ReaderT (Array Lexeme) P

def peek : SP (Option Tok) := fun ts => do
  let i ← get
  return ts[i]?.map (·.tok)

def advance : SP Unit := fun _ => modify (· + 1)

def next : SP Tok := do
  match ← peek with
  | some t => advance; return t
  | none => fail "unexpected end of file"

def expectSym (c : Char) : SP Unit := do
  match ← next with
  | .sym d => if c == d then return () else fail s!"expected '{c}'"
  | t => fail s!"expected '{c}', got {t.describe}"

def ident : SP String := do
  match ← next with
  | .ident s => return s
  | t => fail s!"expected identifier, got {t.describe}"

def mathStr : SP String := do
  match ← next with
  | .math s => return s
  | t => fail s!"expected math string, got {t.describe}"

def isSym (c : Char) : SP Bool := do
  return (← peek) == some (.sym c)

def isIdent (s : String) : SP Bool := do
  return (← peek) == some (.ident s)

/-- Repeat `p` while `cond` holds, with fuel bounded by the token count. -/
partial def many (cond : SP Bool) (p : SP α) : SP (List α) := do
  if ← cond then
    let a ← p
    return a :: (← many cond p)
  else return []

def isIdentTok : SP Bool := do
  match ← peek with
  | some (.ident _) => return true
  | _ => return false

/-- `type ::= identifier (identifier)*` -/
def parseType : SP (String × List String) := do
  let s ← ident
  let ds ← many isIdentTok ident
  return (s, ds)

def parsePrec : SP Prec := do
  match ← next with
  | .num n => return .num n
  | .ident "max" => return .max
  | t => fail s!"expected precedence, got {t.describe}"

/-- Binders. `formulas`: whether `( … : $ … $)` is allowed; `dummies`: whether
`.x` is allowed. -/
def parseBinder (formulas dummies : Bool) : SP (List RBinder) := do
  let curly ← isSym '{'
  advance
  let names ← many (do
      match ← peek with
      | some (.ident _) | some (.sym '_') => return true
      | some (.sym '.') => return dummies
      | _ => return false) (do
      match ← next with
      | .ident s => return (BKind.reg, some s)
      | .sym '_' => return (BKind.reg, none)
      | _ => return (BKind.dummy, some (← ident)))
  expectSym ':'
  let ty ← do
    match ← peek with
    | some (.math _) =>
      if formulas && !curly then pure (BType.formula (← mathStr))
      else fail "formula not allowed here"
    | _ => let (s, ds) ← parseType; pure (BType.sort s ds)
  expectSym (if curly then '}' else ')')
  names.mapM fun (k, x) => do
    if curly && k == .reg && x.isNone then fail "'_' is not allowed in a bound binder"
    let k := if k == .dummy then .dummy else if curly then .bound else .reg
    return { name := x, kind := k, ty }

def isBinderStart : SP Bool := do return (← isSym '(') || (← isSym '{')

/-- Arrow types: `ty > ty > … > ty`. Returns the anonymous binders and the
final piece. -/
partial def parseArrow (formulas : Bool) : SP (List RBinder × BType) := do
  let piece ← do
    match ← peek with
    | some (.math _) =>
      if formulas then pure (BType.formula (← mathStr)) else fail "formula not allowed here"
    | _ => let (s, ds) ← parseType; pure (BType.sort s ds)
  if ← isSym '>' then
    advance
    let (bis, r) ← parseArrow formulas
    return ({ name := none, kind := .reg, ty := piece } :: bis, r)
  else return ([], piece)

def sortRet : BType → SP (String × List String)
  | .sort s ds => return (s, ds)
  | .formula _ => fail "expected a type"

def formulaRet : BType → SP String
  | .formula m => return m
  | .sort _ _ => fail "expected a formula"

def parseStmt : SP Stmt := do
  let kw ← ident
  match kw with
  | "pure" | "strict" | "provable" | "free" | "sort" =>
    -- modifiers in the fixed order pure strict provable free
    let mut sd : SortData := {}
    let mut w := kw
    let mods := ["pure", "strict", "provable", "free"]
    let mut rest := mods
    while w != "sort" do
      match rest.dropWhile (· != w) with
      | [] => fail s!"unexpected '{w}' (modifiers must be in the order pure strict provable free)"
      | _ :: r =>
        rest := r
        sd := match w with
          | "pure" => { sd with pure := true }
          | "strict" => { sd with strict := true }
          | "provable" => { sd with provable := true }
          | _ => { sd with free := true }
        w ← ident
    let name ← ident
    expectSym ';'
    return .sort name sd
  | "term" =>
    let name ← ident
    let bis := (← many isBinderStart (parseBinder false false)).flatten
    expectSym ':'
    let (bis', r) ← parseArrow false
    expectSym ';'
    return .term name (bis ++ bis') (← sortRet r)
  | "axiom" | "theorem" =>
    let name ← ident
    let bis := (← many isBinderStart (parseBinder true false)).flatten
    expectSym ':'
    let (bis', r) ← parseArrow true
    expectSym ';'
    return .assert (kw == "theorem") name (bis ++ bis') (← formulaRet r)
  | "def" =>
    let name ← ident
    let bis := (← many isBinderStart (parseBinder false true)).flatten
    expectSym ':'
    let (bis', r) ← parseArrow false
    let body ← if ← isSym '=' then advance; pure (some (← mathStr)) else pure none
    expectSym ';'
    return .defn name (bis ++ bis') (← sortRet r) body
  | "delimiter" =>
    let a ← mathStr
    let b ← do match ← peek with
      | some (.math _) => pure (some (← mathStr))
      | _ => pure none
    expectSym ';'
    let words (s : String) := (s.splitOn " " |>.flatMap (·.splitOn "\n")).filter (· ≠ "")
    match b with
    | none => return .delimiter (words a) (words a)
    | some b => return .delimiter (words a) (words b)
  | "prefix" | "infixl" | "infixr" =>
    let t ← ident
    expectSym ':'
    let c ← mathStr
    unless (← isIdent "prec") do fail "expected 'prec'"
    advance
    let p ← parsePrec
    expectSym ';'
    let k := if kw == "prefix" then SimpleKind.prefix
      else if kw == "infixl" then .infixl else .infixr
    return .simple k t (trimWs c) p
  | "coercion" =>
    let t ← ident
    expectSym ':'
    let a ← ident
    expectSym '>'
    let b ← ident
    expectSym ';'
    return .coercion t a b
  | "notation" =>
    let t ← ident
    let bis := (← many isBinderStart (parseBinder false false)).flatten
    expectSym ':'
    let ret ← parseType
    expectSym '='
    let precConst : SP NotaLit := do
      expectSym '('
      let c ← mathStr
      expectSym ':'
      let p ← parsePrec
      expectSym ')'
      return .const (trimWs c) p
    let first ← precConst
    let lits ← many (do
        match ← peek with
        | some (.ident _) | some (.sym '(') => return true
        | _ => return false) (do
        match ← peek with
        | some (.ident x) => advance; return NotaLit.var x
        | _ => precConst)
    expectSym ';'
    return .notation t bis ret (first :: lits)
  | "import" =>
    match ← next with
    | .str p => expectSym ';'; return .import p
    | t => fail s!"expected a string, got {t.describe}"
  | "input" | "output" =>
    let _ ← ident
    expectSym ':'
    let _ ← many (do
        match ← peek with
        | some (.ident _) | some (.math _) => return true
        | _ => return false) next
    expectSym ';'
    return .inout (kw == "input")
  | _ => fail s!"unknown statement '{kw}'"

def parseFile (src : String) : Except String (Array Stmt) := do
  let ts ← lex src
  let go : SP (List Stmt) := many (do return (← peek).isSome) parseStmt
  let (r, _) ← (go ts).run 0
  return r.toArray

/-! ## Elaboration -/

structure TermInfo where
  name : String
  args : List Binder
  ret : DepType
  deriving Inhabited

/-- Elaborated expressions with their sort. -/
structure Typed where
  e : SExpr
  sort : SortId
  deriving Inhabited

inductive Nota
  | prefix (t : TermId) (p : Prec)
  | infix (t : TermId) (p : Prec) (right : Bool)
  | general (t : TermId) (p : Prec) (lits : List NotaLit) (vars : List String)
  deriving Inhabited

structure ElabState where
  sorts : Array (String × SortData) := #[]
  terms : Array TermInfo := #[]
  thms : List String := []
  env : Array Decl := #[]
  leftDelims : List Char := []
  rightDelims : List Char := []
  /-- First tokens of notations (prefix, general) and infix operators. -/
  notas : List (String × Nota) := []
  /-- Precedence of each infixy constant. -/
  infixy : List (String × Prec) := []
  /-- Associativity of each precedence level used by an infix operator
  (`true`: right). -/
  assoc : List (Prec × Bool) := []
  /-- Coercion edges `(src, tgt, term)`. -/
  coes : List (SortId × SortId × TermId) := []
  deriving Inhabited

abbrev E := StateT ElabState (Except String)

def findIdx (l : List α) (p : α → Bool) : Option Nat := l.findIdx? p

def sortId (s : String) : E SortId := do
  match findIdx (← get).sorts.toList (·.1 == s) with
  | some i => return i
  | none => throw s!"unknown sort '{s}'"

def termId? (s : String) : E (Option TermId) := do
  return findIdx (← get).terms.toList (·.name == s)

/-- Secondary lexing of a math string. -/
def mathTokens (st : ElabState) (s : String) : List String := Id.run do
  let words := (s.splitOn " " |>.flatMap (·.splitOn "\n")).filter (· ≠ "")
  let mut out := #[]
  for w in words do
    let mut cur := ""
    for c in w.toList do
      if st.rightDelims.contains c then
        if cur ≠ "" then out := out.push cur
        cur := ""
      cur := cur.push c
      if st.leftDelims.contains c then
        out := out.push cur
        cur := ""
    if cur ≠ "" then out := out.push cur
  return out.toList

/-- A variable context for elaborating formulas: name, sort, bound? -/
abbrev VarCtx := List (String × SortId × Bool)

/-- The unique coercion path from `a` to `b`, as a list of terms. -/
partial def coePath (coes : List (SortId × SortId × TermId)) (a b : SortId)
    (visited : List SortId := []) : Option (List TermId) :=
  if a == b then some [] else
  coes.findSome? fun (x, y, t) =>
    if x == a && !visited.contains y then
      (coePath coes y b (a :: visited)).map (t :: ·)
    else none

def coerce (x : Typed) (s : SortId) : E SExpr := do
  match coePath (← get).coes x.sort s with
  | some path => return path.foldl (fun e t => .app1 (.term t) e) x.e
  | none =>
    let st ← get
    throw s!"type mismatch: expected {st.sorts[s]!.1}, got {st.sorts[x.sort]!.1}"

structure MathState where
  toks : List String

abbrev M := ReaderT VarCtx (StateT (List String) E)

def mpeek : M (Option String) := do return (← get).head?
def mnext : M String := do
  match ← get with
  | t :: ts => set ts; return t
  | [] => throw "unexpected end of math string"

/-- Consume the single character `c` (`(` or `)`) at the start of the next
token, leaving the rest of the token. `mm0-rs` reads grouping parentheses
character by character, so `(p)-> q` parses even though `)` is only a right
delimiter there; `mm0.md` reserves `(` and `)` for grouping but does not
settle this case. -/
def mchar (c : Char) : M Bool := do
  match ← get with
  | t :: ts =>
    if t == c.toString then set ts; return true
    else if t.front == c then set (String.ofList (t.toList.drop 1) :: ts); return true
    else return false
  | [] => return false

def lookupNota (tk : String) : M (Option Nota) := do
  return ((← getThe ElabState).notas.lookup tk)

mutual
/-- Elaborate an argument against binder `bi` of a term. -/
partial def elabArg (x : Typed) (bi : Binder) : M SExpr := do
  match bi with
  | .bound s =>
    match x.e with
    | .var v =>
      let ctx ← read
      if (ctx[v]?.map (·.2.2)) == some true && x.sort == s then return x.e
      else throw "expected a bound variable"
    | _ => throw "expected a bound variable"
  | .reg s _ => coerce x s

partial def applyTerm (t : TermId) (args : List Typed) : M Typed := do
  let info := (← getThe ElabState).terms[t]!
  unless args.length == info.args.length do throw s!"wrong number of arguments to {info.name}"
  let mut e := SExpr.term t
  for (a, bi) in args.zip info.args do
    e := .app1 e (← elabArg a bi)
  return ⟨e, info.ret.1⟩

/-- `expression(p)`. -/
partial def parseExpr (p : Prec) : M Typed := do
  let (lhs, _) ← parseAtom p
  parseInfix lhs p

partial def parseInfix (lhs : Typed) (p : Prec) : M Typed := do
  match ← mpeek with
  | some tk =>
    match ← lookupNota tk with
    | some (.infix t q right) =>
      if !(p.le q) then return lhs  -- q < p
      let _ ← mnext
      let rhs ← parseExpr (if right then q else q.succ)
      let e ← applyTerm t [lhs, rhs]
      parseInfix e p
    | _ => return lhs
  | none => return lhs

/-- A leading expression, of level at least `p`. -/
partial def parseAtom (p : Prec) : M (Typed × Prec) := do
  if ← mchar '(' then
    let e ← parseExpr (.num 0)
    unless ← mchar ')' do throw "expected ')'"
    return (e, .max)
  let tk ← mnext
  if tk.front == ')' then throw "unexpected ')'"
  let ctx ← read
  match findIdx ctx (·.1 == tk) with
  | some v => return (⟨.var v, ctx[v]!.2.1⟩, .max)
  | none =>
  match ← lookupNota tk with
  | some (.prefix t q) =>
    unless q.le .max && p.le q do throw s!"precedence too low for '{tk}'"
    let n := (← getThe ElabState).terms[t]!.args.length
    let mut args := #[]
    for _ in [0:n-1] do args := args.push (← parseExpr .max)
    if n > 0 then args := args.push (← parseExpr q)
    return (← applyTerm t args.toList, q)
  | some (.general t q lits vars) =>
    unless p.le q do throw s!"precedence too low for '{tk}'"
    -- X(lits, q), with the first constant already consumed
    let rec go : List NotaLit → M (List (String × Typed))
      | [] => return []
      | .const c _ :: ls => do
        unless (← mnext) == c do throw s!"expected '{c}'"
        go ls
      | .var x :: ls => do
        let q' := match ls with
          | [] => q
          | .const _ r :: _ => r.succ
          | .var _ :: _ => .max
        let e ← parseExpr q'
        return (x, e) :: (← go ls)
    let got ← go (lits.drop 1)
    let args := vars.map fun x => (got.lookup x).get!
    return (← applyTerm t args, q)
  | some (.infix ..) => throw s!"unexpected infix operator '{tk}'"
  | none =>
  match ← (termId? tk : E _) with
  | some t =>
    let n := (← getThe ElabState).terms[t]!.args.length
    if n == 0 then return (← applyTerm t [], .max)
    unless p.le (.num 1024) do throw s!"precedence too low for application of '{tk}'"
    let mut args := #[]
    for _ in [0:n] do args := args.push (← parseExpr .max)
    return (← applyTerm t args.toList, .num 1024)
  | none => throw s!"unknown token '{tk}'"
end

def elabMath (ctx : VarCtx) (s : String) : E Typed := do
  let toks := mathTokens (← get) s
  let (e, rest) ← ((parseExpr (.num 0)).run ctx).run toks
  unless rest.isEmpty do throw s!"unexpected token '{rest.head!}'"
  return e

/-- Coerce a formula into its unique provable sort. -/
def elabFormula (ctx : VarCtx) (s : String) : E SExpr := do
  let x ← elabMath ctx s
  let st ← get
  let provs := (List.range st.sorts.size).filter fun i =>
    st.sorts[i]!.2.provable && (coePath st.coes x.sort i).isSome
  match provs with
  | [s] => coerce x s
  | [] => throw "formula does not have a provable sort"
  | _ => throw "formula has more than one provable sort"

/-- Free bound variables of an expression in definition mode (mm0-c's `FV`). -/
partial def freeVars (st : ElabState) (ctx : Ctx) : SExpr → List VarId
  | .var v => match ctx[v]? with
    | some (.bound _) => [v]
    | some (.reg _ vs) => vs
    | none => []
  | e =>
    let rec spine : SExpr → List SExpr → Option (TermId × List SExpr)
      | .term t, acc => some (t, acc)
      | .app1 f x, acc => spine f (x :: acc)
      | .var _, _ => none
    match spine e [] with
    | none => []
    | some (t, args) =>
      let info := st.terms[t]!
      let pairs := info.args.zip args
      let bvs := pairs.filterMap fun
        | (.bound _, a) => some (freeVars st ctx a)
        | _ => none
      let fromRegs := pairs.flatMap fun
        | (.reg _ deps, a) =>
          -- bound binder indices in the term's own context
          let boundIdx := (info.args.zipIdx.filter fun (b, _) => match b with
            | .bound _ => true | _ => false).map (·.2)
          let bound := deps.filterMap fun d => (findIdx boundIdx (· == d)).bind (bvs[·]?)
          (freeVars st ctx a).filter fun v => !bound.any (·.contains v)
        | _ => []
      let boundIdx := (info.args.zipIdx.filter fun (b, _) => match b with
        | .bound _ => true | _ => false).map (·.2)
      let fromRet := info.ret.2.flatMap fun d =>
        ((findIdx boundIdx (· == d)).bind (bvs[·]?)).getD []
      fromRegs ++ fromRet

/-- Check and convert the variable binders of a statement. Returns the
context, the variable names and the hypotheses (as strings). -/
def elabBinders (bis : List RBinder) (allowDummies : Bool) :
    E (Ctx × VarCtx × List String × List SortId) := do
  let mut ctx : Ctx := []
  let mut vctx : VarCtx := []
  let mut hyps := []
  let mut dummies : List (Option String × SortId) := []
  for b in bis do
    match b.ty with
    | .formula m => hyps := hyps ++ [m]
    | .sort s deps =>
      let sid ← sortId s
      let sd := (← get).sorts[sid]!.2
      if let some x := b.name then
        if vctx.any (·.1 == x) || dummies.any (·.1 == some x) then
          throw s!"duplicate variable '{x}'"
      match b.kind with
      | .dummy =>
        unless allowDummies do throw "dummy not allowed here"
        unless deps.isEmpty do throw "dummy with dependencies"
        if sd.strict || sd.free then throw "dummy variable in strict or free sort"
        dummies := dummies ++ [(b.name, sid)]
      | .bound =>
        unless deps.isEmpty do throw "bound variable with dependencies"
        if sd.strict then throw "bound variable in strict sort"
        ctx := ctx ++ [.bound sid]
        vctx := vctx ++ [(b.name.getD "_", sid, true)]
      | .reg =>
        let vs ← deps.mapM fun d => do
          match findIdx vctx (·.1 == d) with
          | some i => if vctx[i]!.2.2 then pure i else throw s!"'{d}' is not a bound variable"
          | none => throw s!"unknown variable '{d}'"
        ctx := ctx ++ [.reg sid vs]
        vctx := vctx ++ [(b.name.getD "_", sid, false)]
  -- dummies go after the arguments (`appendDummies`)
  for (x, s) in dummies do
    vctx := vctx ++ [(x.getD "_", s, true)]
  -- `_` names are not referable
  vctx := vctx.map fun (x, s, b) => (if x == "_" then "" else x, s, b)
  return (ctx, vctx, hyps, dummies.map (·.2))

def elabRet (vctx : VarCtx) (nargs : Nat) (ret : String × List String) : E DepType := do
  let s ← sortId ret.1
  let vs ← ret.2.mapM fun d => do
    match findIdx (vctx.take nargs) (·.1 == d) with
    | some i => if vctx[i]!.2.2 then pure i else throw s!"'{d}' is not a bound variable"
    | none => throw s!"unknown variable '{d}'"
  return (s, vs)

def newTermName (x : String) : E Unit := do
  if (← termId? x).isSome then throw s!"duplicate term '{x}'"

def addTerm (x : String) (ctx : Ctx) (ret : DepType) (d : Decl) : E Unit := do
  newTermName x
  if (← get).sorts[ret.1]!.2.pure then throw s!"term '{x}' has a pure sort"
  modify fun st => { st with
    terms := st.terms.push ⟨x, ctx, ret⟩, env := st.env.push d }

def checkToken (tk : String) : E Unit := do
  let st ← get
  if tk == "(" || tk == ")" then throw "'(' and ')' are reserved"
  if tk.isEmpty || tk.any (fun c => c == ' ' || c == '\n') then throw s!"bad token '{tk}'"
  unless mathTokens st tk == [tk] do throw s!"token '{tk}' contains a delimiter"

def addNota (tk : String) (n : Nota) : E Unit := do
  checkToken tk
  if ((← get).notas.lookup tk).isSome then throw s!"token '{tk}' already declared"
  modify fun st => { st with notas := (tk, n) :: st.notas }

def addInfixy (tk : String) (p : Prec) : E Unit := do
  let st ← get
  match st.infixy.lookup tk with
  | some q => unless q == p do throw s!"precedence mismatch for '{tk}'"
  | none =>
    modify fun st => { st with infixy := (tk, p) :: st.infixy }

/-- Whether `a` and `b` are already connected in the undirected coercion graph. -/
partial def connected (coes : List (SortId × SortId × TermId)) (a b : SortId)
    (visited : List SortId := []) : Bool :=
  a == b || coes.any fun (x, y, _) =>
    (x == a && !visited.contains y && connected coes y b (a :: visited)) ||
    (y == a && !visited.contains x && connected coes x b (a :: visited))

def elabStmt : Stmt → E Unit
  | .sort x sd => do
    if (← get).sorts.any (·.1 == x) then throw s!"duplicate sort '{x}'"
    modify fun st => { st with
      sorts := st.sorts.push (x, sd), env := st.env.push (.sort st.sorts.size sd) }
  | .term x bis ret => do
    let (ctx, vctx, _, _) ← elabBinders bis false
    let r ← elabRet vctx ctx.length ret
    addTerm x ctx r (.term (← get).terms.size ctx r)
  | .defn x bis ret body => do
    let (ctx, vctx, _, ds) ← elabBinders bis true
    if body.isNone && !ds.isEmpty then throw "dummies in a definition without a body"
    let r ← elabRet vctx ctx.length ret
    let id := (← get).terms.size
    match body with
    | none => addTerm x ctx r (.defn id ctx r none)
    | some b =>
      let e ← elabMath vctx b
      let e ← coerce e r.1
      let full := appendDummies ctx ds
      let fv := freeVars (← get) full e
      for v in fv do
        unless r.2.contains v do
          throw s!"definition '{x}': variable '{(vctx[v]?.map (·.1)).getD "?"}' is free in the body but not in the return type"
      addTerm x ctx r (.defn id ctx r (some (ds, e)))
  | .assert thm x bis concl => do
    let st ← get
    if st.thms.contains x then throw s!"duplicate theorem '{x}'"
    let (ctx, vctx, hyps, _) ← elabBinders bis false
    let hs ← hyps.mapM (elabFormula vctx)
    let c ← elabFormula vctx concl
    modify fun st => { st with
      thms := x :: st.thms
      env := st.env.push (if thm then .thm ctx hs c else .ax ctx hs c) }
  | .delimiter l r => do
    for w in l ++ r do
      unless w.length == 1 do throw s!"delimiter '{w}' is not a single character"
      if w.all isIdentChar then throw s!"delimiter '{w}' consists of identifier characters"
    modify fun st => { st with
      leftDelims := st.leftDelims ++ l.map (·.front)
      rightDelims := st.rightDelims ++ r.map (·.front) }
  | .simple k x tk p => do
    let some t ← termId? x | throw s!"unknown term '{x}'"
    let info := (← get).terms[t]!
    match k with
    | .prefix =>
      if info.args.isEmpty && p != .max then pure ()
      addNota tk (.prefix t p)
    | .infixl | .infixr =>
      unless info.args.length == 2 do throw s!"infix '{tk}' needs a binary term"
      if p == .max then throw "infix precedence must be less than max"
      -- as in mm0-c: a precedence level is left or right associative, not both
      let right := k == .infixr
      match (← get).assoc.lookup p with
      | some r => unless r == right do throw "precedence level is both left and right assoc"
      | none => modify fun st => { st with assoc := (p, right) :: st.assoc }
      addInfixy tk p
      addNota tk (.infix t p (k == .infixr))
  | .coercion x a b => do
    let some t ← termId? x | throw s!"unknown term '{x}'"
    let a ← sortId a
    let b ← sortId b
    let info := (← get).terms[t]!
    unless a != b do throw "coercion to the same sort"
    match info.args with
    | [.reg s _] => unless s == a && info.ret.1 == b do throw "coercion type mismatch"
    | _ => throw "coercion must be a unary term"
    let st ← get
    if connected st.coes a b then throw "coercion cycle or diamond"
    set { st with coes := (a, b, t) :: st.coes }
    -- each sort coerces to at most one provable sort
    let st ← get
    for s in List.range st.sorts.size do
      let n := (List.range st.sorts.size).filter fun i =>
        st.sorts[i]!.2.provable && (coePath st.coes s i).isSome
      if n.length > 1 then throw "coercion diamond to provable sort"
  | .notation x bis ret lits => do
    let some t ← termId? x | throw s!"unknown term '{x}'"
    let info := (← get).terms[t]!
    let (ctx, vctx, _, _) ← tryCatch (elabBinders bis false) fun e =>
      throw s!"notation binder: {e}"
    let r ← elabRet vctx ctx.length ret
    unless ctx == info.args && r == info.ret do throw s!"notation does not match the type of '{x}'"
    let vars := vctx.map (·.1)
    let used := lits.filterMap fun | .var x => some x | _ => none
    unless used.length == vars.length && vars.all (used.contains ·) do
      throw "each variable must appear exactly once in the notation"
    match lits with
    | .const c p :: _ =>
      if ((← get).infixy.lookup c).isSome then throw s!"'{c}' is already infixy"
      -- constants after a variable are infixy
      let mut prev := false
      for l in lits.drop 1 do
        match l with
        | .const d q =>
          if prev then
            if q == .max then throw "infixy constant with precedence max"
            addInfixy d q
          else checkToken d
          prev := false
        | .var _ => prev := true
      addNota c (.general t p lits vars)
    | _ => throw "notation must start with a constant"
  | .inout _ => pure ()
  | .import _ => throw "import needs a file system; use elabFileIO"

/-- Elaborate a self-contained source (no `import`). -/
def elabFile (src : String) : Except String (Array Decl × ElabState) := do
  let stmts ← parseFile src
  let (_, st) ← (stmts.forM elabStmt).run {}
  return (st.env, st)

def elabEnv (src : String) : Except String Env := (·.1.toList) <$> elabFile src

/-- Elaborate a file, following `import "path";` (relative to the importing
file, each file at most once), as `mm0-rs` does. -/
partial def elabFileIO (path : System.FilePath) :
    ExceptT String IO (Array Decl × ElabState) := do
  let rec go (path : System.FilePath) (st : ElabState × List String) :
      ExceptT String IO (ElabState × List String) := do
    let key := path.normalize.toString
    if st.2.contains key then return st
    let src ← IO.FS.readFile path
    let stmts ← match parseFile src with
      | .ok s => pure s
      | .error e => throw s!"{path}:{e}"
    let mut st := (st.1, key :: st.2)
    for s in stmts do
      match s with
      | .import p => st ← go ((path.parent.getD ".") / p) st
      | s => match (elabStmt s).run st.1 with
        | .ok (_, st1) => st := (st1, st.2)
        | .error e => throw s!"{path}: {e}"
    return st
  let (st, _) ← go path ({}, [])
  return (st.env, st)

end MM0.Parse
