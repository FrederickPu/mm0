import MM0.Parse

/-!
Differential fuzzer for the Lean `.mm0` parser (`MM0/Parse.lean`)
against `mm0-rs` and `mm0-c`.

    mm0-fuzz [--iters N] [--seed S] [--out DIR] [--rs PATH] [--c PATH]
             SEED.mm0[=SEED.mmb] ...

Each iteration mutates one seed file and checks two oracles:

* **mm0-rs** (`mm0-rs compile MUTANT.mm0`): it must accept exactly when the
  Lean parser accepts.
* **mm0-c** (only for seeds given with an `.mmb`): `mm0-c SEED.mmb < MUTANT.mm0`
  must accept exactly when the Lean parser accepts the mutant *and*
  elaborates it to the same environment (declarations and names) as the seed.

Known, intended differences are not reported (see `knownDifference`).
Disagreements are written to `DIR` (default `fuzz-out/`) as
`NNNN-<oracle>.mm0` plus a `.txt` with both verdicts, so they can be turned
into regression tests.
-/

open MM0 MM0.Parse

/-! ## A small PRNG (xorshift64), so runs are reproducible from `--seed` -/

structure Rng where
  s : UInt64

def Rng.next (r : Rng) : Rng × Nat :=
  let x := r.s
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  let x := x ^^^ (x <<< 17)
  (⟨x⟩, x.toNat)

def Rng.below (r : Rng) (n : Nat) : Rng × Nat :=
  let (r, x) := r.next
  (r, if n == 0 then 0 else x % n)

/-! ## Mutations -/

/-- Characters and snippets to insert: grammar symbols, whitespace (legal and
illegal), comments, and characters outside the allowed set. -/
def insertPool : Array String :=
  #[" ", "\n", ";", "$", "(", ")", "{", "}", ":", ">", "_", ".", "=", "x", "0", "1",
    "-- c\n", "--", "\t", "\r", "é", "max", "sort", "prec", " $ $ ", "\"",
    "pure ", "strict ", "provable ", "free "]

/-- Insertions that should not change the meaning of the file, at a position
between two tokens: these exercise the "same environment" half of the mm0-c
oracle. -/
def neutralPool : Array String := #[" ", "\n", "  \n ", "-- comment\n", "\n--|doc\n"]

def identsOf (s : String) : Array String := Id.run do
  let mut out := #[]
  let mut cur := ""
  for c in s.toList do
    if isIdentChar c then cur := cur.push c
    else
      if cur.length > 0 && isIdentStart cur.front then out := out.push cur
      cur := ""
  return out

def mutate (r : Rng) (src : String) : Rng × String × String := Id.run do
  let cs := src.toList.toArray
  let n := cs.size
  let (r, kind) := r.below 7
  let (r, i) := r.below (n + 1)
  let pre := String.ofList (cs.toList.take i)
  let post := String.ofList (cs.toList.drop i)
  match kind with
  | 0 => -- delete a character
    (r, String.ofList (cs.toList.take i ++ cs.toList.drop (i + 1)), s!"delete char at {i}")
  | 1 => -- insert something
    let (r, j) := r.below insertPool.size
    (r, pre ++ insertPool[j]! ++ post, s!"insert {repr insertPool[j]!} at {i}")
  | 2 => -- neutral insertion next to whitespace or a statement end
    let mut k := i
    while k < n && !(cs[k]! == ' ' || cs[k]! == ';' || cs[k]! == '\n') do k := k + 1
    let pos := min (k + 1) n
    let (r, j) := r.below neutralPool.size
    (r, String.ofList (cs.toList.take pos) ++ neutralPool[j]! ++ String.ofList (cs.toList.drop pos),
      s!"neutral insert {repr neutralPool[j]!} at {pos}")
  | 3 => -- delete or duplicate a line
    let lines := src.splitOn "\n" |>.toArray
    let (r, l) := r.below lines.size
    let (r, dup) := r.below 2
    let ls := if dup == 0 then lines.eraseIdx! l else lines.insertIdx! l lines[l]!
    (r, "\n".intercalate ls.toList, if dup == 0 then s!"delete line {l}" else s!"duplicate line {l}")
  | 4 => -- swap two adjacent lines
    let lines := src.splitOn "\n" |>.toArray
    if lines.size < 2 then return (r, src, "noop")
    let (r, l) := r.below (lines.size - 1)
    (r, "\n".intercalate (lines.swapIfInBounds l (l+1)).toList, s!"swap lines {l},{l+1}")
  | 5 => -- replace one identifier occurrence with another identifier of the file
    let ids := identsOf src
    if ids.isEmpty then return (r, src, "noop")
    let (r, a) := r.below ids.size
    let (r, b) := r.below ids.size
    let parts := src.splitOn ids[a]!
    if parts.length < 2 then return (r, src, "noop")
    let (r, k) := r.below (parts.length - 1)
    let res := String.intercalate "" ((parts.take (k+1)).intersperse ids[a]!) ++ ids[b]! ++
      String.intercalate ids[a]! (parts.drop (k+1))
    (r, res, s!"replace occurrence {k} of '{ids[a]!}' with '{ids[b]!}'")
  | _ => -- bump a digit
    let mut k := i
    while k < n && !cs[k]!.isDigit do k := k + 1
    if k ≥ n then return (r, src, "noop")
    let (r, d) := r.below 10
    (r, String.ofList (cs.toList.take k ++ [Char.ofNat (48 + d)] ++ cs.toList.drop (k+1)),
      s!"set digit at {k} to {d}")

/-! ## Oracles -/

/-- Lean verdict: the error, or a canonical dump of the elaborated
declarations. Names and notations are left out: `mm0-c` checks neither. -/
def leanVerdict (src : String) : Except String String := do
  let (env, _) ← elabFile src
  return toString (repr env)

def runProc (cmd : String) (args : Array String) (stdin : Option String := none) :
    IO (UInt32 × String) := do
  let child ← IO.Process.spawn {
    cmd, args, stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdinH, child) ← child.takeStdin
  stdinH.putStr (stdin.getD "")
  stdinH.flush
  -- dropping the handle closes the child's stdin
  let out ← IO.asTask child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  let code ← child.wait
  let out ← IO.ofExcept out.get
  return (code, out ++ err)

/-- Known mm0-rs vs. Lean differences. Each is a deliberate choice of the
Lean parser (it follows `mm0.md` and `mm0-c`); none is a parser bug. Returns a
label for the statistics. -/
def knownRsDifference (leanErr : Option String) (rsOut : String) : Option String :=
  if leanErr.any (·.contains "modifiers must be in the order") then
    some "mm0-rs accepts sort modifiers out of order"
  else if rsOut.contains "unsupported input kind" then
    some "mm0-rs implements no input kinds"
  else if rsOut.contains "type inference is not allowed in MM0 files" then
    some "mm0-rs infers undeclared variables (with a warning)"
  else if rsOut.contains "statement expected after doc comment" || rsOut.contains "--|" then
    some "mm0-rs restricts where a --| doc comment may appear"
  else if leanErr.any (·.contains "duplicate sort") then
    some "mm0-rs accepts duplicate sort declarations"
  else if leanErr.any (·.contains "invalid number or identifier '0") then
    some "mm0-rs accepts numbers with a leading zero"
  else if leanErr.any (·.contains "notation binder:") then
    some "mm0-rs does not check the binders of a notation"
  else if leanErr.any (·.contains "both left and right assoc") then
    some "mm0-rs accepts mixed associativity at one precedence"
  else none

structure Args where
  iters : Nat := 200
  seed : Nat := 1
  out : System.FilePath := "fuzz-out"
  rs : String := "mm0-rs"
  c : String := "mm0-c"
  seeds : List (String × Option String) := []

partial def parseArgs : List String → Args → Args
  | "--iters" :: n :: rest, a => parseArgs rest { a with iters := n.toNat! }
  | "--seed" :: n :: rest, a => parseArgs rest { a with seed := n.toNat! }
  | "--out" :: d :: rest, a => parseArgs rest { a with out := d }
  | "--rs" :: p :: rest, a => parseArgs rest { a with rs := p }
  | "--c" :: p :: rest, a => parseArgs rest { a with c := p }
  | s :: rest, a =>
    let seed := match s.splitOn "=" with
      | [m, b] => (m, some b)
      | _ => (s, none)
    parseArgs rest { a with seeds := a.seeds ++ [seed] }
  | [], a => a

def bump (l : List (String × Nat)) (k : String) : List (String × Nat) :=
  if l.any (·.1 == k) then l.map fun (x, n) => if x == k then (x, n + 1) else (x, n)
  else l ++ [(k, 1)]

def main (argv : List String) : IO UInt32 := do
  let a := parseArgs argv {}
  if a.seeds.isEmpty then
    IO.eprintln "usage: mm0-fuzz [--iters N] [--seed S] [--out DIR] [--rs PATH] [--c PATH] SEED.mm0[=SEED.mmb] ..."
    return 2
  IO.FS.createDirAll a.out
  let tmp := a.out / "mutant.mm0"
  let seeds ← a.seeds.toArray.mapM fun (m, b) => do
    let src ← IO.FS.readFile m
    return (m, b, src, leanVerdict src)
  let mut rng : Rng := ⟨(a.seed * 2654435761 + 1).toUInt64⟩
  let mut found := 0
  let mut known : List (String × Nat) := []
  let mut accepted := 0
  let mut cRuns := 0
  for it in [0:a.iters] do
    let (r, si) := rng.below seeds.size
    let (m, mmb, src, seedV) := seeds[si]!
    let (r, mutant, how) := mutate r src
    rng := r
    let lv := leanVerdict mutant
    let leanErr := match lv with | .error e => some e | _ => none
    let leanOk := leanErr.isNone
    if leanOk then accepted := accepted + 1
    IO.FS.writeFile tmp mutant
    let report (oracle detail : String) : IO Unit := do
      IO.FS.writeFile (a.out / s!"{it}-{oracle}.mm0") mutant
      IO.FS.writeFile (a.out / s!"{it}-{oracle}.txt") <|
        s!"seed: {m}\nmutation: {how}\noracle: {oracle}\n{detail}\n"
      IO.println s!"[{it}] {oracle} disagrees on {m} ({how})"
    let leanStr := match leanErr with | none => "accept" | some e => "reject: " ++ e
    -- oracle 1: mm0-rs, same verdict
    let (rsCode, rsOut) ← runProc a.rs #["compile", tmp.toString]
    let rsOk := rsCode == 0
    if leanOk != rsOk then
      match knownRsDifference leanErr rsOut with
      | some k => known := bump known k
      | none =>
        found := found + 1
        report "rs" s!"lean: {leanStr}\nmm0-rs exit {rsCode}:\n{rsOut}"
    -- oracle 2: mm0-c against the seed's proof file: accepts iff the mutant
    -- elaborates to the seed's declarations
    if let some mmb := mmb then
      cRuns := cRuns + 1
      let (cCode, cOut) ← runProc a.c #[mmb] (stdin := some mutant)
      let cOk := cCode == 0
      let same := match lv, seedV with
        | .ok x, .ok y => x == y
        | _, _ => false
      if same != cOk then
        if cOk && !leanOk && !rsOk then
          -- Lean and mm0-rs both reject; mm0-c checks less of the .mm0 file
          known := bump known "mm0-c accepts what Lean and mm0-rs reject"
        else if cOk && !leanOk && (knownRsDifference leanErr rsOut).isSome then
          known := bump known "mm0-c accepts (known mm0-rs difference)"
        else
          found := found + 1
          report "c" s!"lean: {if same then "accept, same declarations" else if leanOk then "accept, different declarations" else leanStr}\nmm0-c exit {cCode}:\n{cOut}"
  IO.println s!"{a.iters} mutants ({accepted} accepted by Lean, {cRuns} also run through mm0-c)"
  for (k, n) in known do IO.println s!"  known difference, {n}x: {k}"
  IO.println s!"{found} unexplained disagreements"
  return if found == 0 then 0 else 1
