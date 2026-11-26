import MM0.Check

/-!
# Reading `.mmb` proof files

Turns an `.mmb` file (format: `mm0-c/mmb.md`) into the input of the verified
checker `MM0.Check.checkFile`: the proof file's declarations, a tag relating
each one to the `.mm0` file, and a proof term for each theorem.

This code is **not** verified, and does not need to be: `checkFile_sound`
only trusts the checker, so a misreading can make a correct file fail to
check but can never make the checker accept something that is not derivable.

The reader follows `mm0-c/verifier.c`'s stack machine, building terms instead
of checking them:

* the term and theorem tables give each declaration's binders;
* unify streams give statements and definition bodies (`decodeExpr`);
* proof streams are run on a stack of expressions, proofs and conversion
  obligations, producing `Pf` and `ConvPf` terms. A conversion obligation is
  a hole that later commands fill (`RConv.hole`).

Numbering: public terms and definitions get the ids the `.mm0` parser gives
them (their order in the file), and local definitions get ids from
`localBase` up, so that kept declarations are identical to the `.mm0` ones.
-/

namespace MM0.MMB

open MM0.Check

/-! ## Bytes -/

def u8At (b : ByteArray) (i : Nat) : Except String Nat :=
  if h : i < b.size then .ok b[i].toNat else .error s!"read past end of file at {i}"

def uAt (b : ByteArray) (i n : Nat) : Except String Nat := do
  let mut x := 0
  for k in [0:n] do
    x := x + (← u8At b (i + k)) * 256 ^ k
  return x

def u16At (b : ByteArray) (i : Nat) := uAt b i 2
def u32At (b : ByteArray) (i : Nat) := uAt b i 4
def u64At (b : ByteArray) (i : Nat) := uAt b i 8

/-- A `(cmd, data)` pair at `i`: the command, its data, and the position after it. -/
def cmdAt (b : ByteArray) (i : Nat) : Except String (Nat × Nat × Nat) := do
  let c ← u8At b i
  let cmd := c % 64
  match c / 64 with
  | 0 => return (cmd, 0, i + 1)
  | 1 => return (cmd, ← u8At b (i + 1), i + 2)
  | 2 => return (cmd, ← u16At b (i + 1), i + 3)
  | _ => return (cmd, ← u32At b (i + 1), i + 5)

/-! ## Tables -/

/-- An `arg` word: dependency bits, sort, and whether it is bound. -/
structure Arg where
  deps : Nat
  sort : Nat
  bound : Bool
  deriving Inhabited

def Arg.ofNat (x : Nat) : Arg :=
  { deps := x % 2 ^ 55, sort := (x / 2 ^ 56) % 128, bound := x / 2 ^ 63 % 2 == 1 }

/-- The binders of a declaration, from its `arg` words: a dependency on the
`j`th bound variable becomes the index of that bound binder. -/
def argsToCtx (args : Array Arg) : Ctx × (Nat → List VarId) :=
  let boundIdx := (List.range args.size).filter fun i => args[i]!.bound
  let depsOf (d : Nat) : List VarId :=
    (List.range boundIdx.length).filterMap fun j =>
      if d / 2 ^ j % 2 == 1 then boundIdx[j]? else none
  (args.toList.map fun a => if a.bound then .bound a.sort else .reg a.sort (depsOf a.deps),
   depsOf)

structure TermEntry where
  args : Array Arg
  ret : Arg
  isDef : Bool
  unify : Nat

structure ThmEntry where
  args : Array Arg
  unify : Nat

structure File where
  bytes : ByteArray
  sorts : Array SortData
  terms : Array TermEntry
  thms : Array ThmEntry
  proof : Nat

def readFile (b : ByteArray) : Except String File := do
  unless (← u32At b 0) == 0x42304D4D do throw "not an MMB file (bad magic)"
  unless (← u8At b 4) == 1 do throw "unsupported MMB version"
  let nSorts ← u8At b 5
  let nTerms ← u32At b 8
  let nThms ← u32At b 12
  let pTerms ← u32At b 16
  let pThms ← u32At b 20
  let pProof ← u32At b 24
  let mut sorts := #[]
  for i in [0:nSorts] do
    let x ← u8At b (40 + i)
    sorts := sorts.push { pure := x % 2 == 1, strict := x / 2 % 2 == 1,
                          provable := x / 4 % 2 == 1, free := x / 8 % 2 == 1 }
  let mut terms := #[]
  for i in [0:nTerms] do
    let e := pTerms + 8 * i
    let n ← u16At b e
    let rs ← u8At b (e + 2)
    let pData ← u32At b (e + 4)
    let mut args := #[]
    for k in [0:n] do args := args.push (Arg.ofNat (← u64At b (pData + 8 * k)))
    let ret := Arg.ofNat (← u64At b (pData + 8 * n))
    let isDef := rs / 128 == 1
    -- The unify stream follows the binders directly, as in `mm0-c` (`mmb.md`
    -- describes a `p32` pointer here, which is not what mm0-rs writes).
    let unify := if isDef then pData + 8 * (n + 1) else 0
    terms := terms.push { args, ret, isDef, unify }
  let mut thms := #[]
  for i in [0:nThms] do
    let e := pThms + 8 * i
    let n ← u16At b e
    let pData ← u32At b (e + 4)
    let mut args := #[]
    for k in [0:n] do args := args.push (Arg.ofNat (← u64At b (pData + 8 * k)))
    thms := thms.push { args, unify := pData + 8 * n }
  return { bytes := b, sorts, terms, thms, proof := pProof }

/-! ## Numbering -/

/-- Local definitions get ids from here up. -/
def localBase : Nat := 1000000000

/-- The id of each `.mmb` term: public ones in order, local ones above
`localBase`. Filled in while reading the statements. -/
abbrev IdMap := Array Nat

/-! ## Unify streams -/

/-- Decode one expression of a unify stream. `heap` holds the variables and
saved subterms (`none` while a saved term is still being read); `dummies`
collects the sorts of `UDummy` variables, numbered after the `nargs`
arguments. -/
partial def decodeExpr (f : File) (ids : IdMap) (nargs : Nat) (pos : Nat)
    (heap : Array (Option SExpr)) (dummies : Array SortId) :
    Except String (SExpr × Nat × Array (Option SExpr) × Array SortId) := do
  let (cmd, data, pos') ← cmdAt f.bytes pos
  match cmd with
  | 0x30 | 0x31 =>
    let some te := f.terms[data]? | throw s!"unify: bad term {data}"
    let some t := ids[data]? | throw s!"unify: forward reference to term {data}"
    let slot := heap.size
    let mut heap := if cmd == 0x31 then heap.push none else heap
    let mut dummies := dummies
    let mut pos := pos'
    let mut es := #[]
    for _ in [0:te.args.size] do
      let (e, p, h, d) ← decodeExpr f ids nargs pos heap dummies
      es := es.push e; pos := p; heap := h; dummies := d
    let e := SExpr.app t es.toList
    if cmd == 0x31 then heap := heap.set! slot (some e)
    return (e, pos, heap, dummies)
  | 0x32 =>
    match heap[data]? with
    | some (some e) => return (e, pos', heap, dummies)
    | _ => throw s!"unify: bad or cyclic reference {data}"
  | 0x33 =>
    let x := SExpr.var (nargs + dummies.size)
    return (x, pos', heap.push (some x), dummies.push data)
  | c => throw s!"unify: unexpected command {c}"

def initHeap (nargs : Nat) : Array (Option SExpr) :=
  (Array.range nargs).map fun i => some (.var i)

/-- A theorem's statement: hypotheses (in declaration order) and conclusion. -/
partial def decodeThm (f : File) (ids : IdMap) (te : ThmEntry) :
    Except String (List SExpr × SExpr) := do
  let n := te.args.size
  let (concl, pos, heap, _) ← decodeExpr f ids n te.unify (initHeap n) #[]
  let rec hyps (pos : Nat) (heap : Array (Option SExpr)) (acc : List SExpr) :
      Except String (List SExpr) := do
    let (cmd, _, pos') ← cmdAt f.bytes pos
    match cmd with
    | 0 => return acc
    | 0x36 =>
      let (h, pos'', heap', _) ← decodeExpr f ids n pos' heap #[]
      hyps pos'' heap' (h :: acc)
    | c => throw s!"unify: unexpected command {c} in theorem statement"
  -- the stream lists hypotheses last to first, so prepending puts them in order
  return (← hyps pos heap [], concl)

/-- A definition's body and the sorts of its dummies. -/
def decodeDef (f : File) (ids : IdMap) (te : TermEntry) :
    Except String (List SortId × SExpr) := do
  let n := te.args.size
  let (body, _, _, ds) ← decodeExpr f ids n te.unify (initHeap n) #[]
  return (ds.toList, body)

/-! ## Proof streams -/

/-- Conversion proofs with holes for obligations not yet discharged. -/
inductive RConv
  | hole (o : Nat)
  | refl (e : SExpr)
  | symm (c : RConv)
  | trans (c₁ c₂ : RConv)
  | cong (t : TermId) (cs : List RConv)
  | unfold (t : TermId) (es : List SExpr) (zs : List VarId)
  deriving Inhabited

inductive RPf
  | hyp (n : Nat)
  | thm (args : Ctx) (hs : List SExpr) (ret : SExpr) (σ : List SExpr) (ps : List RPf)
  | conv (c : RConv) (p : RPf)
  deriving Inhabited

/-- Stack and heap elements. -/
inductive El
  | expr (e : SExpr)
  | proof (e : SExpr) (p : RPf)
  | conv (e₁ e₂ : SExpr) (c : RConv)
  | coConv (e₁ e₂ : SExpr) (o : Nat)
  deriving Inhabited

structure PState where
  stack : List El := []
  heap : Array El := #[]
  hyps : Array SExpr := #[]
  dummies : Array SortId := #[]
  /-- Solutions of the conversion obligations. -/
  sols : Array (Option RConv) := #[]

/-- The statement of each theorem read so far (by `.mmb` theorem index). -/
abbrev ThmTable := Array (Ctx × List SExpr × SExpr)

/-- Definition data, by `.mmb` term index: binders, dummies and body. -/
abbrev DefTable := Array (Option (Ctx × List SortId × SExpr))

/-- Unification of an expression against a theorem's statement (`UThm`
mode): checks the shape, and pops the hypotheses' proofs off the main stack,
returning them last to first. -/
partial def unifyThm (f : File) (ids : IdMap) (pos : Nat) (heap : Array SExpr)
    (us : List SExpr) (main : List El) (pfs : List RPf) :
    Except String (List El × List RPf) := do
  let (cmd, data, pos') ← cmdAt f.bytes pos
  match cmd, us with
  | 0, [] => return (main, pfs)
  | 0x32, e :: us =>
    unless heap[data]? == some e do throw "Thm: unification failed (ref)"
    unifyThm f ids pos' heap us main pfs
  | 0x30, e :: us | 0x31, e :: us =>
    let heap := if cmd == 0x31 then heap.push e else heap
    match e with
    | .app t es =>
      unless ids[data]? == some t do throw "Thm: unification failed (term)"
      unifyThm f ids pos' heap (es ++ us) main pfs
    | _ => throw "Thm: unification failed (expected a term)"
  | 0x36, us =>
    match main with
    | .proof e p :: main => unifyThm f ids pos' heap (e :: us) main (p :: pfs)
    | _ => throw "Thm: expected a hypothesis proof"
  | c, _ => throw s!"Thm: unification failed at command {c}"

/-- Unification for `Unfold` (`UDef` mode): returns the variables matched to
the definition's dummies, in order. -/
partial def unifyDef (f : File) (ids : IdMap) (pos : Nat) (heap : Array SExpr)
    (us : List SExpr) (zs : List VarId) : Except String (List VarId) := do
  let (cmd, data, pos') ← cmdAt f.bytes pos
  match cmd, us with
  | 0, [] => return zs.reverse
  | 0x32, e :: us =>
    unless heap[data]? == some e do throw "Unfold: unification failed (ref)"
    unifyDef f ids pos' heap us zs
  | 0x30, e :: us | 0x31, e :: us =>
    let heap := if cmd == 0x31 then heap.push e else heap
    match e with
    | .app t es =>
      unless ids[data]? == some t do throw "Unfold: unification failed (term)"
      unifyDef f ids pos' heap (es ++ us) zs
    | _ => throw "Unfold: unification failed (expected a term)"
  | 0x33, e :: us =>
    match e with
    | .var z => unifyDef f ids pos' (heap.push e) us (z :: zs)
    | _ => throw "Unfold: expected a dummy variable"
  | c, _ => throw s!"Unfold: unification failed at command {c}"

/-- Match two bodies of the same definition that may number their dummies
(variables from `nargs` on) differently: `m[i] = j` sends dummy `i` of the
first to dummy `j` of the second. -/
partial def matchDummies (nargs : Nat) : SExpr → SExpr → Array (Option Nat) →
    Option (Array (Option Nat))
  | .var a, .var b, m =>
    if a < nargs || b < nargs then (if a == b then some m else none)
    else
      let i := a - nargs
      match m[i]? with
      | some (some j) => if j == b - nargs then some m else none
      | some none => some (m.set! i (some (b - nargs)))
      | none => none
  | .app t es, .app t' es', m =>
    if t == t' && es.length == es'.length then
      (es.zip es').foldlM (fun m (e, e') => matchDummies nargs e e' m) m
    else none
  | _, _, _ => none

/-- Put the dummies matched by `unifyDef` (in the `.mmb` numbering) in the
order of the definition used in the proof file. -/
def reorder (perm : Option (Array Nat)) (zs : List VarId) : List VarId :=
  match perm with
  | none => zs
  | some p =>
    let out := (List.range zs.length).map fun j =>
      (List.range zs.length).findSome? fun i => if p[i]? == some j then zs[i]? else none
    out.map (·.getD 0)

def newOblig (st : PState) : PState × Nat := ({ st with sols := st.sols.push none }, st.sols.size)

def solve (st : PState) (o : Nat) (c : RConv) : PState := { st with sols := st.sols.set! o (some c) }

/-- Run a theorem's proof stream. -/
partial def runProof (f : File) (ids : IdMap) (perms : Array (Option (Array Nat))) (thms : ThmTable) (nargs : Nat)
    (pos : Nat) (st : PState) : Except String PState := do
  let (cmd, data, pos') ← cmdAt f.bytes pos
  let continue_ (st : PState) := runProof f ids perms thms nargs pos' st
  match cmd with
  | 0 => return st
  | 0x10 | 0x11 => -- Term, TermSave
    let some te := f.terms[data]? | throw s!"Term: bad term {data}"
    let some t := ids[data]? | throw s!"Term: forward reference {data}"
    let n := te.args.size
    unless st.stack.length ≥ n do throw "Term: stack underflow"
    let args := (st.stack.take n).reverse
    let es ← args.mapM fun | .expr e => pure e | _ => throw "Term: expected an expression"
    let e := El.expr (.app t es)
    let st := { st with stack := e :: st.stack.drop n }
    continue_ (if cmd == 0x11 then { st with heap := st.heap.push e } else st)
  | 0x12 => -- Ref
    let some el := st.heap[data]? | throw s!"Ref: bad heap index {data}"
    match el, st.stack with
    | .conv e₁ e₂ c, .coConv e₁' e₂' o :: S =>
      unless e₁ == e₁' && e₂ == e₂' do throw "Ref: conversion mismatch"
      continue_ { solve st o c with stack := S }
    | .conv .., _ => throw "Ref: expected a conversion obligation"
    | el, S => continue_ { st with stack := el :: S }
  | 0x13 => -- Dummy
    let x := El.expr (.var (nargs + st.dummies.size))
    continue_ { st with stack := x :: st.stack, heap := st.heap.push x,
                        dummies := st.dummies.push data }
  | 0x14 | 0x15 => -- Thm, ThmSave
    let some (targs, ths, tret) := thms[data]? | throw s!"Thm: bad theorem {data}"
    let some te := f.thms[data]? | throw s!"Thm: bad theorem {data}"
    let n := targs.length
    match st.stack with
    | .expr e :: S =>
      unless S.length ≥ n do throw "Thm: stack underflow"
      let σ ← (S.take n).reverse.mapM fun | .expr e => pure e | _ => throw "Thm: expected an expression"
      let (S, pfs) ← unifyThm f ids te.unify σ.toArray [e] (S.drop n) []
      let pf := RPf.thm targs ths tret σ pfs
      let el := El.proof e pf
      let st := { st with stack := el :: S }
      continue_ (if cmd == 0x15 then { st with heap := st.heap.push el } else st)
    | _ => throw "Thm: expected the conclusion"
  | 0x16 => -- Hyp
    match st.stack with
    | .expr e :: S =>
      let p := El.proof e (.hyp st.hyps.size)
      continue_ { st with stack := S, hyps := st.hyps.push e, heap := st.heap.push p }
    | _ => throw "Hyp: expected an expression"
  | 0x17 => -- Conv: S, e1, |- e2 --> S, |- e1, e1 =?= e2
    match st.stack with
    | .proof e₂ p :: .expr e₁ :: S =>
      let (st, o) := newOblig st
      -- the obligation is e1 = e2; the proof of e1 converts p along e2 = e1
      continue_ { st with stack := .coConv e₁ e₂ o :: .proof e₁ (.conv (.symm (.hole o)) p) :: S }
    | _ => throw "Conv: bad stack"
  | 0x18 => -- Refl
    match st.stack with
    | .coConv e₁ e₂ o :: S =>
      unless e₁ == e₂ do throw "Refl: sides differ"
      continue_ { solve st o (.refl e₁) with stack := S }
    | _ => throw "Refl: expected an obligation"
  | 0x19 => -- Symm
    match st.stack with
    | .coConv e₁ e₂ o :: S =>
      let (st, o') := newOblig st
      continue_ { solve st o (.symm (.hole o')) with stack := .coConv e₂ e₁ o' :: S }
    | _ => throw "Symm: expected an obligation"
  | 0x1A => -- Cong
    match st.stack with
    | .coConv (.app t es₁) (.app t' es₂) o :: S =>
      unless t == t' && es₁.length == es₂.length do throw "Cong: heads differ"
      let mut st1 := st
      let mut holes := #[]
      for (a, b) in es₁.zip es₂ do
        let (st', o') := newOblig st1
        st1 := st'
        holes := holes.push (a, b, o')
      let obligs := holes.toList.map fun (a, b, o') => El.coConv a b o'
      let st2 := solve st1 o (.cong t (holes.toList.map fun (_, _, o') => RConv.hole o'))
      -- pushed last to first, so the first argument's obligation is on top
      continue_ { st2 with stack := obligs ++ S }
    | _ => throw "Cong: expected an obligation between applications"
  | 0x1B => -- Unfold: S, (t es) =?= e', e --> S, e =?= e'
    match st.stack with
    | .expr e :: .coConv (.app t es) e' o :: S =>
      let some k := ids.findIdx? (· == t) | throw "Unfold: unknown term"
      let some te := f.terms[k]? | throw "Unfold: unknown term"
      unless te.isDef do throw "Unfold: not a definition"
      let zs ← unifyDef f ids te.unify es.toArray [e] []
      let zs := reorder (perms[k]?.join) zs
      let (st, o') := newOblig st
      let st := solve st o (.trans (.unfold t es zs) (.hole o'))
      continue_ { st with stack := .coConv e e' o' :: S }
    | _ => throw "Unfold: bad stack"
  | 0x1C => -- ConvCut: S, e1 =?= e2 --> S, e1 = e2, e1 =?= e2
    match st.stack with
    | .coConv e₁ e₂ o :: S => continue_ { st with stack := .coConv e₁ e₂ o :: .conv e₁ e₂ (.hole o) :: S }
    | _ => throw "ConvCut: expected an obligation"
  | 0x1E => -- ConvSave
    match st.stack with
    | (.conv e₁ e₂ c) :: S => continue_ { st with stack := S, heap := st.heap.push (.conv e₁ e₂ c) }
    | _ => throw "ConvSave: expected a conversion"
  | 0x1F => -- Save
    match st.stack with
    | (.coConv ..) :: _ => throw "Save: cannot save an obligation"
    | el :: _ => continue_ { st with heap := st.heap.push el }
    | [] => throw "Save: empty stack"
  | 0x20 => throw "proof uses Sorry"
  | c => throw s!"unknown proof command {c}"

/-- Fill the holes of a conversion proof. -/
partial def RConv.resolve (sols : Array (Option RConv)) (fuel : Nat) : RConv → Except String ConvPf
  | .hole o => match fuel, sols[o]? with
    | f + 1, some (some c) => c.resolve sols f
    | 0, _ => throw "conversion: too deep"
    | _, _ => throw s!"conversion obligation {o} was never discharged"
  | .refl e => return .refl e
  | .symm c => return .symm (← c.resolve sols fuel)
  | .trans a b => return .trans (← a.resolve sols fuel) (← b.resolve sols fuel)
  | .cong t cs => return .cong t (← cs.mapM (·.resolve sols fuel))
  | .unfold t es zs => return .unfold t es zs

partial def RPf.resolve (sols : Array (Option RConv)) : RPf → Except String Pf
  | .hyp n => return .hyp n
  | .thm a hs r σ ps => return .thm a hs r σ (← ps.mapM (·.resolve sols))
  | .conv c p => return .conv (← c.resolve sols sols.size) (← p.resolve sols)

/-! ## Statements -/

structure Result where
  decls : Array Decl := #[]
  tags : Array Tag := #[]
  certs : Array (Option ThmCert) := #[]

/-- Read the proof file against the `.mm0` declarations `E`. -/
partial def read (b : ByteArray) (E : Env) : Except String (Env × List Tag × List (Option ThmCert)) := do
  let f ← readFile b
  let mut pos := f.proof
  let mut ids : IdMap := #[]
  let mut publicTerms := 0
  let mut nSorts := 0
  let mut thms : ThmTable := #[]
  let mut perms : Array (Option (Array Nat)) := #[]
  let mut res : Result := {}
  let mut rest := E  -- the `.mm0` declarations not yet matched
  for _ in [0:1000000] do
    let (cmd, data, pos') ← cmdAt f.bytes pos
    let next := pos + data
    if cmd == 0 then break
    match cmd with
    | 0x04 => -- Sort
      let some sd := f.sorts[nSorts]? | throw "bad sort"
      let d := Decl.sort nSorts sd
      nSorts := nSorts + 1
      res := { res with decls := res.decls.push d, tags := res.tags.push .keep,
                        certs := res.certs.push none }
      rest := rest.drop 1
    | 0x05 | 0x0D => -- Term, Def, LocalDef
      let k := ids.size
      let some te := f.terms[k]? | throw "bad term"
      let isLocal := cmd == 0x0D
      let t := if isLocal then localBase + k else publicTerms
      unless isLocal do publicTerms := publicTerms + 1
      ids := ids.push t
      let (args, depsOf) := argsToCtx te.args
      let ret : DepType := (te.ret.sort, depsOf te.ret.deps)
      let d ← if te.isDef then do
          let (ds, body) ← decodeDef f ids te
          pure (Decl.defn t args ret (some (ds, body)))
        else pure (Decl.term t args ret)
      -- match against the `.mm0` file
      let (d, tag) := match isLocal, rest with
        | true, _ => (d, Tag.skip)
        | false, .defn t' a' r' none :: _ =>
          if t' == t && a' == args && r' == ret && te.isDef then (d, .define) else (d, .keep)
        | false, d' :: _ =>
          -- a public def whose body is in the `.mm0` file: use the `.mm0` text
          match d, d' with
          | .defn .., .defn .. => (d', .keep)
          | _, _ => (d, .keep)
        | false, [] => (d, .keep)
      -- if the `.mm0` body replaced the `.mmb` one, record how dummies map
      let (ds, b) ← if te.isDef then decodeDef f ids te else pure ([], .var 0)
      let perm : Option (Array Nat) := match d with
        | .defn _ _ _ (some (_, b')) =>
          if isLocal || ds.isEmpty then none else
          (matchDummies args.length b b' (Array.replicate ds.length none)).map fun m =>
            m.map (·.getD 0)
        | _ => none
      perms := perms.push perm
      unless isLocal do rest := rest.drop 1
      res := { res with decls := res.decls.push d, tags := res.tags.push tag,
                        certs := res.certs.push none }
    | 0x02 | 0x06 | 0x0E => -- Axiom, Thm, LocalThm
      let k := thms.size
      let some te := f.thms[k]? | throw "bad theorem"
      let (args, _) := argsToCtx te.args
      let (hs, concl) ← decodeThm f ids te
      thms := thms.push (args, hs, concl)
      if cmd == 0x02 then
        res := { res with decls := res.decls.push (.ax args hs concl), tags := res.tags.push .keep,
                          certs := res.certs.push none }
        rest := rest.drop 1
      else
        let st ← runProof f ids perms thms args.length pos'
          { heap := (Array.range args.length).map fun i => El.expr (.var i) }
        let cert ← match st.stack with
          | [.proof _ p] => pure { ds := st.dummies.toList, pf := ← p.resolve st.sols : ThmCert }
          | _ => throw s!"theorem {k}: the proof does not end with one proof on the stack"
        let tag := if cmd == 0x0E then Tag.skip else .keep
        unless cmd == 0x0E do rest := rest.drop 1
        res := { res with decls := res.decls.push (.thm args hs concl), tags := res.tags.push tag,
                          certs := res.certs.push (some cert) }
    | c => throw s!"unknown statement {c}"
    pos := next
  return (res.decls.toList, res.tags.toList, res.certs.toList)

end MM0.MMB
