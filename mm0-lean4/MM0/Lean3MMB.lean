/-!
# Port of `mm0-lean/mm0/mm0b.lean`

A faithful port of the Lean 3 operational semantics of the `.mmb` proof
format by Mario Carneiro, definition by definition, so that the two can be
compared side by side. It describes the verifier as a relation on states: a
stack, a heap and a store of expressions. Each proof command (`ProofCmd`)
steps the state (`StepProof`), and unification commands (`UnifyCmd`) check a
theorem's or definition's statement against the stack (`Unify`). The format
itself is documented in `mm0-c/mmb.md`, and `mm0-c/verifier.c` implements it.

The Lean 3 file stops there. It proves nothing, `initial_state` has no
constructors, and nothing relates these states to `MM0.Proof`. Doing that
(an `.mmb` checker whose acceptance implies `Env.Proof'`, Plan.md's
`check_sound`) is future work.

Differences in the port itself:

* Lean 3's `list.nth` is `l[i]?`, and `list.zip_with` is `List.zipWith`.
* Lean 3's `σ.nth e = sexpr.app …` compares an `option` with a value through
  a coercion. Here it is written `σ[e]? = some (…)`.
* `unify` and `proof` take their arguments in the same order as in Lean 3.

Two quirks of the Lean 3 source are kept, not fixed, so the port stays
faithful:

* The `unfold` rule of `step_proof` is stated for the command
  `proof_cmd.cong`, not `proof_cmd.unfold`. It looks like a typo; as
  written, no rule handles `proof_cmd.unfold`.
* `initial_state` is declared with no constructors, so no state is initial.
-/

namespace MM0.Lean3.MMB

abbrev SortId := Nat
abbrev TermId := Nat
abbrev ThmId := Nat
abbrev HeapId := Nat
abbrev Ptr := Nat

structure SortData where
  pure : Bool := false
  strict : Bool := false
  provable : Bool := false
  free : Bool := false

inductive ProofCmd : Type
  | save : ProofCmd
  | term : TermId → ProofCmd
  | ref : HeapId → ProofCmd
  | dummy : SortId → ProofCmd
  | thm : ThmId → ProofCmd
  | hyp : ProofCmd
  | conv : ProofCmd
  | refl : ProofCmd
  | symm : ProofCmd
  | cong : ProofCmd
  | unfold : ProofCmd
  | convCut : ProofCmd
  | convRef : HeapId → ProofCmd

/-- A variable's type: a bound variable of a sort, or a regular one with its
dependencies as a bit list. -/
inductive Ty : Type
  | bound : SortId → Ty
  | reg : SortId → List Bool → Ty

/-- An expression in the store: a variable (with its heap index) or a term
applied to pointers into the store. -/
inductive SExpr : Type
  | var : Ty → HeapId → SExpr
  | app : Ty → TermId → List Ptr → SExpr

inductive StackEl
  | expr : Ptr → StackEl
  | proof : Ptr → StackEl
  | conv : Ptr → Ptr → StackEl
  | coConv : Ptr → Ptr → StackEl
  | hyp : Ptr → StackEl

def Ty.sort : Ty → SortId
  | .bound s => s
  | .reg s _ => s

inductive UnifyCmd
  | save : UnifyCmd
  | term : TermId → UnifyCmd
  | ref : HeapId → UnifyCmd
  | dummy : SortId → UnifyCmd
  | hyp : UnifyCmd

structure TermEl where
  bis : List Ty
  ret : Ty
  defn : Option (List UnifyCmd)

structure ThmEl where
  bis : List Ty
  unify : List UnifyCmd

structure Env where
  sorts : List SortData
  terms : List TermEl
  thms : List ThmEl

/-- Pop `n` expressions off the stack, returning them in pushed order. -/
inductive GetTermArgs : Nat → List StackEl → List Ptr → List StackEl → Prop
  | zero (S) : GetTermArgs 0 S [] S
  | succ (n S₁ p ps S₂) :
      GetTermArgs n S₁ ps S₂ →
      GetTermArgs (n + 1) (StackEl.expr p :: S₁) (ps ++ [p]) S₂

structure State where
  stack : List StackEl
  heap : List StackEl
  store : List SExpr

/-- `Unify σ (H, us) K S S'`: running the unification commands `us` with
unify heap `H` against the pending expressions `K` takes the main stack from
`S` to `S'`. -/
inductive Unify : List SExpr → List Ptr × List UnifyCmd → List Ptr →
    List StackEl → List StackEl → Prop
  | save (σ H us e K S S') :
      Unify σ (H ++ [e], us) (e :: K) S S' →
      Unify σ (H, UnifyCmd.save :: us) (e :: K) S S'
  | term (σ : List SExpr) (H us e t τ es K S S') :
      σ[e]? = some (SExpr.app τ t es) →
      Unify σ (H, us) (es ++ K) S S' →
      Unify σ (H, UnifyCmd.term t :: us) (e :: K) S S'
  | ref (σ) (H : List Ptr) (us e v K S S') :
      H[v]? = some e →
      Unify σ (H, us) K S S' →
      Unify σ (H, UnifyCmd.ref v :: us) (e :: K) S S'
  | dummy (σ : List SExpr) (H us e s v K S S') :
      σ[e]? = some (SExpr.var (Ty.bound s) v) →
      Unify σ (H ++ [e], us) K S S' →
      Unify σ (H, UnifyCmd.dummy s :: us) (e :: K) S S'
  | hyp (σ H us e K S S') :
      Unify σ (H, us) (e :: K) S S' →
      Unify σ (H, UnifyCmd.hyp :: us) K (StackEl.proof e :: S) S'
  | nil (σ H S) : Unify σ (H, []) [] S S

/-- One proof command. -/
inductive StepProof (env : Env) : ProofCmd → State → State → Prop
  | save (e S H σ) : StepProof env ProofCmd.save ⟨e :: S, H, σ⟩ ⟨e :: S, H ++ [e], σ⟩
  | term (t el S args S' H σ) :
      env.terms[t]? = some el →
      GetTermArgs el.bis.length S args S' →
      StepProof env (ProofCmd.term t) ⟨S, H, σ⟩
        ⟨StackEl.expr σ.length :: S', H, σ ++ [SExpr.app el.ret t args]⟩
  | ref (v S) (H : List StackEl) (el σ) :
      H[v]? = some el →
      StepProof env (ProofCmd.ref v) ⟨S, H, σ⟩ ⟨el :: S, H, σ⟩
  | dummy (s S H σ) :
      StepProof env (ProofCmd.dummy s) ⟨S, H, σ⟩
        ⟨StackEl.expr σ.length :: S,
         H ++ [StackEl.expr σ.length],
         σ ++ [SExpr.var (Ty.bound s) H.length]⟩
  | thm (t e el S args S₁ S₂ H σ) :
      env.thms[t]? = some el →
      GetTermArgs el.bis.length S args S₁ →
      Unify σ (args, el.unify) [e] S₁ S₂ →
      StepProof env (ProofCmd.thm t) ⟨StackEl.expr e :: S, H, σ⟩ ⟨S₂, H, σ⟩
  | hyp (e S H σ) :
      StepProof env ProofCmd.hyp
        ⟨StackEl.expr e :: S, H, σ⟩
        ⟨StackEl.hyp e :: S, H ++ [StackEl.proof e], σ⟩
  | conv (e1 e2 S H σ) :
      StepProof env ProofCmd.conv
        ⟨StackEl.proof e2 :: StackEl.expr e1 :: S, H, σ⟩
        ⟨StackEl.coConv e1 e2 :: StackEl.proof e1 :: S, H, σ⟩
  | refl (e S H σ) :
      StepProof env ProofCmd.refl
        ⟨StackEl.coConv e e :: S, H, σ⟩ ⟨S, H, σ⟩
  | symm (e1 e2 S H σ) :
      StepProof env ProofCmd.symm
        ⟨StackEl.coConv e1 e2 :: S, H, σ⟩
        ⟨StackEl.coConv e2 e1 :: S, H, σ⟩
  | cong (e1 e2 t τ1 τ2 es1 es2 S H) (σ : List SExpr) :
      σ[e1]? = some (SExpr.app τ1 t es1) →
      σ[e2]? = some (SExpr.app τ2 t es2) →
      StepProof env ProofCmd.cong
        ⟨StackEl.coConv e1 e2 :: S, H, σ⟩
        ⟨List.zipWith StackEl.coConv es1 es2 ++ S, H, σ⟩
  /-- As in the Lean 3 source, this rule is stated for `ProofCmd.cong`, not
  `ProofCmd.unfold` (see the module docs). -/
  | unfold (e e' τ t el us e2 args S H S') (σ : List SExpr) :
      σ[e]? = some (SExpr.app τ t args) →
      env.terms[t]? = some el → el.defn = some us →
      Unify σ (args, us) [e2] S (StackEl.coConv e e' :: S') →
      StepProof env ProofCmd.cong
        ⟨StackEl.expr e2 :: StackEl.expr e :: S, H, σ⟩
        ⟨StackEl.coConv e2 e' :: S', H, σ⟩
  | convCut (e1 e2 S H) (σ : List SExpr) :
      StepProof env ProofCmd.convCut
        ⟨StackEl.expr e2 :: StackEl.expr e1 :: S, H, σ⟩
        ⟨StackEl.coConv e1 e2 :: StackEl.conv e1 e2 :: S, H, σ⟩
  | convRef (v e1 e2 S) (H : List StackEl) (σ) :
      H[v]? = some (StackEl.conv e1 e2) →
      StepProof env (ProofCmd.convRef v)
        ⟨StackEl.coConv e1 e2 :: S, H, σ⟩ ⟨S, H, σ⟩

/-- As in the Lean 3 source, there are no constructors (see the module docs). -/
inductive InitialState (env : Env) : List Ty → State → Prop

/-- A run of proof commands from a state to an accepting final state: the
final stack holds the conclusion (a proof if `thm`, else an expression for a
definition) over the hypotheses, and it unifies with the statement `us`. -/
inductive Proof (env : Env) (args : List Ptr) (us : List UnifyCmd)
    (thm : Bool) : List ProofCmd → State → Prop
  | cons (p ps st st') :
      StepProof env p st st' →
      Proof env args us thm ps st' → Proof env args us thm (p :: ps) st
  | nil (S H σ e) :
      Unify σ (args, us) [e] (StackEl.proof <$> S) [] →
      Proof env args us thm [] ⟨(if thm then StackEl.proof e else StackEl.expr e) ::
        (StackEl.hyp <$> S), H, σ⟩

end MM0.Lean3.MMB
