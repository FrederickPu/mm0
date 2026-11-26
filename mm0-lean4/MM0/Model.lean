import MM0.Spec

/-!
# Models of MM0 and soundness

What it means for a model to satisfy an MM0 environment, and the soundness
theorem: a model that satisfies an environment's axioms and definitions
satisfies every theorem proved in it (Plan.md, M2, generic layer).

## The semantics

Values live in one type `U`, and each sort has a carrier (`Model.sorts`).
Variables are read nominally, as in Mario Carneiro's unfinished
`mm0-lean/mm0/model.lean` (ported in `MM0/Lean3Model.lean`): an expression
denotes a function from a valuation `ρ : Nat → U` of variable *names* to `U`.

* A bound variable `v` of the context has a name `η v`, and denotes
  `fun ρ => ρ (η v)`.
* A regular variable `v` denotes a given function `G v`.
* A term `t` receives, for each argument position `k`, the name of its
  argument if position `k` is bound (`M.bnd t k`), and the denotation of its
  argument otherwise.

Passing names instead of values is what makes unfolding a definition sound
when one variable is passed for two bound arguments, as in `d z z`.

A formula holds at a valuation when `M.prov` holds of its denotation there. A
*good* valuation puts each bound variable in its sort's carrier (`Good`). An
axiom or theorem is valid when, at every good valuation, the conclusion holds
if the hypotheses hold at every good valuation that differs only at the
theorem's bound variables (`Model.Valid`). This must hold for every naming `η`
that is injective on bound variables, and every `G` that
* respects dependencies: `G v` does not read the name of a bound variable
  that `v` does not depend on (`Supp`), and
* reads only finitely many names (`Bounded`), so a proof can always find
  fresh names for its dummy variables.

## Main results

* `MM0.Proof.sound`: soundness of one proof (`Proof E Γ Hs φ`).
* `MM0.Env.Proof'.sound`: every theorem of a proved, well-formed
  environment is valid in every model of it.
-/

namespace MM0

universe u

variable {U : Type u}

/-! ## Models -/

/-- Update a valuation at one name. -/
def upd (ρ : Nat → U) (n : Nat) (a : U) : Nat → U := fun m => if m = n then a else ρ m

/-- `f` does not read the name `n`. -/
def Indep (f : (Nat → U) → U) (n : Nat) : Prop := ∀ ρ a, f (upd ρ n a) = f ρ

/-- A model: a meaning for each term and definition, which argument positions
each one binds, and which values are true. -/
structure Model (U : Type u) where
  /-- `term t ν S`: the denotation of `t` applied to arguments whose names
  (at bound positions) are `ν` and whose denotations (at the other positions)
  are `S`. -/
  term : TermId → (Nat → Nat) → (Nat → (Nat → U) → U) → (Nat → U) → U
  /-- Which argument positions of a term are bound. -/
  bnd : TermId → Nat → Bool
  /-- The carrier of each sort: the values a bound variable of that sort
  ranges over (`env_ctx_model.sorts` in `model.lean`). -/
  sorts : SortId → U → Prop
  /-- Every sort has a value, so dummy variables can always be given one. -/
  sorts_nonempty : ∀ s, ∃ a, sorts s a
  /-- The true values of the provable sorts (`env_ctx_model.provs`). -/
  prov : U → Prop

variable [Inhabited U] (M : Model U)

/-- The denotation of an expression in context `Γ`, with names `η` for the
bound variables and denotations `G` for the regular ones. -/
def SExpr.eval (Γ : Ctx) (η : Nat → Nat) (G : Nat → (Nat → U) → U) :
    SExpr → (Nat → U) → U
  | .var v => match Γ[v]? with
    | some (.bound _) => fun ρ => ρ (η v)
    | _ => G v
  | .app t es =>
    M.term t
      (fun k => if M.bnd t k then
        (match es[k]? with | some (.var v) => η v | _ => 0) else 0)
      (fun k => if M.bnd t k then fun _ => default else
        ((es.map fun e => e.eval Γ η G)[k]?).getD fun _ => default)

/-- The bound positions of the model agree with the binders of the
environment's terms. -/
def Model.Agree (E : Env) : Prop :=
  ∀ t args r o, E.getTerm t args r o →
    ∀ k, M.bnd t k = true ↔ ∃ s, args[k]? = some (.bound s)

/-- A term reads no name other than those of its bound arguments and those
its other arguments read. -/
def Model.Frame : Prop :=
  ∀ t ν S n, (∀ k, M.bnd t k = true → ν k ≠ n) →
    (∀ k, M.bnd t k = false → Indep (S k) n) → Indep (M.term t ν S) n

/-- `η` names distinct bound variables of `Γ` differently. -/
def Inj (Γ : Ctx) (η : Nat → Nat) : Prop :=
  ∀ v w s s', Γ[v]? = some (.bound s) → Γ[w]? = some (.bound s') → η v = η w → v = w

/-- A regular variable does not read the name of a bound variable it does not
depend on. -/
def Supp (Γ : Ctx) (η : Nat → Nat) (G : Nat → (Nat → U) → U) : Prop :=
  ∀ u s vs w s', Γ[u]? = some (.reg s vs) → Γ[w]? = some (.bound s') → w ∉ vs →
    Indep (G u) (η w)

/-- Regular variables read only names below `N`. -/
def Bounded (Γ : Ctx) (G : Nat → (Nat → U) → U) (N : Nat) : Prop :=
  ∀ u s vs n, Γ[u]? = some (.reg s vs) → N ≤ n → Indep (G u) n

/-- `ρ` gives each bound variable of `Γ` a value in its sort's carrier
(`valuation.ok` in `model.lean`). -/
def Good (Γ : Ctx) (η : Nat → Nat) (ρ : Nat → U) : Prop :=
  ∀ v s, Γ[v]? = some (.bound s) → M.sorts s (ρ (η v))

/-- `ρ` is a good valuation that differs from `ρ₀` only at the names of the
bound variables of `Γ`. -/
def Near (Γ : Ctx) (η : Nat → Nat) (ρ₀ ρ : Nat → U) : Prop :=
  Good M Γ η ρ ∧ ∀ n, (∀ v s, Γ[v]? = some (.bound s) → η v ≠ n) → ρ n = ρ₀ n

/-- An axiom or theorem with binders `args`, hypotheses `hs` and conclusion
`ret` is valid in `M`: at every good valuation `ρ₀`, the conclusion holds if
the hypotheses hold at every good valuation that differs from `ρ₀` only at
the theorem's bound variables. (For `ax_gen: $ ph $ > $ A. x ph $`, the
hypothesis is needed for every value of `x`.) -/
def Model.Valid (args : Ctx) (hs : List SExpr) (ret : SExpr) : Prop :=
  ∀ η G N, Inj args η → Supp args η G → Bounded args G N →
    ∀ ρ₀, Good M args η ρ₀ →
    (∀ h ∈ hs, ∀ ρ, Near M args η ρ₀ ρ → M.prov (h.eval M args η G ρ)) →
    M.prov (ret.eval M args η G ρ₀)

/-- The model's meaning of the definition `t` is its body `val`, with dummies
`ds`: for any arguments, and any distinct names for the dummies that are
fresh for the arguments. -/
def Model.DefValid (t : TermId) (args : Ctx) (ds : List SortId) (val : SExpr) : Prop :=
  ∀ (ν : Nat → Nat) (S : Nat → (Nat → U) → U) (η' : Nat → Nat) (G' : Nat → (Nat → U) → U),
    (∀ k s, args[k]? = some (.bound s) → ν k = η' k) →
    (∀ k s vs, args[k]? = some (.reg s vs) → S k = G' k) →
    (∀ i j, i < ds.length → j < ds.length →
      η' (args.length + i) = η' (args.length + j) → i = j) →
    (∀ i k s, i < ds.length → args[k]? = some (.bound s) → η' (args.length + i) ≠ ν k) →
    (∀ i k s vs, i < ds.length → args[k]? = some (.reg s vs) →
      Indep (S k) (η' (args.length + i))) →
    M.term t ν S = val.eval M (appendDummies args ds) η' G'

/-- `M` is a model of the environment `E`: it agrees with the binders of its
terms, satisfies `Frame`, interprets each definition by its body, and
satisfies each axiom. -/
structure Model.Of (E : Env) : Prop where
  agree : M.Agree E
  frame : M.Frame
  defs : ∀ t args r ds val, Decl.defn t args r (some (ds, val)) ∈ E →
    M.DefValid t args ds val
  axioms : ∀ args hs ret, Decl.ax args hs ret ∈ E → M.Valid args hs ret

end MM0
