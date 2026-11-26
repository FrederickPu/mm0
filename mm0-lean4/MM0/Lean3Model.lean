import MM0.Spec

/-!
# Port of `mm0-lean/mm0/model.lean`

A faithful port of the Lean 3 model theory of MM0 by Mario Carneiro, kept
definition by definition so that the two can be compared side by side. The
Lean 3 file was never finished: everything after `env_ctx_model.insert_term`
is commented out there, and is reproduced below as documentation only.

`MM0.Model` (`MM0/Model.lean`) completes what this file started. It is the
version the soundness theorem (`MM0/Sound.lean`) uses. How its pieces
correspond to the ones here:

| `model.lean` | `MM0.Model` |
|---|---|
| `second A U = (A → U) → U` | the denotation type `(Nat → U) → U` (names `A = Nat`) |
| `termval = list second → second` | `Model.term`, which also gets the names of bound arguments |
| `second.supported s F` | `Indep F n` for each `n ∈ s` |
| `env_ctx_model.sorts` | `Model.sorts` (the carrier of each sort) |
| `env_ctx_model.provs` | `Model.prov` |
| `valuation.ok` (commented out) | `Good` |
| `term.model.ok`, `defn.model.ok`, `env.model'.ok` (commented out) | `Model.Frame`, `Model.DefValid`, `Model.Valid`, `Model.Of` |

Differences in the port itself:

* Lean 3's `set α` is `α → Prop`, `punit` is `PUnit`, and `bool` is `Bool`.
* `env_ctx_model.terms` is typed by `sort_id` in the Lean 3 file. Both are
  `ℕ` there, and the field is clearly meant to be indexed by term, so it is
  `TermId` here.
* `section parameters (A U : Type u)` becomes explicit arguments.
-/

namespace MM0.Lean3

universe u

/-- `sort_data.model`: a provable sort carries a set of true values. -/
def SortData.model (α : Type u) (sd : SortData) : Type u :=
  cond sd.provable (α → Prop) PUnit

variable (A U : Type u)

/-- `second`: the denotation of an expression, a function of a valuation of
the variable names `A`. -/
def Second : Type u := (A → U) → U

/-- `termval`: the meaning of a term, from its arguments' denotations to its
own. -/
def TermVal : Type u := List (Second A U) → Second A U

variable {A U}

/-- `second.supported`: `F` gives the same result on valuations that agree
outside `s`. (Despite the name, this says that `F` does not read the names
in `s`.) -/
def Second.Supported (s : A → Prop) (F : Second A U) : Prop :=
  ∀ v w : A → U, (∀ x, ¬ s x → v x = w x) → F v = F w

variable (A U)

/-- `env.model'`: the data of a model, declaration by declaration: two sets
for each sort (its values and its true values), a meaning for each term, and
a meaning for each definition as a function of its value. -/
def Env.model' : List Decl → Type u
  | [] => PUnit
  | .sort _ _ :: E' => (U → Prop) × (U → Prop) × Env.model' E'
  | .term _ _ _ :: E' => TermVal A U × Env.model' E'
  | .defn _ _ _ _ :: E' => TermVal A U → Env.model' E'
  | .ax _ _ _ :: E' => Env.model' E'
  | .thm _ _ _ :: E' => Env.model' E'

/-- `terms_model`. -/
def TermsModel : Type u := TermId → TermVal A U → Prop

/-- `env_ctx_model`: the carrier and the true values of each sort, and the
meanings of the terms. -/
structure EnvCtxModel where
  sorts : SortId → U → Prop
  provs : SortId → U → Prop
  ss : ∀ ⦃s x⦄, provs s x → sorts s x
  terms : TermId → TermVal A U → Prop

variable {A U}

/-- `env_ctx_model.insert_sort`: add the sort `id`, with values `S` and, if it
is provable, true values `P`. -/
def EnvCtxModel.insertSort (id : SortId) (S P : U → Prop) (H : ∀ x, P x → S x)
    (E : EnvCtxModel A U) : Bool → EnvCtxModel A U
  | false => {
      sorts := fun s x => E.sorts s x ∨ id = s ∧ S x
      provs := E.provs
      ss := fun _ _ h => Or.inl (E.ss h)
      terms := E.terms }
  | true => {
      sorts := fun s x => E.sorts s x ∨ id = s ∧ S x
      provs := fun s x => E.provs s x ∨ id = s ∧ P x
      ss := fun _ x h => h.imp (fun h => E.ss h) (And.imp_right (H x))
      terms := E.terms }

/-- `env_ctx_model.insert_term`: add the term `id` with meaning `F`. -/
def EnvCtxModel.insertTerm (id : TermId) (F : TermVal A U) (E : EnvCtxModel A U) :
    EnvCtxModel A U :=
  { E with terms := fun f F' => E.terms f F' ∨ id = f ∧ F = F' }

/-!
## The unfinished part

The rest of `model.lean` is commented out in the Lean 3 source, and some of
it does not typecheck there (for instance `sexpr.eval` is a fragment of
`defn.model.ok`). It is recorded here so that this port is complete. Its
intent:

* `valuation.ok Γ vs f`: the valuation `f` gives each bound variable in `vs`
  a value in its sort. Completed by `MM0.Good`.
* `dep_type.model.ok Γ (s, vs) F`: `F` lands in sort `s` under every good
  valuation of `vs`.
* `dep_type.model.supported S Γ (s, vs) F`: `F` reads only the names in
  `S ∪ vs`.
* `binders.ok'`, `binders.supported'`, `binders.ok`: walk a binder list,
  pushing bound variables into the context and checking each regular
  argument with `dep_type.model.ok`.
* `term.model.ok bis ret F`: the meaning `F` of a term maps well-sorted,
  supported arguments to a well-sorted, supported result. Completed by
  `MM0.Model.Frame` (support) and `MM0.Model.sorts` (sorting).
* `add_dummies`, `defn.model.ok bis ret F o`: a definition's meaning equals
  its body's, for every value of the dummies. Completed by
  `MM0.Model.DefValid`.
* `env.model'.ok`: `insert_sort`, `insert_term` and the definition cases
  thread an `env_ctx_model` through the environment, checking each term and
  definition. Completed by `MM0.Model.Of`, which also requires each axiom to
  be valid (`MM0.Model.Valid`). The Lean 3 file never got as far as axioms
  or theorems.
-/

end MM0.Lean3
