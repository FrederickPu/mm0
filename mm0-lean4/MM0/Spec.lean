/-!
MM0 in Lean 4 (Plan.md, M1): sorts with modifiers, terms, definitions with
unfolding, axioms, theorems, bound vs. regular variables, dependency sets, and
derivability.

A port of `mm0-lean/mm0/mm0.lean` (Lean 3). It follows that file
definition by definition, so the two can be compared side by side. That file in
turn follows `examples/mm0.mm0`. Only Lean core is used: Lean 3's `finset` is a
`List`, and the possibly infinite hypothesis set is a predicate.
-/
namespace MM0

/-- `List.forall₂` from Lean 3 core; not in Lean 4 core. -/
inductive Forall₂ (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {a b l₁ l₂} : R a b → Forall₂ R l₁ l₂ → Forall₂ R (a :: l₁) (b :: l₂)

/-- The four sort modifiers. -/
structure SortData where
  pure : Bool := false
  strict : Bool := false
  provable : Bool := false
  free : Bool := false
  deriving DecidableEq, Repr, Inhabited

abbrev SortId := Nat
abbrev TermId := Nat
abbrev VarId := Nat

inductive Binder
  /-- A bound variable `{x : s}`. -/
  | bound : SortId → Binder
  /-- A regular variable `(x : s vs)`, depending on the bound variables `vs`. -/
  | reg : SortId → List VarId → Binder
  deriving DecidableEq, Repr, Inhabited

def Binder.sort : Binder → SortId
  | .bound s => s
  | .reg s _ => s

/-- Expressions in curried form, as in the Lean 3 spec: a term applied to its
arguments is `app1 (… (app1 (term t) e₁) …) eₙ`. -/
inductive SExpr
  | var : VarId → SExpr
  | term : TermId → SExpr
  | app1 : SExpr → SExpr → SExpr
  deriving DecidableEq, Repr, Inhabited

def SExpr.app' : SExpr → List SExpr → SExpr
  | f, [] => f
  | f, x :: xs => SExpr.app' (.app1 f x) xs

def SExpr.app (t : TermId) : List SExpr → SExpr := SExpr.app' (.term t)

/-- A return type: a sort and the bound variables it may depend on. -/
abbrev DepType := SortId × List VarId

abbrev Ctx := List Binder

inductive Decl
  | sort : SortId → SortData → Decl
  | term : TermId → Ctx → DepType → Decl
  /-- A definition; `none` is an abstract `def`, `some (dummies, value)` has a body. -/
  | defn : TermId → Ctx → DepType → Option (List SortId × SExpr) → Decl
  | ax : Ctx → List SExpr → SExpr → Decl
  | thm : Ctx → List SExpr → SExpr → Decl
  deriving Repr, DecidableEq

abbrev Env := List Decl

def Env.getSD (e : Env) (s : SortId) (sd : SortData) : Prop := Decl.sort s sd ∈ e

inductive Env.getTerm (e : Env) (t : TermId) (a : Ctx) (r : DepType) :
    Option (List SortId × SExpr) → Prop
  | term : Decl.term t a r ∈ e → Env.getTerm e t a r none
  | defn {o} : Decl.defn t a r o ∈ e → Env.getTerm e t a r o

def Env.getThm (e : Env) (a : Ctx) (h : List SExpr) (r : SExpr) : Prop :=
  Decl.ax a h r ∈ e ∨ Decl.thm a h r ∈ e

def Env.IsSort (e : Env) (s : SortId) : Prop := ∃ sd, e.getSD s sd

def Ctx.IsBound (Γ : Ctx) (x : VarId) : Prop := ∃ s, Γ[x]? = some (.bound s)

def DepType.Ok (e : Env) (Γ : Ctx) : DepType → Prop
  | (s, vs) => e.IsSort s ∧ ∀ x ∈ vs, Γ.IsBound x

/-- Well-formed contexts, built by appending on the right as in `mm0.mm0`. -/
inductive Ctx.Ok (e : Env) : Ctx → Prop
  | nil : Ctx.Ok e []
  | bound {s sd Γ} : e.getSD s sd → sd.strict = false →
      Ctx.Ok e Γ → Ctx.Ok e (Γ ++ [.bound s])
  | reg {s vs Γ} : DepType.Ok e Γ (s, vs) →
      Ctx.Ok e Γ → Ctx.Ok e (Γ ++ [.reg s vs])

/-- `SExpr.Ok' E Γ e bis s`: `e` is a term applied to some of its arguments; it
still expects the arguments `bis` and then has sort `s`. -/
inductive SExpr.Ok' (E : Env) (Γ : Ctx) : SExpr → List Binder → SortId → Prop
  | var {v bi} : Γ[v]? = some bi → SExpr.Ok' E Γ (.var v) [] bi.sort
  | term {f bis ret o} : E.getTerm f bis ret o → SExpr.Ok' E Γ (.term f) bis ret.1
  | app_var {f s v bis ret} :
      Γ[v]? = some (.bound s) →
      SExpr.Ok' E Γ f (.bound s :: bis) ret →
      SExpr.Ok' E Γ (.app1 f (.var v)) bis ret
  | app_reg {f x s vs bis ret} :
      SExpr.Ok' E Γ f (.reg s vs :: bis) ret →
      SExpr.Ok' E Γ x [] s →
      SExpr.Ok' E Γ (.app1 f x) bis ret

def SExpr.Ok (E : Env) (Γ : Ctx) (e : SExpr) (s : SortId) : Prop := SExpr.Ok' E Γ e [] s

/-- `e` may be passed for an argument with binder `bi`: a bound variable for a
bound binder, any expression of the right sort for a regular one. -/
def SExpr.OkBi (E : Env) (Γ : Ctx) (e : SExpr) : Binder → Prop
  | .bound s => ∃ v, e = .var v ∧ Γ[v]? = some (.bound s)
  | .reg s _ => SExpr.Ok E Γ e s

def SExpr.OkProv (E : Env) (Γ : Ctx) (e : SExpr) : Prop :=
  ∃ s sd, SExpr.Ok E Γ e s ∧ E.getSD s sd ∧ sd.provable = true

def appendDummies (Γ : Ctx) (ds : List SortId) : Ctx := Γ ++ ds.map .bound

/-- `e.HasVar Γ v`: the bound variable `v` occurs in `e`, directly or through a
regular variable that depends on it. -/
def SExpr.HasVar (Γ : Ctx) : SExpr → VarId → Prop
  | .var u, v => ∃ bi, Γ[u]? = some bi ∧
      match bi with
      | .bound _ => u = v
      | .reg _ vs => v ∈ vs
  | .term _, _ => False
  | .app1 f x, v => f.HasVar Γ v ∨ x.HasVar Γ v

def MaybeFreeArgs (es : List SExpr) (a : Binder) (v : VarId) : Prop :=
  ∃ s vs, a = .reg s vs ∧ ¬ ∃ u ∈ vs, es[u]? = some (.var v)

/-- Free occurrence of `v`, looking through definitions: an occurrence is not
free when the term binds it. `es` and `ps` collect the arguments seen so far
and whether `v` is free in each. -/
def SExpr.Free' (E : Env) (Γ : Ctx) (v : VarId) : SExpr → List SExpr → List Prop → Prop
  | .var u, _, _ => SExpr.HasVar Γ (.var u) v
  | .term f, es, ps => ∃ args r rs o,
      E.getTerm f args (r, rs) o ∧
      (∃ (n : Nat) (free : Prop) (a : Binder), ps[n]? = some free ∧ args[n]? = some a ∧
        free ∧ MaybeFreeArgs es a v) ∧
      ∃ u ∈ rs, es[u]? = some (.var v)
  | .app1 f x, es, ps => SExpr.Free' E Γ v f (x :: es) (SExpr.Free' E Γ v x [] [] :: ps)

def SExpr.Free (E : Env) (Γ : Ctx) (e : SExpr) (v : VarId) : Prop := SExpr.Free' E Γ v e [] []

def TermOk (E : Env) (t : TermId) (args : Ctx) (ret : DepType) : Prop :=
  (¬ ∃ a r v, E.getTerm t a r v) ∧
  Ctx.Ok E args ∧ DepType.Ok E args ret ∧
  ∃ sd, E.getSD ret.1 sd ∧ sd.pure = false

def DefnOk (E : Env) (t : TermId) (args : Ctx) (ret : DepType)
    (ds : List SortId) (e : SExpr) : Prop :=
  TermOk E t args ret ∧
  let Γ := appendDummies args ds
  Ctx.Ok E Γ ∧ SExpr.Ok E Γ e ret.1 ∧
    ∀ v, SExpr.Free E Γ e v → v ∈ ret.2 ∨
      ∃ sd s, Γ[v]? = some (.bound s) ∧ E.getSD s sd ∧ sd.free = true

def AxiomOk (E : Env) (args : Ctx) (hs : List SExpr) (ret : SExpr) : Prop :=
  Ctx.Ok E args ∧ ∀ x ∈ ret :: hs, SExpr.OkProv E args x

def Decl.Ok (E : Env) : Decl → Prop
  | .sort _ _ => True
  | .term t args ret => TermOk E t args ret
  | .defn t args ret none => TermOk E t args ret
  | .defn t args ret (some (ds, e)) => DefnOk E t args ret ds e
  | .ax args hs ret => AxiomOk E args hs ret
  | .thm args hs ret => AxiomOk E args hs ret

inductive Env.Ok : Env → Prop
  | nil : Env.Ok []
  | cons {E d} : Env.Ok E → Decl.Ok E d → Env.Ok (E ++ [d])

/-- `Env.Extend E₁ E₂`: the `.mm0` file `E₁` is matched by the proof file `E₂`,
which may add definitions and theorems and give bodies to abstract `def`s. -/
inductive Env.Extend : Env → Env → Prop
  | nil : Env.Extend [] []
  | keep {E1 E2 d} : Env.Extend E1 E2 → Env.Extend (E1 ++ [d]) (E2 ++ [d])
  | defn_skip {E1 E2 id a r o} :
      Env.Extend E1 E2 → Env.Extend E1 (E2 ++ [.defn id a r o])
  | defn_def {E1 E2 id a r o} :
      Env.Extend E1 E2 →
      Env.Extend (E1 ++ [.defn id a r none]) (E2 ++ [.defn id a r o])
  | thm_skip {E1 E2 a h r} :
      Env.Extend E1 E2 → Env.Extend E1 (E2 ++ [.thm a h r])

/-- Simultaneous substitution of the variables `0, 1, …` by `σ`. -/
def SExpr.subst (σ : List SExpr) : SExpr → SExpr
  | .var v => σ.getD v default
  | .term f => .term f
  | .app1 f x => .app1 (f.subst σ) (x.subst σ)

/-- Conversion (definitional unfolding). As in the Lean 3 spec, this is an
inductive predicate rather than the proof objects `CExpr` of `mm0.mm0`. -/
inductive Conv' (E : Env) (Γ : Ctx) : SExpr → SExpr → List Binder → SortId → Prop
  | refl {e args s} : SExpr.Ok' E Γ e args s → Conv' E Γ e e args s
  | symm {e1 e2 s} : Conv' E Γ e1 e2 [] s → Conv' E Γ e2 e1 [] s
  | cong {f1 f2 bi bis x1 x2 s} :
      SExpr.OkBi E Γ x1 bi → SExpr.OkBi E Γ x2 bi →
      Conv' E Γ f1 f2 (bi :: bis) s →
      Conv' E Γ x1 x2 [] bi.sort →
      Conv' E Γ (.app1 f1 x1) (.app1 f2 x2) bis s
  | unfold {t args ret ys val es zs e2 s} :
      E.getTerm t args ret (some (ys, val)) →
      Forall₂ (SExpr.OkBi E Γ) es args →
      Forall₂ (fun y z => Γ[z]? = some (.bound y)) ys zs →
      Conv' E Γ (SExpr.app t es) e2 [] s →
      Conv' E Γ (SExpr.subst (es ++ zs.map .var) val) e2 [] s

def Conv (E : Env) (Γ : Ctx) (e1 e2 : SExpr) (s : SortId) : Prop := Conv' E Γ e1 e2 [] s

/-- A substitution respects the theorem's distinctness conditions: a bound
variable `u` that the regular variable `v` may not depend on is sent to a
variable that does not occur in what `v` is sent to. -/
def SafeSubst (Γ : Ctx) (σ : List SExpr) : Prop :=
  ∀ u v, (∃ s, Γ[u]? = some (.bound s)) →
    v < Γ.length → ¬ SExpr.HasVar Γ (.var v) u →
    ∀ y e2, σ[u]? = some (.var y) → σ[v]? = some e2 →
      ¬ e2.HasVar Γ y

/-- Provability from a (possibly infinite) set of hypotheses. -/
inductive Proof (E : Env) (Γ : Ctx) (Hs : SExpr → Prop) : SExpr → Prop
  | hyp {h} : Hs h → Proof E Γ Hs h
  | thm {args hs ret σ} :
      E.getThm args hs ret →
      Forall₂ (SExpr.OkBi E Γ) σ args →
      SafeSubst Γ σ →
      (∀ h ∈ hs, Proof E Γ Hs (SExpr.subst σ h)) →
      Proof E Γ Hs (SExpr.subst σ ret)
  | conv {e1 e2 s} : Conv E Γ e1 e2 s → Proof E Γ Hs e1 → Proof E Γ Hs e2

/-- Every theorem of the environment has a proof from its hypotheses. -/
inductive Env.Proof' : Env → Prop
  | nil : Env.Proof' []
  | sort {E s sd} : Env.Proof' E → Env.Proof' (E ++ [.sort s sd])
  | term {E id a r} : Env.Proof' E → Env.Proof' (E ++ [.term id a r])
  | defn {E id a r o} : Env.Proof' E → Env.Proof' (E ++ [.defn id a r (some o)])
  | ax {E a h r} : Env.Proof' E → Env.Proof' (E ++ [.ax a h r])
  | thm {E a hs r ds} :
      Ctx.Ok E (appendDummies a ds) →
      Proof E (appendDummies a ds) (· ∈ hs) r →
      Env.Proof' E → Env.Proof' (E ++ [.thm a hs r])

/-- The `.mm0` file `E` is proved: some proof file extends it and proves every
theorem in it. -/
def Env.Proof (E : Env) : Prop := ∃ E', Env.Extend E E' ∧ E'.Proof'

end MM0
