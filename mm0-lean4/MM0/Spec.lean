/-!
# MM0 derivability

Sorts with modifiers, terms, definitions with unfolding, axioms, theorems,
bound vs. regular variables, dependency sets, and derivability (Plan.md, M1).

This follows `examples/mm0.mm0`, the MM0 spec written in MM0, definition by
definition. It started as a port of `mm0-lean/mm0/mm0.lean` (Lean 3), and
departs from both where they are too weak for the soundness theorem in
`MM0.Model` to hold. Each departure matches what `mm0-c` actually checks:

* **Expressions** are `app t [e₁, …, eₙ]`, as in `mm0.mm0`'s `SApp`, rather
  than the Lean 3 port's curried `app1` chains. Lean 4 handles the nested
  inductive. Conversion therefore has `mm0.mm0`'s rules: `refl`, `symm`,
  `trans`, `cong` on whole applications, and `unfold`.
* **`SafeSubst`** checks the theorem's own binders (`args`) to decide which
  argument positions are bound and what they depend on. Both `mm0.mm0`'s
  `VerifyProofThm` and the Lean 3 port read these from the *proof's* context
  (`nth u ctx`), although `u` indexes the theorem's arguments. As written,
  that lets a regular variable be instantiated with an expression containing
  a bound variable it must not depend on.
* **`unfold`** requires the dummy variables to be distinct and fresh: they
  occur in none of the arguments. `mm0.mm0` requires freshness but not
  distinctness, and the Lean 3 port requires neither. Without these
  conditions, unfolding can capture variables. `mm0-c` allocates a new
  variable for every dummy, so both conditions hold there.
* **`Free`** uses "or" where the Lean 3 port had "and": `v` is free in
  `t es` if it is free in an argument the term does not bind, *or* it is
  passed for a bound argument the result depends on (mm0.md, Definition
  checking).

Only Lean core is used. Lean 3's `finset` is a `List`, and the possibly
infinite hypothesis set is a predicate.
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

/-- Expressions: variables (by index into the context) and terms applied to
all their arguments (`mm0.mm0`'s `SVar` and `SApp`). -/
inductive SExpr
  | var : VarId → SExpr
  | app : TermId → List SExpr → SExpr
  deriving Inhabited

-- `deriving` does not handle the nested inductive; these are written out.
mutual
def SExpr.decEq : (a b : SExpr) → Decidable (a = b)
  | .var x, .var y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .app t es, .app u fs =>
    if h : t = u then
      match SExpr.decEqList es fs with
      | isTrue h2 => isTrue (by subst h; subst h2; rfl)
      | isFalse h2 => isFalse (by intro e; cases e; exact h2 rfl)
    else isFalse (by intro e; cases e; exact h rfl)
  | .var _, .app _ _ => isFalse (by intro e; cases e)
  | .app _ _, .var _ => isFalse (by intro e; cases e)
def SExpr.decEqList : (a b : List SExpr) → Decidable (a = b)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match SExpr.decEq a b, SExpr.decEqList as bs with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h1, _ => isFalse (by intro e; cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (by intro e; cases e; exact h2 rfl)
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
end

instance : DecidableEq SExpr := SExpr.decEq

partial def SExpr.toString : SExpr → String
  | .var v => s!"v{v}"
  | .app t es => s!"({t}" ++ String.join (es.map (" " ++ ·.toString)) ++ ")"

instance : Repr SExpr := ⟨fun e _ => .text e.toString⟩

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

mutual
/-- `e` is a well-formed expression of sort `s` (`mm0.mm0`'s `Expr`). -/
inductive SExpr.Ok (E : Env) (Γ : Ctx) : SExpr → SortId → Prop
  | var {v bi} : Γ[v]? = some bi → SExpr.Ok E Γ (.var v) bi.sort
  | app {t args ret o es} : E.getTerm t args ret o →
      SExpr.OkArgs E Γ es args → SExpr.Ok E Γ (.app t es) ret.1

/-- The arguments `es` fit the binders `bis`: a bound variable for a bound
binder, any expression of the right sort for a regular one (`ExprBi`). -/
inductive SExpr.OkArgs (E : Env) (Γ : Ctx) : List SExpr → List Binder → Prop
  | nil : SExpr.OkArgs E Γ [] []
  | bound {v s es bis} : Γ[v]? = some (.bound s) → SExpr.OkArgs E Γ es bis →
      SExpr.OkArgs E Γ (.var v :: es) (.bound s :: bis)
  | reg {e s vs es bis} : SExpr.Ok E Γ e s → SExpr.OkArgs E Γ es bis →
      SExpr.OkArgs E Γ (e :: es) (.reg s vs :: bis)
end

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
  | .app _ es, v => ∃ e, ∃ _ : e ∈ es, e.HasVar Γ v

/-- Free occurrence of `v`, looking through binders: `v` is free in `t es` if
it is free in an argument for a regular binder that does not depend on a
bound binder `v` is passed for, or if `v` is passed for a bound binder that
the return type depends on (mm0.md, Definition checking). -/
def SExpr.Free (E : Env) (Γ : Ctx) : SExpr → VarId → Prop
  | .var u, v => SExpr.HasVar Γ (.var u) v
  | .app t es, v => ∃ args r rs o, E.getTerm t args (r, rs) o ∧
      ((∃ e, ∃ _ : e ∈ es, ∃ (n : Nat) (s : SortId) (vs : List VarId), es[n]? = some e ∧ args[n]? = some (Binder.reg s vs) ∧
          e.Free E Γ v ∧ ¬ ∃ u ∈ vs, es[u]? = some (SExpr.var v)) ∨
        ∃ u ∈ rs, es[u]? = some (SExpr.var v))

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

/-- Simultaneous substitution of the variables `0, 1, …` by `σ`
(`mm0.mm0`'s `substExpr`). -/
def SExpr.subst (σ : List SExpr) : SExpr → SExpr
  | .var v => σ.getD v default
  | .app t es => .app t (es.map fun e => e.subst σ)

mutual
/-- Conversion (`mm0.mm0`'s `VerifyConv`), as an inductive predicate rather
than proof objects `CExpr`. -/
inductive Conv (E : Env) (Γ : Ctx) : SExpr → SExpr → SortId → Prop
  | refl {e s} : SExpr.Ok E Γ e s → Conv E Γ e e s
  | symm {e1 e2 s} : Conv E Γ e1 e2 s → Conv E Γ e2 e1 s
  | trans {e1 e2 e3 s} : Conv E Γ e1 e2 s → Conv E Γ e2 e3 s → Conv E Γ e1 e3 s
  | cong {t args ret o es1 es2} : E.getTerm t args ret o →
      ConvArgs E Γ es1 es2 args → Conv E Γ (.app t es1) (.app t es2) ret.1
  /-- Unfold a definition, instantiating its dummies with the bound variables
  `zs` of the context, which are distinct and occur in no argument. -/
  | unfold {t args ret ys val es zs} :
      E.getTerm t args ret (some (ys, val)) →
      SExpr.OkArgs E Γ es args →
      Forall₂ (fun y z => Γ[z]? = some (.bound y)) ys zs →
      zs.Nodup →
      (∀ e ∈ es, ∀ z ∈ zs, ¬ e.HasVar Γ z) →
      Conv E Γ (.app t es) (SExpr.subst (es ++ zs.map .var) val) ret.1

/-- Argument-wise conversion (`VerifyConvs`): bound arguments must be the same
variable. -/
inductive ConvArgs (E : Env) (Γ : Ctx) : List SExpr → List SExpr → List Binder → Prop
  | nil : ConvArgs E Γ [] [] []
  | bound {v s es1 es2 bis} : Γ[v]? = some (.bound s) → ConvArgs E Γ es1 es2 bis →
      ConvArgs E Γ (.var v :: es1) (.var v :: es2) (.bound s :: bis)
  | reg {e1 e2 s vs es1 es2 bis} : Conv E Γ e1 e2 s → ConvArgs E Γ es1 es2 bis →
      ConvArgs E Γ (e1 :: es1) (e2 :: es2) (.reg s vs :: bis)
end

/-- A substitution `σ` for a theorem with binders `args`, used in context `Γ`,
respects the theorem's distinctness conditions: if `v` may not depend on the
bound variable `u`, then the variable `u` is sent to does not occur in what
`v` is sent to. Bound positions and dependencies are read from `args`, and
occurrences from `Γ`. -/
def SafeSubst (Γ : Ctx) (args : Ctx) (σ : List SExpr) : Prop :=
  ∀ u v, (∃ s, args[u]? = some (.bound s)) →
    v < args.length → ¬ SExpr.HasVar args (.var v) u →
    ∀ y e2, σ[u]? = some (.var y) → σ[v]? = some e2 →
      ¬ e2.HasVar Γ y

/-- Provability from a (possibly infinite) set of hypotheses. -/
inductive Proof (E : Env) (Γ : Ctx) (Hs : SExpr → Prop) : SExpr → Prop
  | hyp {h} : Hs h → Proof E Γ Hs h
  | thm {args hs ret σ} :
      E.getThm args hs ret →
      SExpr.OkArgs E Γ σ args →
      SafeSubst Γ args σ →
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
