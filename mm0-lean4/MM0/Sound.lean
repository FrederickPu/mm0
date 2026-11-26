import MM0.Model

/-!
# Soundness of MM0

The soundness theorems for the semantics in `MM0.Model`:

* `MM0.Proof.sound`: if `M` is a model of `E` in which every theorem of `E`
  is valid, then whatever `Proof E Γ Hs` derives holds whenever the
  hypotheses `Hs` hold.
* `MM0.Env.Proof'.sound`: in a well-formed environment whose theorems all
  have proofs, every theorem is valid in every model of the environment.

The steps:

* `eval_subst`: substitution commutes with evaluation;
* `eval_indep_var` and `eval_indep_fresh`: an expression does not read the
  name of a bound variable that does not occur in it, nor a name no
  variable of the context has (the frame lemmas);
* `Conv.sound`: convertible expressions have equal denotations;
* instantiating a valid theorem, which uses `SafeSubst` to show that the
  instantiated variables still satisfy `Inj`, `Supp` and `Bounded`.
-/

set_option linter.unusedSectionVars false

namespace MM0

universe u

variable {U : Type u} [Inhabited U] (M : Model U)

/-! ## Lists and contexts -/

theorem Forall₂.length_eq {R : α → β → Prop} : ∀ {l₁ l₂}, Forall₂ R l₁ l₂ → l₁.length = l₂.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [h.length_eq]

theorem Forall₂.get {R : α → β → Prop} : ∀ {l₁ l₂}, Forall₂ R l₁ l₂ →
    ∀ (i : Nat) (a : α) (b : β), l₁[i]? = some a → l₂[i]? = some b → R a b
  | _, _, .nil, _, _, _, h, _ => by simp at h
  | _, _, .cons hab _, 0, _, _, h1, h2 => by simp at h1 h2; subst h1; subst h2; exact hab
  | _, _, .cons _ h, i+1, _, _, h1, h2 => h.get i _ _ (by simpa using h1) (by simpa using h2)

theorem Forall₂.get_left {R : α → β → Prop} : ∀ {l₁ l₂}, Forall₂ R l₁ l₂ →
    ∀ (i : Nat) (a : α), l₁[i]? = some a → ∃ b, l₂[i]? = some b ∧ R a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hab _, 0, _, h1 => by simp at h1; subst h1; exact ⟨_, rfl, hab⟩
  | _, _, .cons _ h, i+1, _, h1 => by simpa using h.get_left i _ (by simpa using h1)

theorem appendDummies_length (a : Ctx) (ds : List SortId) :
    (appendDummies a ds).length = a.length + ds.length := by simp [appendDummies]

theorem appendDummies_lt (a : Ctx) (ds : List SortId) (v : Nat) (h : v < a.length) :
    (appendDummies a ds)[v]? = a[v]? := by
  simp [appendDummies, List.getElem?_append_left h]

theorem appendDummies_dummy (a : Ctx) (ds : List SortId) (i : Nat) :
    (appendDummies a ds)[a.length + i]? = (ds[i]?).map .bound := by
  simp [appendDummies, List.getElem?_append_right]

theorem appendDummies_cases (a : Ctx) (ds : List SortId) (v : Nat) (bi : Binder)
    (h : (appendDummies a ds)[v]? = some bi) :
    (v < a.length ∧ a[v]? = some bi) ∨
      (∃ i s, v = a.length + i ∧ ds[i]? = some s ∧ bi = .bound s) := by
  by_cases hv : v < a.length
  · left; rw [appendDummies_lt a ds v hv] at h; exact ⟨hv, h⟩
  · right
    obtain ⟨i, rfl⟩ : ∃ i, v = a.length + i := ⟨v - a.length, by omega⟩
    rw [appendDummies_dummy] at h
    cases hd : ds[i]? <;> simp [hd] at h
    exact ⟨i, _, rfl, hd, h.symm⟩

/-! ## Variable occurrence -/

theorem hasVar_bound {Γ : Ctx} {u v : VarId} {s} (h : Γ[u]? = some (Binder.bound s)) :
    SExpr.HasVar Γ (.var u) v ↔ u = v := by
  rw [SExpr.HasVar]; simp [h]

theorem hasVar_reg {Γ : Ctx} {u v : VarId} {s vs} (h : Γ[u]? = some (Binder.reg s vs)) :
    SExpr.HasVar Γ (.var u) v ↔ v ∈ vs := by
  rw [SExpr.HasVar]; simp [h]

theorem hasVar_app {Γ : Ctx} {t : TermId} {es : List SExpr} {v : VarId} :
    SExpr.HasVar Γ (.app t es) v ↔ ∃ e ∈ es, e.HasVar Γ v := by
  rw [SExpr.HasVar]; simp

/-! ## Well-formed arguments -/

/-- What `OkArgs` says about each position. -/
theorem SExpr.OkArgs.facts {E : Env} {Γ : Ctx} : ∀ {es args}, SExpr.OkArgs E Γ es args →
    es.length = args.length ∧
    (∀ (k : Nat) s, args[k]? = some (Binder.bound s) →
      ∃ v : VarId, es[k]? = some (SExpr.var v) ∧ Γ[v]? = some (Binder.bound s)) ∧
    (∀ (k : Nat) s vs, args[k]? = some (Binder.reg s vs) → ∃ e, es[k]? = some e ∧ SExpr.Ok E Γ e s)
  | _, _, .nil => by simp
  | _, _, .bound hv h => by
    obtain ⟨h1, h2, h3⟩ := h.facts
    refine ⟨by simp [h1], ?_, ?_⟩
    · intro k s hk; cases k with
      | zero => simp at hk; subst hk; exact ⟨_, rfl, hv⟩
      | succ k => simpa using h2 k s (by simpa using hk)
    · intro k s vs hk; cases k with
      | zero => simp at hk
      | succ k => simpa using h3 k s vs (by simpa using hk)
  | _, _, .reg he h => by
    obtain ⟨h1, h2, h3⟩ := h.facts
    refine ⟨by simp [h1], ?_, ?_⟩
    · intro k s hk; cases k with
      | zero => simp at hk
      | succ k => simpa using h2 k s (by simpa using hk)
    · intro k s vs hk; cases k with
      | zero => simp at hk; obtain ⟨rfl, -⟩ := hk; exact ⟨_, rfl, he⟩
      | succ k => simpa using h3 k s vs (by simpa using hk)

/-- An induction principle for well-formed expressions, with induction
hypotheses for the arguments at regular positions. -/
theorem SExpr.Ok.rec' {E : Env} {Γ : Ctx} (P : SExpr → Prop)
    (hv : ∀ (v : Nat) bi, Γ[v]? = some bi → P (.var v))
    (ha : ∀ t args ret o es, E.getTerm t args ret o → SExpr.OkArgs E Γ es args →
      (∀ (k : Nat) s vs e, args[k]? = some (Binder.reg s vs) → es[k]? = some e → P e) → P (.app t es)) :
    ∀ {e s}, SExpr.Ok E Γ e s → P e :=
  fun h => go h
where
  go : ∀ {e s}, SExpr.Ok E Γ e s → P e
    | _, _, .var h => hv _ _ h
    | _, _, .app ht hargs => ha _ _ _ _ _ ht hargs (goArgs hargs)
  goArgs : ∀ {es args}, SExpr.OkArgs E Γ es args →
      ∀ (k : Nat) s vs e, args[k]? = some (Binder.reg s vs) → es[k]? = some e → P e
    | _, _, .nil, _, _, _, _, h, _ => by simp at h
    | _, _, .bound _ h, 0, _, _, _, hk, _ => by simp at hk
    | _, _, .bound _ h, k+1, _, _, _, hk, he => goArgs h k _ _ _ (by simpa using hk) (by simpa using he)
    | _, _, .reg he' _, 0, _, _, _, _, he => by simp at he; subst he; exact go he'
    | _, _, .reg _ h, k+1, _, _, _, hk, he => goArgs h k _ _ _ (by simpa using hk) (by simpa using he)

/-! ## Evaluation -/

theorem eval_var (Γ : Ctx) (η G) (v : VarId) :
    (SExpr.var v).eval M Γ η G = match Γ[v]? with
      | some (Binder.bound _) => fun ρ => ρ (η v)
      | _ => G v := by
  rw [SExpr.eval.eq_def]; rfl

theorem eval_app (Γ : Ctx) (η G) (t : TermId) (es : List SExpr) :
    (SExpr.app t es).eval M Γ η G =
    M.term t
      (fun k => if M.bnd t k then
        (match es[k]? with | some (SExpr.var v) => η v | _ => 0) else 0)
      (fun k => if M.bnd t k then fun _ => default else
        ((es.map fun e => e.eval M Γ η G)[k]?).getD fun _ => default) := by
  rw [SExpr.eval.eq_def]; rfl

theorem eval_bound {Γ : Ctx} {η G} {v : VarId} {s} (h : Γ[v]? = some (Binder.bound s)) :
    (SExpr.var v).eval M Γ η G = fun ρ => ρ (η v) := by
  rw [eval_var, h]

theorem eval_reg {Γ : Ctx} {η G} {v : VarId} {s vs} (h : Γ[v]? = some (Binder.reg s vs)) :
    (SExpr.var v).eval M Γ η G = G v := by
  rw [eval_var, h]

/-- The names and denotations that a substitution `σ` gives the variables it
replaces. -/
def substNames (η : Nat → Nat) (σ : List SExpr) (v : Nat) : Nat :=
  match σ.getD v default with
  | .var y => η y
  | _ => 0

def substDen (Γ : Ctx) (η : Nat → Nat) (G : Nat → (Nat → U) → U) (σ : List SExpr)
    (v : Nat) : (Nat → U) → U :=
  (σ.getD v default).eval M Γ η G

/-- Substitution commutes with evaluation, provided `σ` sends the bound
variables of `Δ` to bound variables of `Γ`. -/
theorem eval_subst (Γ Δ : Ctx) (σ : List SExpr) (η : Nat → Nat) (G : Nat → (Nat → U) → U)
    (hσ : ∀ (v : Nat) s, Δ[v]? = some (Binder.bound s) →
      ∃ (y : VarId) (s' : SortId), σ[v]? = some (SExpr.var y) ∧ Γ[y]? = some (Binder.bound s')) :
    ∀ e : SExpr, (e.subst σ).eval M Γ η G =
      e.eval M Δ (substNames η σ) (substDen M Γ η G σ)
  | .var v => by
    rw [SExpr.subst, eval_var M Δ]
    split
    · next s h =>
      obtain ⟨y, s', h1, h2⟩ := hσ v s h
      have : σ.getD v default = .var y := by simp [List.getD_eq_getElem?_getD, h1]
      rw [this, eval_bound M h2]
      funext ρ; simp [substNames, List.getD_eq_getElem?_getD, h1]
    · rfl
  | .app t es => by
    rw [SExpr.subst, eval_app, eval_app]
    congr 1
    · funext k
      split
      · simp only [List.getElem?_map]
        cases es[k]? with
        | none => rfl
        | some e =>
          cases e with
          | var v =>
            simp only [Option.map_some, SExpr.subst, substNames]
            cases σ.getD v default <;> rfl
          | app => simp [SExpr.subst]
      · rfl
    · funext k
      split
      · rfl
      · simp only [List.map_map, List.getElem?_map]
        cases h : es[k]? with
        | none => rfl
        | some e =>
          simp only [Option.map_some, Option.getD_some, Function.comp]
          exact eval_subst Γ Δ σ η G hσ e
termination_by e => sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem (List.mem_of_getElem? h)
  simp_wf; omega

/-! ## Frame lemmas -/

theorem indep_const (c : (Nat → U) → U) (h : ∀ ρ ρ', c ρ = c ρ') (n : Nat) : Indep c n :=
  fun ρ a => h _ _

theorem indep_name (m n : Nat) (h : m ≠ n) : Indep (fun ρ : Nat → U => ρ m) n := by
  intro ρ a; simp [upd, h]

section
variable {E : Env} {Γ : Ctx} {η : Nat → Nat} {G : Nat → (Nat → U) → U}

/-- At a position the model does not bind, a well-formed application has an
argument for a regular binder, or none. -/
theorem reg_pos (hA : M.Agree E) {t args ret o es} (ht : E.getTerm t args ret o)
    (hargs : SExpr.OkArgs E Γ es args) (k : Nat) (hk : M.bnd t k = false) (e : SExpr)
    (he : es[k]? = some e) : ∃ s vs, args[k]? = some (Binder.reg s vs) := by
  obtain ⟨hlen, -, -⟩ := hargs.facts
  have hk' : k < args.length := by
    have := (List.getElem?_eq_some_iff.1 he).1; omega
  match h : args[k]? with
  | none => simp [List.getElem?_eq_none_iff] at h; omega
  | some (Binder.reg s vs) => exact ⟨s, vs, rfl⟩
  | some (Binder.bound s) =>
    have := (hA t args ret o ht k).2 ⟨s, h⟩
    simp [hk] at this

/-- The argument denotations at positions the model does not bind. -/
theorem den_at (t : TermId) (es : List SExpr) (k : Nat) (hk : M.bnd t k = false) :
    (if M.bnd t k then (fun _ => default : (Nat → U) → U) else
      ((es.map fun e => e.eval M Γ η G)[k]?).getD fun _ => default) =
    match es[k]? with
    | some e => e.eval M Γ η G
    | none => fun _ => default := by
  simp only [hk, List.getElem?_map]
  cases es[k]? <;> rfl

/-- A well-formed expression does not read the name of a bound variable `w`
that does not occur in it. -/
theorem eval_indep_var (hA : M.Agree E) (hF : M.Frame) (hI : Inj Γ η) (hS : Supp Γ η G)
    {w s'} (hw : Γ[w]? = some (Binder.bound s')) {e s} (he : SExpr.Ok E Γ e s) :
    ¬ e.HasVar Γ w → Indep (e.eval M Γ η G) (η w) := by
  refine SExpr.Ok.rec' (P := fun e => ¬ e.HasVar Γ w → Indep (e.eval M Γ η G) (η w))
    ?_ ?_ he
  · intro v bi hv hn
    cases bi with
    | bound s =>
      rw [eval_bound M hv]
      refine indep_name _ _ fun h => hn ((hasVar_bound hv).2 (hI v w s s' hv hw h))
    | reg s vs =>
      rw [eval_reg M hv]
      exact hS v s vs w s' hv hw fun hm => hn ((hasVar_reg hv).2 hm)
  · intro t args ret o es ht hargs ih hn
    obtain ⟨-, hb, -⟩ := hargs.facts
    rw [eval_app]
    apply hF
    · intro k hk
      obtain ⟨s, hs⟩ := (hA t args ret o ht k).1 hk
      obtain ⟨v, hv, hvb⟩ := hb k s hs
      simp only [hk, ite_true, hv]
      intro h
      have := hI v w _ s' hvb hw h
      subst this
      exact hn (hasVar_app.2 ⟨_, List.mem_of_getElem? hv, (hasVar_bound hvb).2 rfl⟩)
    · intro k hk
      rw [den_at M t es k hk]
      cases he : es[k]? with
      | none => exact indep_const _ (fun _ _ => rfl) _
      | some e =>
        obtain ⟨s, vs, hs⟩ := reg_pos M hA ht hargs k hk e he
        exact ih k s vs e hs he fun h => hn (hasVar_app.2 ⟨e, List.mem_of_getElem? he, h⟩)

/-- A well-formed expression does not read a name that no bound variable of
the context has and that no regular variable reads. -/
theorem eval_indep_fresh (hA : M.Agree E) (hF : M.Frame) {n : Nat}
    (hη : ∀ v s, Γ[v]? = some (Binder.bound s) → η v ≠ n)
    (hG : ∀ u s vs, Γ[u]? = some (Binder.reg s vs) → Indep (G u) n)
    {e s} (he : SExpr.Ok E Γ e s) : Indep (e.eval M Γ η G) n := by
  refine SExpr.Ok.rec' (P := fun e => Indep (e.eval M Γ η G) n) ?_ ?_ he
  · intro v bi hv
    cases bi with
    | bound s => rw [eval_bound M hv]; exact indep_name _ _ (hη v s hv)
    | reg s vs => rw [eval_reg M hv]; exact hG v s vs hv
  · intro t args ret o es ht hargs ih
    obtain ⟨-, hb, -⟩ := hargs.facts
    rw [eval_app]
    apply hF
    · intro k hk
      obtain ⟨s, hs⟩ := (hA t args ret o ht k).1 hk
      obtain ⟨v, hv, hvb⟩ := hb k s hs
      simp only [hk, ite_true, hv]
      exact hη v _ hvb
    · intro k hk
      rw [den_at M t es k hk]
      cases he : es[k]? with
      | none => exact indep_const _ (fun _ _ => rfl) _
      | some e =>
        obtain ⟨s, vs, hs⟩ := reg_pos M hA ht hargs k hk e he
        exact ih k s vs e hs he

/-- Evaluation reads `η` only at bound variables and `G` only at regular
variables, and a well-formed expression does not see variables beyond its
context. -/
theorem eval_congr (hA : M.Agree E) {Γ' : Ctx} {η' : Nat → Nat} {G' : Nat → (Nat → U) → U}
    (hΓ : ∀ (v : Nat) bi, Γ[v]? = some bi → Γ'[v]? = some bi)
    (hη : ∀ v s, Γ[v]? = some (Binder.bound s) → η v = η' v)
    (hG : ∀ u s vs, Γ[u]? = some (Binder.reg s vs) → G u = G' u)
    {e s} (he : SExpr.Ok E Γ e s) : e.eval M Γ η G = e.eval M Γ' η' G' := by
  refine SExpr.Ok.rec' (P := fun e => e.eval M Γ η G = e.eval M Γ' η' G') ?_ ?_ he
  · intro v bi hv
    cases bi with
    | bound s => rw [eval_bound M hv, eval_bound M (hΓ v _ hv), hη v s hv]
    | reg s vs => rw [eval_reg M hv, eval_reg M (hΓ v _ hv), hG v s vs hv]
  · intro t args ret o es ht hargs ih
    obtain ⟨-, hb, -⟩ := hargs.facts
    rw [eval_app, eval_app]
    congr 1
    · funext k
      by_cases hk : M.bnd t k
      · obtain ⟨s, hs⟩ := (hA t args ret o ht k).1 hk
        obtain ⟨v, hv, hvb⟩ := hb k s hs
        simp only [hk, ite_true, hv]
        exact hη v _ hvb
      · simp [hk]
    · funext k
      by_cases hk : M.bnd t k
      · simp [hk]
      · have hk : M.bnd t k = false := by simpa using hk
        rw [den_at M t es k hk, den_at M t es k hk]
        cases he : es[k]? with
        | none => rfl
        | some e =>
          obtain ⟨s, vs, hs⟩ := reg_pos M hA ht hargs k hk e he
          exact ih k s vs e hs he

end

/-! ## Conversion -/

theorem nodup_getElem? {α} : ∀ {l : List α}, l.Nodup →
    ∀ (i j : Nat) a, l[i]? = some a → l[j]? = some a → i = j
  | [], _, _, _, _, h, _ => by simp at h
  | b :: l, hn, i, j, a, hi, hj => by
    rw [List.nodup_cons] at hn
    cases i <;> cases j
    · rfl
    · simp at hi hj; subst hi; exact absurd (List.mem_of_getElem? hj) hn.1
    · simp at hi hj; subst hj; exact absurd (List.mem_of_getElem? hi) hn.1
    · simp at hi hj; rw [nodup_getElem? hn.2 _ _ a hi hj]

theorem getTerm_defn {E : Env} {t args ret ys val}
    (h : E.getTerm t args ret (some (ys, val))) : Decl.defn t args ret (some (ys, val)) ∈ E := by
  cases h with
  | defn h => exact h

section
variable {E : Env} {Γ : Ctx} {η : Nat → Nat} {G : Nat → (Nat → U) → U}

theorem ConvArgs.length_args : ∀ {es1 es2 args}, ConvArgs E Γ es1 es2 args →
    es1.length = args.length
  | _, _, _, .nil => rfl
  | _, _, _, .bound _ h => by simp [h.length_args]
  | _, _, _, .reg _ h => by simp [h.length_args]

theorem bnd_false_of_reg (hA : M.Agree E) {t args ret o} (ht : E.getTerm t args ret o)
    {k s vs} (hk : args[k]? = some (Binder.reg s vs)) : M.bnd t k = false := by
  cases h : M.bnd t k
  · rfl
  · obtain ⟨s', hs'⟩ := (hA t args ret o ht k).1 h
    rw [hk] at hs'; cases hs'

mutual
/-- Convertible expressions have equal denotations. -/
theorem Conv.sound (hM : M.Of E) (hI : Inj Γ η) (hS : Supp Γ η G) :
    ∀ {e1 e2 s}, Conv E Γ e1 e2 s → e1.eval M Γ η G = e2.eval M Γ η G
  | _, _, _, .refl _ => rfl
  | _, _, _, .symm h => (Conv.sound hM hI hS h).symm
  | _, _, _, .trans h1 h2 => (Conv.sound hM hI hS h1).trans (Conv.sound hM hI hS h2)
  | _, _, _, .cong (t := t) (args := args) (ret := ret) (o := o) (es1 := es1) (es2 := es2)
      ht h => by
    obtain ⟨hlen, hb, hr⟩ := ConvArgs.sound hM hI hS h
    rw [eval_app, eval_app]
    congr 1
    · funext k
      by_cases hk : M.bnd t k
      · obtain ⟨s, hs⟩ := (hM.agree t args ret o ht k).1 hk
        obtain ⟨v, h1, h2⟩ := hb k s hs
        simp [hk, h1, h2]
      · simp [hk]
    · funext k
      by_cases hk : M.bnd t k
      · simp [hk]
      · have hk : M.bnd t k = false := by simpa using hk
        rw [den_at M t es1 k hk, den_at M t es2 k hk]
        cases h1 : es1[k]? with
        | none =>
          have : es2[k]? = none := by
            rw [List.getElem?_eq_none_iff] at h1 ⊢; omega
          rw [this]
        | some e1 =>
          have hk1 := (List.getElem?_eq_some_iff.1 h1).1
          obtain ⟨e2, h2⟩ : ∃ e2, es2[k]? = some e2 :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          rw [h2]
          match ha : args[k]? with
          | none =>
            have := ConvArgs.length_args h
            rw [List.getElem?_eq_none_iff] at ha; omega
          | some (Binder.bound s) =>
            have := (hM.agree t args ret o ht k).2 ⟨s, ha⟩
            simp [hk] at this
          | some (Binder.reg s vs) => exact hr k s vs e1 e2 ha h1 h2
  | _, _, _, .unfold (t := t) (args := args) (ret := ret) (ys := ys) (val := val) (es := es)
      (zs := zs) ht hargs hzs hnd hfresh => by
    obtain ⟨hlen, hb, hr⟩ := hargs.facts
    have hzlen := hzs.length_eq
    have hσ_lt : ∀ k : Nat, k < es.length → (es ++ zs.map SExpr.var)[k]? = es[k]? := fun k hk => by
      simp [List.getElem?_append_left hk]
    have hσ_dummy : ∀ i : Nat, (es ++ zs.map SExpr.var)[args.length + i]? = (zs[i]?).map SExpr.var :=
      fun i => by simp [← hlen, List.getElem?_append_right]
    have hz : ∀ (i : Nat) (z : VarId), zs[i]? = some z → ∃ y, ys[i]? = some y ∧ Γ[z]? = some (Binder.bound y) := by
      intro i z h
      have hi := (List.getElem?_eq_some_iff.1 h).1
      obtain ⟨y, hy⟩ : ∃ y, ys[i]? = some y := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      exact ⟨y, hy, hzs.get i y z hy h⟩
    have hσ : ∀ (v : Nat) s, (appendDummies args ys)[v]? = some (Binder.bound s) →
        ∃ (y : VarId) (s' : SortId), (es ++ zs.map SExpr.var)[v]? = some (SExpr.var y) ∧
          Γ[y]? = some (Binder.bound s') := by
      intro v s hv
      rcases appendDummies_cases args ys v _ hv with ⟨hlt, ha⟩ | ⟨i, s, rfl, hi, -⟩
      · obtain ⟨y, h1, h2⟩ := hb v s ha
        exact ⟨y, s, by rw [hσ_lt v (by omega), h1], h2⟩
      · have := (List.getElem?_eq_some_iff.1 hi).1
        obtain ⟨z, hzi⟩ : ∃ z, zs[i]? = some z := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨y, -, hzb⟩ := hz i z hzi
        exact ⟨z, y, by rw [hσ_dummy, hzi]; rfl, hzb⟩
    rw [eval_app, eval_subst M Γ (appendDummies args ys) _ η G hσ val]
    have hσd : ∀ (i : Nat) (z : VarId), zs[i]? = some z →
        substNames η (es ++ zs.map SExpr.var) (args.length + i) = η z := by
      intro i z h
      simp [substNames, List.getD_eq_getElem?_getD, hσ_dummy, h]
    have hzget : ∀ i : Nat, i < ys.length → ∃ z : VarId, zs[i]? = some z := fun i hi =>
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    apply hM.defs t args ret ys val (getTerm_defn ht)
    · -- bound arguments keep their names
      intro k s hk
      obtain ⟨v, h1, -⟩ := hb k s hk
      have hbk := (hM.agree t args ret _ ht k).2 ⟨s, hk⟩
      have hk' : k < es.length := (List.getElem?_eq_some_iff.1 h1).1
      simp [hbk, h1, substNames, List.getD_eq_getElem?_getD, hσ_lt k hk']
    · -- regular arguments keep their denotations
      intro k s vs hk
      obtain ⟨e, h1, -⟩ := hr k s vs hk
      have hbk := bnd_false_of_reg M hM.agree ht hk
      have hk' : k < es.length := (List.getElem?_eq_some_iff.1 h1).1
      funext ρ
      rw [den_at M t es k hbk, h1]
      simp [substDen, List.getD_eq_getElem?_getD, hσ_lt k hk', h1]
    · -- the dummies get distinct names
      intro i j hi hj h
      obtain ⟨zi, hzi⟩ := hzget i hi
      obtain ⟨zj, hzj⟩ := hzget j hj
      rw [hσd i zi hzi, hσd j zj hzj] at h
      obtain ⟨yi, -, hbi⟩ := hz i zi hzi
      obtain ⟨yj, -, hbj⟩ := hz j zj hzj
      have := hI zi zj yi yj hbi hbj h
      subst this
      exact nodup_getElem? hnd i j zi hzi hzj
    · -- the dummies' names differ from the bound arguments' names
      intro i k s hi hk h
      obtain ⟨zi, hzi⟩ := hzget i hi
      obtain ⟨v, h1, hvb⟩ := hb k s hk
      have hbk := (hM.agree t args ret _ ht k).2 ⟨s, hk⟩
      rw [hσd i zi hzi] at h
      simp only [hbk, ite_true, h1] at h
      obtain ⟨yi, -, hbi⟩ := hz i zi hzi
      have := hI zi v yi s hbi hvb h
      subst this
      exact hfresh _ (List.mem_of_getElem? h1) zi (List.mem_of_getElem? hzi)
        ((hasVar_bound hvb).2 rfl)
    · -- regular arguments do not read the dummies' names
      intro i k s vs hi hk
      obtain ⟨zi, hzi⟩ := hzget i hi
      obtain ⟨e, h1, he⟩ := hr k s vs hk
      have hbk := bnd_false_of_reg M hM.agree ht hk
      rw [den_at M t es k hbk, h1, hσd i zi hzi]
      obtain ⟨yi, -, hbi⟩ := hz i zi hzi
      exact eval_indep_var M hM.agree hM.frame hI hS hbi he
        (hfresh e (List.mem_of_getElem? h1) zi (List.mem_of_getElem? hzi))

/-- Argument-wise conversion: equal lengths, the same variable at bound
positions, and equal denotations at regular positions. -/
theorem ConvArgs.sound (hM : M.Of E) (hI : Inj Γ η) (hS : Supp Γ η G) :
    ∀ {es1 es2 args}, ConvArgs E Γ es1 es2 args →
    es1.length = es2.length ∧
    (∀ (k : Nat) s, args[k]? = some (Binder.bound s) →
      ∃ v : VarId, es1[k]? = some (SExpr.var v) ∧ es2[k]? = some (SExpr.var v)) ∧
    (∀ (k : Nat) s vs e1 e2, args[k]? = some (Binder.reg s vs) → es1[k]? = some e1 →
      es2[k]? = some e2 → e1.eval M Γ η G = e2.eval M Γ η G)
  | _, _, _, .nil => by simp
  | _, _, _, .bound _ h => by
    obtain ⟨h1, h2, h3⟩ := ConvArgs.sound hM hI hS h
    refine ⟨by simp [h1], ?_, ?_⟩
    · intro k s hk; cases k with
      | zero => simp at hk ⊢
      | succ k => simpa using h2 k s (by simpa using hk)
    · intro k s vs e1 e2 hk he1 he2; cases k with
      | zero => simp at hk
      | succ k =>
        exact h3 k s vs e1 e2 (by simpa using hk) (by simpa using he1) (by simpa using he2)
  | _, _, _, .reg hc h => by
    obtain ⟨h1, h2, h3⟩ := ConvArgs.sound hM hI hS h
    refine ⟨by simp [h1], ?_, ?_⟩
    · intro k s hk; cases k with
      | zero => simp at hk
      | succ k => simpa using h2 k s (by simpa using hk)
    · intro k s vs e1 e2 hk he1 he2; cases k with
      | zero =>
        simp at he1 he2; subst he1; subst he2
        exact Conv.sound hM hI hS hc
      | succ k =>
        exact h3 k s vs e1 e2 (by simpa using hk) (by simpa using he1) (by simpa using he2)
end

end

/-! ## Proofs -/

/-- A strict upper bound for `f` below `n`. -/
def natSup (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => max (natSup f n) (f n + 1)

theorem lt_natSup (f : Nat → Nat) : ∀ {n v}, v < n → f v < natSup f n
  | n + 1, v, h => by
    simp only [natSup]
    by_cases hv : v < n
    · have := lt_natSup f hv; omega
    · have : v = n := by omega
      subst this; omega

theorem getElem?_lt {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) : i < l.length :=
  (List.getElem?_eq_some_iff.1 h).1

/-- Valuations that agree outside finitely many names a function does not
read give it the same value. -/
theorem indep_agree {f : (Nat → U) → U} :
    ∀ {L : List Nat}, (∀ n ∈ L, Indep f n) →
      ∀ ρ ρ', (∀ m, m ∉ L → ρ m = ρ' m) → f ρ = f ρ'
  | [], _, ρ, ρ', h => by
    have : ρ = ρ' := funext fun m => h m (by simp)
    rw [this]
  | n :: L, hL, ρ, ρ', h => by
    have h1 : f (upd ρ n (ρ' n)) = f ρ := hL n (List.mem_cons_self ..) ρ (ρ' n)
    rw [← h1]
    refine indep_agree (L := L) (fun m hm => hL m (List.mem_cons_of_mem _ hm)) _ _
      fun m hm => ?_
    by_cases e : m = n
    · subst e; simp [upd]
    · simp only [upd, if_neg e]; exact h m (by simp [e, hm])

/-- Soundness of one proof: in a model of `E` in which the theorems of `E`
are valid, whatever `Proof E Γ Hs` derives holds at every good valuation
near `ρ₀`, if the hypotheses `Hs` do. -/
theorem Proof.sound {E : Env} (hM : M.Of E)
    (hT : ∀ a hs r, Decl.thm a hs r ∈ E → M.Valid a hs r)
    {Γ : Ctx} {Hs : SExpr → Prop} {φ : SExpr} (h : Proof E Γ Hs φ)
    (η : Nat → Nat) (G : Nat → (Nat → U) → U) (N : Nat)
    (hI : Inj Γ η) (hS : Supp Γ η G) (hB : Bounded Γ G N) (ρ₀ : Nat → U)
    (hH : ∀ h, Hs h → ∀ ρ, Near M Γ η ρ₀ ρ → M.prov (h.eval M Γ η G ρ)) :
    ∀ ρ, Near M Γ η ρ₀ ρ → M.prov (φ.eval M Γ η G ρ) := by
  induction h with
  | hyp h => exact hH _ h
  | conv hc _ ih =>
    intro ρ hρ
    rw [← Conv.sound M hM hI hS hc]; exact ih ρ hρ
  | @thm args hs ret σ hthm hok hsafe _ ih =>
    have hV : M.Valid args hs ret := by
      rcases hthm with h | h
      · exact hM.axioms _ _ _ h
      · exact hT _ _ _ h
    obtain ⟨hlen, hb, hr⟩ := hok.facts
    have hσ : ∀ (v : Nat) s, args[v]? = some (Binder.bound s) →
        ∃ (y : VarId) (s' : SortId), σ[v]? = some (SExpr.var y) ∧
          Γ[y]? = some (Binder.bound s') := fun v s hv => by
      obtain ⟨y, h1, h2⟩ := hb v s hv
      exact ⟨y, s, h1, h2⟩
    have hname : ∀ v y, σ[v]? = some (SExpr.var y) → substNames η σ v = η y := by
      intro v y h; simp [substNames, List.getD_eq_getElem?_getD, h]
    have hden : ∀ v e, σ[v]? = some e → substDen M Γ η G σ v = e.eval M Γ η G := by
      intro v e h; simp [substDen, List.getD_eq_getElem?_getD, h]
    have hsub := eval_subst M Γ args σ η G hσ
    intro ρ hρ
    rw [hsub]
    refine hV (substNames η σ) (substDen M Γ η G σ) (max N (natSup η Γ.length))
      ?_ ?_ ?_ ρ ?_ ?_
    · -- distinct bound variables get distinct names
      intro u w s s' hu hw he
      obtain ⟨yu, hu1, hu2⟩ := hb u s hu
      obtain ⟨yw, hw1, hw2⟩ := hb w s' hw
      rw [hname u yu hu1, hname w yw hw1] at he
      have hy := hI yu yw s s' hu2 hw2 he
      subst hy
      refine Classical.byContradiction fun hne => ?_
      refine hsafe u w ⟨s, hu⟩ (getElem?_lt hw) (fun h => hne ((hasVar_bound hw).1 h).symm)
        yu _ hu1 hw1 ((hasVar_bound hw2).2 rfl)
    · -- regular variables respect their dependencies
      intro u s vs w s' hu hw hnot
      obtain ⟨e, he1, he2⟩ := hr u s vs hu
      obtain ⟨yw, hw1, hw2⟩ := hb w s' hw
      rw [hden u e he1, hname w yw hw1]
      exact eval_indep_var M hM.agree hM.frame hI hS hw2 he2
        (hsafe w u ⟨s', hw⟩ (getElem?_lt hu) (fun h => hnot ((hasVar_reg hu).1 h)) yw e hw1 he1)
    · -- regular variables read finitely many names
      intro u s vs n hu hn
      obtain ⟨e, he1, he2⟩ := hr u s vs hu
      rw [hden u e he1]
      refine eval_indep_fresh M hM.agree hM.frame ?_ ?_ he2
      · intro v s hv
        have := lt_natSup η (getElem?_lt hv); omega
      · intro u s vs hu
        exact hB u s vs n hu (by omega)
    · -- the instance's bound variables are well sorted
      intro v s hv
      obtain ⟨y, h1, h2⟩ := hb v s hv
      rw [hname v y h1]
      exact hρ.1 y s h2
    · -- the hypotheses hold near `ρ`
      intro h hm ρ' hρ'
      rw [← hsub]
      refine ih h hm ρ' ⟨fun w s hw => ?_, fun n hn => ?_⟩
      · by_cases hk : ∃ k sk, args[k]? = some (Binder.bound sk) ∧ substNames η σ k = η w
        · obtain ⟨k, sk, hk1, hk2⟩ := hk
          obtain ⟨y, h1, h2⟩ := hb k sk hk1
          rw [hname k y h1] at hk2
          have := hI y w sk s h2 hw hk2
          subst this
          have hsk := hρ'.1 k sk hk1
          rw [hname k y h1] at hsk
          have e : Binder.bound sk = Binder.bound s := Option.some.inj (h2.symm.trans hw)
          cases e; exact hsk
        · rw [hρ'.2 (η w) fun k sk hk1 he => hk ⟨k, sk, hk1, he⟩]
          exact hρ.1 w s hw
      · have hn' : ∀ (k : Nat) sk, args[k]? = some (Binder.bound sk) → substNames η σ k ≠ n := by
          intro k sk hk1
          obtain ⟨y, h1, h2⟩ := hb k sk hk1
          rw [hname k y h1]; exact hn y sk h2
        rw [hρ'.2 n hn']; exact hρ.2 n hn

theorem getTerm_mono {E E' : Env} (hsub : ∀ d ∈ E, d ∈ E') {t a r o}
    (h : E.getTerm t a r o) : E'.getTerm t a r o := by
  cases h with
  | term h => exact .term (hsub _ h)
  | defn h => exact .defn (hsub _ h)

theorem Model.Of.mono {E E' : Env} (hsub : ∀ d ∈ E, d ∈ E') (hM : M.Of E') : M.Of E where
  agree t a r o h := hM.agree t a r o (getTerm_mono hsub h)
  frame := hM.frame
  defs t a r ds val h := hM.defs t a r ds val (hsub _ h)
  axioms a hs r h := hM.axioms a hs r (hsub _ h)

theorem Env.Ok.snoc' {E E' : Env} {d : Decl} (h : Env.Ok E') (he : E' = E ++ [d]) :
    Env.Ok E ∧ Decl.Ok E d := by
  cases h with
  | nil => simp at he
  | cons h1 h2 =>
    obtain ⟨rfl, h⟩ := List.append_inj' he rfl
    simp at h; subst h
    exact ⟨h1, h2⟩

theorem Env.Ok.snoc {E : Env} {d : Decl} (h : Env.Ok (E ++ [d])) : Env.Ok E ∧ Decl.Ok E d :=
  h.snoc' rfl

/-- A theorem proved with dummies `ds` is valid for its binders `a`. The
dummies get names above every name the arguments use, and values in their
sorts' carriers. -/
theorem Model.Valid.of_dummies {E : Env} (hA : M.Agree E) (hF : M.Frame) {a : Ctx}
    {ds : List SortId} {hs : List SExpr} {r : SExpr} (hok : AxiomOk E a hs r)
    (h : ∀ η G N, Inj (appendDummies a ds) η → Supp (appendDummies a ds) η G →
      Bounded (appendDummies a ds) G N → ∀ ρ₀,
      (∀ x ∈ hs, ∀ ρ, Near M (appendDummies a ds) η ρ₀ ρ →
        M.prov (x.eval M (appendDummies a ds) η G ρ)) →
      ∀ ρ, Near M (appendDummies a ds) η ρ₀ ρ →
        M.prov (r.eval M (appendDummies a ds) η G ρ)) :
    M.Valid a hs r := by
  intro η G N hI hS hB ρ₀ hgood hH
  let K := max N (natSup η a.length)
  let η' : Nat → Nat := fun v => if v < a.length then η v else K + (v - a.length)
  have hlt : ∀ v, v < a.length → η' v = η v := fun v hv => by simp [η', hv]
  have hge : ∀ i, η' (a.length + i) = K + i := fun i => by
    simp only [η']; rw [if_neg (by omega)]; congr 1; omega
  have hK : ∀ v, v < a.length → η v < K := fun v hv => by
    have := lt_natSup η hv; omega
  -- `x` evaluates the same in `a` and in `a` extended with dummies
  have hsame : ∀ x ∈ r :: hs, x.eval M a η G = x.eval M (appendDummies a ds) η' G := by
    intro x hx
    obtain ⟨s, -, hx, -, -⟩ := hok.2 x hx
    refine eval_congr M hA (fun v bi hv => ?_) (fun v s hv => (hlt v (getElem?_lt hv)).symm)
      (fun _ _ _ _ => rfl) hx
    rw [appendDummies_lt a ds v (getElem?_lt hv)]; exact hv
  -- `x` does not read the dummies' names
  let D : Nat → Prop := fun n => K ≤ n ∧ n < K + ds.length
  have hreset : ∀ x ∈ r :: hs, ∀ ρ ρ' : Nat → U, (∀ n, ¬ D n → ρ n = ρ' n) →
      x.eval M a η G ρ = x.eval M a η G ρ' := by
    intro x hx ρ ρ' hρ
    obtain ⟨s, -, hx, -, -⟩ := hok.2 x hx
    refine indep_agree (L := (List.range ds.length).map (K + ·)) ?_ ρ ρ' fun m hm => ?_
    · intro n hn
      simp only [List.mem_map, List.mem_range] at hn
      obtain ⟨i, -, rfl⟩ := hn
      refine eval_indep_fresh M hA hF (fun v s hv => ?_) (fun u s vs hu => ?_) hx
      · have := hK v (getElem?_lt hv); omega
      · exact hB u s vs _ hu (by omega)
    · refine hρ m fun ⟨h1, h2⟩ => hm ?_
      simp only [List.mem_map, List.mem_range]
      exact ⟨m - K, by omega, by omega⟩
  -- values for the dummies
  have hc : ∀ i : Nat, ∃ c : U, ∀ s, ds[i]? = some s → M.sorts s c := fun i => by
    cases hi : ds[i]? with
    | none => exact ⟨default, fun _ h => by cases h⟩
    | some s =>
      obtain ⟨c, hc⟩ := M.sorts_nonempty s
      exact ⟨c, fun s' h => by cases h; exact hc⟩
  let c : Nat → U := fun i => Classical.choose (hc i)
  have hcs : ∀ (i : Nat) s, ds[i]? = some s → M.sorts s (c i) := fun i => Classical.choose_spec (hc i)
  let ρ₀' : Nat → U := fun n => if D n then c (n - K) else ρ₀ n
  have hρ₀' : ∀ n, ¬ D n → ρ₀' n = ρ₀ n := fun n hn => by simp [ρ₀', hn]
  rw [hreset r (List.mem_cons_self ..) ρ₀ ρ₀' fun n hn => (hρ₀' n hn).symm,
    hsame r (List.mem_cons_self ..)]
  have hInj : Inj (appendDummies a ds) η' := by
    intro v w s s' hv hw he
    rcases appendDummies_cases a ds v _ hv with ⟨hv1, hv2⟩ | ⟨i, _, rfl, -, -⟩ <;>
    rcases appendDummies_cases a ds w _ hw with ⟨hw1, hw2⟩ | ⟨j, _, rfl, -, -⟩
    · rw [hlt v hv1, hlt w hw1] at he; exact hI v w s s' hv2 hw2 he
    · rw [hlt v hv1, hge] at he; have := hK v hv1; omega
    · rw [hlt w hw1, hge] at he; have := hK w hw1; omega
    · rw [hge, hge] at he; omega
  -- a good valuation for the extended context
  have hgood' : Good M (appendDummies a ds) η' ρ₀' := by
    intro v s hv
    rcases appendDummies_cases a ds v _ hv with ⟨hv1, hv2⟩ | ⟨i, s', rfl, hi, he⟩
    · rw [hlt v hv1, hρ₀' _ fun ⟨h1, _⟩ => by have := hK v hv1; omega]
      exact hgood v s hv2
    · cases he
      rw [hge]
      have hD : D (K + i) := ⟨by omega, by have := getElem?_lt hi; omega⟩
      simp only [ρ₀', hD, if_true]
      rw [show K + i - K = i by omega]
      exact hcs i _ hi
  refine h η' G N hInj ?_ ?_ ρ₀' ?_ ρ₀' ⟨hgood', fun _ _ => rfl⟩
  · intro u s vs w s' hu hw hnot
    rcases appendDummies_cases a ds u _ hu with ⟨hu1, hu2⟩ | ⟨_, _, _, _, h⟩
    · rcases appendDummies_cases a ds w _ hw with ⟨hw1, hw2⟩ | ⟨j, _, rfl, -, -⟩
      · rw [hlt w hw1]; exact hS u s vs w s' hu2 hw2 hnot
      · rw [hge]; exact hB u s vs _ hu2 (by omega)
    · cases h
  · intro u s vs n hu hn
    rcases appendDummies_cases a ds u _ hu with ⟨hu1, hu2⟩ | ⟨_, _, _, _, h⟩
    · exact hB u s vs n hu2 hn
    · cases h
  · intro x hx ρ hρ
    rw [← hsame x (List.mem_cons_of_mem _ hx)]
    -- reset the dummies' names to `ρ₀`
    let ρ' : Nat → U := fun n => if D n then ρ₀ n else ρ n
    rw [hreset x (List.mem_cons_of_mem _ hx) ρ ρ' fun n hn => by simp [ρ', hn]]
    refine hH x hx ρ' ⟨fun v s hv => ?_, fun n hn => ?_⟩
    · have hv1 := getElem?_lt hv
      have hD : ¬ D (η v) := fun ⟨h1, _⟩ => by have := hK v hv1; omega
      simp only [ρ', hD, if_false]
      have := hρ.1 v s (by rw [appendDummies_lt a ds v hv1]; exact hv)
      rwa [hlt v hv1] at this
    · by_cases hD : D n
      · simp [ρ', hD]
      · simp only [ρ', hD, if_false]
        rw [hρ.2 n fun v s hv => ?_, hρ₀' n hD]
        rcases appendDummies_cases a ds v _ hv with ⟨hv1, hv2⟩ | ⟨i, _, rfl, hi, -⟩
        · rw [hlt v hv1]; exact hn v s hv2
        · rw [hge]; intro he; subst he
          exact hD ⟨by omega, by have := getElem?_lt hi; omega⟩

/-- **Soundness.** In a well-formed environment `E` whose theorems all have
proofs, every theorem is valid in every model of any environment containing
`E`. -/
theorem Env.Proof'.sound {E : Env} (hp : Env.Proof' E) (hok : Env.Ok E) {Ef : Env}
    (hsub : ∀ d ∈ E, d ∈ Ef) (hM : M.Of Ef) :
    ∀ a hs r, Decl.thm a hs r ∈ E → M.Valid a hs r := by
  induction hp with
  | nil => intro _ _ _ h; cases h
  | sort _ ih | term _ ih | defn _ ih | ax _ ih =>
    intro a hs r h
    rcases List.mem_append.1 h with h | h
    · exact ih hok.snoc.1 (fun d hd => hsub d (List.mem_append_left _ hd)) a hs r h
    · simp at h
  | @thm E a' hs' r' ds hctx hproof _ ih =>
    have ⟨hokE, hokd⟩ := hok.snoc
    have hsubE : ∀ d ∈ E, d ∈ Ef := fun d hd => hsub d (List.mem_append_left _ hd)
    have ihE := ih hokE hsubE
    intro a hs r h
    rcases List.mem_append.1 h with h | h
    · exact ihE a hs r h
    · simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hME := Model.Of.mono M hsubE hM
      exact Model.Valid.of_dummies M hME.agree hME.frame hokd fun η G N hI hS hB ρ₀ hH =>
        Proof.sound M hME ihE hproof η G N hI hS hB ρ₀ hH

/-- Every theorem of a well-formed, proved environment is valid in every
model of it. -/
theorem Env.Proof'.sound' {E : Env} (hp : Env.Proof' E) (hok : Env.Ok E) (hM : M.Of E) :
    ∀ a hs r, Decl.thm a hs r ∈ E → M.Valid a hs r :=
  hp.sound M hok (fun _ h => h) hM

end MM0
