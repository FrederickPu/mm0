import MM0.Sound
import MM0Examples.SetEnv

/-!
# A model of `set.mm0`

`examples/set.mm0` is the logical core of Metamath's `set.mm`: propositional
logic, first-order logic with equality and membership, the ZFC axioms, and
class abstraction. This file gives it a model, and so (via
`MM0.Env.Proof'.sound`) shows that its theorems hold in every model of ZFC.
It is the Lean 4 counterpart of `mm0-lean/mm0/fol.lean`, built on the
generic soundness theorem instead of a deep embedding of first-order logic.

Given a type `V` with a membership relation satisfying the ZFC axioms
(`ZFC V`):

* `wff` is read as `Prop`, `set` as `V`, and `class` as `V → Prop`;
* each term is read as the operation its name says (`wi` is `→`, `wal` is
  `∀`, `wel` is membership, `cab` is class abstraction, …), and each
  definition by its body.

`setModel_of` proves that this is a model of `setEnv`, the environment the
parser produces from `examples/set.mm0` (`MM0Examples/SetEnv.lean`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace MM0.SetModel

/-- The values: propositions, sets and classes, plus a junk value. -/
inductive Val (V : Type) : Type 1
  | prop (p : Prop)
  | set (a : V)
  | cls (A : V → Prop)
  | junk

instance {V} : Inhabited (Val V) := ⟨.junk⟩

variable {V : Type} [Inhabited V]

def Val.p : Val V → Prop
  | .prop p => p
  | _ => False

def Val.s : Val V → V
  | .set a => a
  | _ => default

def Val.c : Val V → V → Prop
  | .cls A => A
  | _ => fun _ => False

@[simp] theorem Val.p_prop (p : Prop) : (Val.prop p : Val V).p = p := rfl
@[simp] theorem Val.s_set (a : V) : (Val.set a : Val V).s = a := rfl
@[simp] theorem Val.c_cls (A : V → Prop) : (Val.cls A : Val V).c = A := rfl

variable (mem : V → V → Prop)

/-- The meaning of each term of `set.mm0` (numbered as in `setEnv`). Bound
arguments are given by name (`ν k`), and a binder updates the valuation at
that name. Definitions are read by their bodies, with each dummy replaced by
a quantified variable. -/
def term : TermId → (Nat → Nat) → (Nat → (Nat → Val V) → Val V) → (Nat → Val V) → Val V
  -- wi: ph -> ps
  | 0, _, S, ρ => .prop ((S 0 ρ).p → (S 1 ρ).p)
  -- wn: ~ph
  | 1, _, S, ρ => .prop (¬ (S 0 ρ).p)
  -- wb: ~((ph -> ps) -> ~(ps -> ph))
  | 2, _, S, ρ => .prop (¬ (((S 0 ρ).p → (S 1 ρ).p) → ¬ ((S 1 ρ).p → (S 0 ρ).p)))
  -- wa: ~(ph -> ~ps)
  | 3, _, S, ρ => .prop (¬ ((S 0 ρ).p → ¬ (S 1 ρ).p))
  -- or: ~ph -> ps
  | 4, _, S, ρ => .prop (¬ (S 0 ρ).p → (S 1 ρ).p)
  -- wtru: T.
  | 5, _, _, _ => .prop True
  -- wal {x} ph: A. x ph
  | 6, ν, S, ρ => .prop (∀ a : V, (S 1 (upd ρ (ν 0) (.set a))).p)
  -- wex {x} ph: ~(A. x ~ph)
  | 7, ν, S, ρ => .prop (¬ ∀ a : V, ¬ (S 1 (upd ρ (ν 0) (.set a))).p)
  -- weq a b: a =s b
  | 8, _, S, ρ => .prop ((S 0 ρ).s = (S 1 ρ).s)
  -- wel a b: a es. b
  | 9, _, S, ρ => .prop (mem (S 0 ρ).s (S 1 ρ).s)
  -- weu {x .y} ph: E. y A. x (ph <-> x =s y)
  | 10, ν, S, ρ => .prop (¬ ∀ b : V, ¬ ∀ a : V,
      ¬ (((S 1 (upd ρ (ν 0) (.set a))).p → a = b) → ¬ (a = b → (S 1 (upd ρ (ν 0) (.set a))).p)))
  -- sb a {x .y} ph: A. y (y =s a -> A. x (x =s y -> ph))
  | 11, ν, S, ρ => .prop (∀ b : V, b = (S 0 ρ).s →
      ∀ a : V, a = b → (S 2 (upd ρ (ν 1) (.set a))).p)
  -- cab {x} ph: {x | ph}
  | 12, ν, S, ρ => .cls fun a => (S 1 (upd ρ (ν 0) (.set a))).p
  -- welc a A: a ec. A
  | 13, _, S, ρ => .prop ((S 1 ρ).c (S 0 ρ).s)
  -- wceq {.x} A B: A. x (x ec. A <-> x ec. B)
  | 14, _, S, ρ => .prop (∀ a : V,
      ¬ (((S 0 ρ).c a → (S 1 ρ).c a) → ¬ ((S 1 ρ).c a → (S 0 ρ).c a)))
  -- cv {.x} a: {x | x es. a}
  | 15, _, S, ρ => .cls fun a => mem a (S 0 ρ).s
  -- wcel {.x} A B: E. x (x = A /\ x ec. B), where x = A is wceq (cv x) A
  | 16, _, S, ρ => .prop (¬ ∀ b : V, ¬ ¬ ((∀ a : V,
      ¬ ((mem a b → (S 0 ρ).c a) → ¬ ((S 0 ρ).c a → mem a b))) → ¬ (S 1 ρ).c b))
  | _, _, _, _ => .junk

/-- The bound argument positions: `wal`, `wex`, `weu` and `cab` bind their
first argument, `sb` its second. -/
def bnd : TermId → Nat → Bool
  | 6, 0 | 7, 0 | 10, 0 | 12, 0 | 11, 1 => true
  | _, _ => false

/-- The carriers: `wff` (sort 0) ranges over propositions, `set` (sort 1)
over sets, `class` (sort 2) over classes. -/
def sorts : SortId → Val V → Prop
  | 0, .prop _ => True
  | 1, .set _ => True
  | 2, .cls _ => True
  | _ + 3, _ => True
  | _, _ => False

theorem sorts_nonempty : ∀ s, ∃ a : Val V, sorts s a
  | 0 => ⟨.prop True, trivial⟩
  | 1 => ⟨.set default, trivial⟩
  | 2 => ⟨.cls fun _ => True, trivial⟩
  | _ + 3 => ⟨.junk, trivial⟩

def model : Model (Val V) where
  term := term mem
  bnd := bnd
  sorts := sorts
  sorts_nonempty := sorts_nonempty
  prov v := v.p

/-- A value in the carrier of `set` is a set. -/
theorem eq_set_of_sorts {a : Val V} (h : sorts 1 a) : a = .set a.s := by
  cases a <;> simp_all [sorts]

/-- The ZFC axioms for `mem`, in the form `set.mm0` states them. Unique
existence is written `∃ b, ∀ z, P z ↔ z = b`, as `weu` defines it. -/
structure ZFC : Prop where
  ext : ∀ a b : V, (∀ x, mem x a ↔ mem x b) → a = b
  rep : ∀ (P : V → V → Prop) (a : V), (∀ y, ∃ x, ∀ z, P y z → z = x) →
    ∃ x, ∀ z, mem z x ↔ ∃ y, mem y a ∧ P y z
  pow : ∀ a : V, ∃ x, ∀ y, (∀ z, mem z y → mem z a) → mem y x
  un : ∀ a : V, ∃ x, ∀ y, (∃ z, mem y z ∧ mem z a) → mem y x
  reg : ∀ a : V, (∃ x, mem x a) → ∃ x, mem x a ∧ ∀ y, mem y x → ¬ mem y a
  inf : ∀ a : V, ∃ x, mem a x ∧ ∀ y, mem y x → ∃ z, mem y z ∧ mem z x
  ac : ∀ a : V, ∃ x, ∀ y, mem y a → (∃ z, mem z y) →
    ∃ b, ∀ z, (mem z y ∧ ∃ w, mem w x ∧ mem y w ∧ mem z w) ↔ z = b

/-! ## Valuations -/

variable {mem}

@[simp] theorem upd_same (ρ : Nat → Val V) (n : Nat) (a : Val V) : upd ρ n a n = a := by
  simp [upd]

theorem upd_ne (ρ : Nat → Val V) {m n : Nat} (a : Val V) (h : m ≠ n) : upd ρ n a m = ρ m := by
  simp [upd, h]

theorem upd_comm (ρ : Nat → Val V) {m n : Nat} (a b : Val V) (h : m ≠ n) :
    upd (upd ρ n a) m b = upd (upd ρ m b) n a := by
  funext k; simp only [upd]; split <;> split <;> simp_all

@[simp] theorem upd_upd (ρ : Nat → Val V) (n : Nat) (a b : Val V) :
    upd (upd ρ n a) n b = upd ρ n b := by
  funext k; simp only [upd]; split <;> simp_all

theorem upd_eta (ρ : Nat → Val V) (n : Nat) : upd ρ n (ρ n) = ρ := by
  funext k; simp only [upd]; split <;> simp_all

/-- Reading `f` after an update at a name it does not read. -/
theorem Indep.upd {f : (Nat → Val V) → Val V} {n : Nat} (h : Indep f n) (ρ) (a) :
    f (MM0.upd ρ n a) = f ρ := h ρ a

/-- Updating at a name `f` does not read, then at another one. -/
theorem Indep.upd₂ {f : (Nat → Val V) → Val V} {n m : Nat} (h : Indep f n) (hm : m ≠ n)
    (ρ) (a b) : f (MM0.upd (MM0.upd ρ n a) m b) = f (MM0.upd ρ m b) := by
  rw [upd_comm ρ a b hm]; exact h _ _

/-! ## Binders and frame -/

/-- The binders a declaration gives a term, if it declares one. -/
def declArgs : Decl → Option (TermId × Ctx)
  | .term t a _ => some (t, a)
  | .defn t a _ _ => some (t, a)
  | _ => none

theorem model_agree : (model mem).Agree setEnv := by
  have key : ∀ d ∈ setEnv, ∀ t a, declArgs d = some (t, a) →
      ∀ k, bnd t k = true ↔ ∃ s, a[k]? = some (Binder.bound s) := by
    simp only [setEnv, List.forall_mem_cons, List.not_mem_nil, declArgs,
      false_imp_iff, implies_true, and_true]
    and_intros <;>
    intro t a h <;> simp at h <;>
    (try obtain ⟨rfl, rfl⟩ := h) <;>
    intro k <;> rcases k with _ | _ | _ | _ | k <;> simp [bnd]
  intro t args r o ht k
  cases ht with
  | term h => exact key _ h t args rfl k
  | defn h => exact key _ h t args rfl k

theorem model_frame : (model mem).Frame := by
  intro t ν S n hν hS ρ c
  have hS' : ∀ k, bnd t k = false → ∀ ρ a, S k (upd ρ n a) = S k ρ := hS
  match t with
  | 0 | 1 | 2 | 3 | 4 | 8 | 9 | 13 | 14 | 15 | 16 =>
    simp only [model, term, hS' 0 rfl, hS' 1 rfl]
  | 5 => rfl
  | 6 | 7 | 10 | 12 => simp only [model, term, Indep.upd₂ (hS 1 rfl) (hν 0 rfl)]
  | 11 => simp only [model, term, hS' 0 rfl, Indep.upd₂ (hS 2 rfl) (hν 1 rfl)]
  | _ + 17 => rfl

/-! ## Regular variables as functions of their dependencies -/

/-- `f` reads none of the names in `L`, so valuations that agree outside `L`
give the same value. -/
theorem Indep.agree {f : (Nat → Val V) → Val V} :
    ∀ {L : List Nat}, (∀ n ∈ L, Indep f n) →
      ∀ ρ ρ', (∀ m, m ∉ L → ρ m = ρ' m) → f ρ = f ρ'
  | [], _, ρ, ρ', h => by
    have : ρ = ρ' := funext fun m => h m (by simp)
    rw [this]
  | n :: L, hL, ρ, ρ', h => by
    have h1 : f (MM0.upd ρ n (ρ' n)) = f ρ := hL n (List.mem_cons_self ..) ρ (ρ' n)
    rw [← h1]
    refine Indep.agree (L := L) (fun m hm => hL m (List.mem_cons_of_mem _ hm)) _ _
      fun m hm => ?_
    by_cases e : m = n
    · subst e; exact upd_same _ _ _
    · rw [upd_ne _ _ e]; exact h m (by simp [e, hm])

/-- A regular variable with no dependencies, among bound variables named `L`,
has the same value under any valuation that changes only names in `L`. -/
theorem norm0 {f : (Nat → Val V) → Val V} {L : List Nat} (hL : ∀ n ∈ L, Indep f n)
    (ρ : Nat → Val V) : ∀ ρ', (∀ m, m ∉ L → ρ' m = ρ m) → f ρ' = f ρ :=
  fun ρ' h => Indep.agree hL ρ' ρ h

/-- A regular variable depending on the bound variable named `d` is a
function of the set at `d`. -/
theorem norm1 {f : (Nat → Val V) → Val V} {L : List Nat} (hL : ∀ n ∈ L, Indep f n)
    (ρ : Nat → Val V) (d : Nat) (hd : d ∉ L) :
    ∃ P : V → Val V, ∀ ρ', (∀ m, m ∉ L → m ≠ d → ρ' m = ρ m) →
      ρ' d = .set (ρ' d).s → f ρ' = P (ρ' d).s := by
  refine ⟨fun a => f (upd ρ d (.set a)), fun ρ' h hs => Indep.agree hL _ _ fun m hm => ?_⟩
  by_cases e : m = d
  · subst e; rw [upd_same]; exact hs
  · rw [upd_ne _ _ e]; exact h m hm e

/-- A regular variable depending on the bound variables named `d₁` and `d₂`
is a function of the sets at `d₁` and `d₂`. -/
theorem norm2 {f : (Nat → Val V) → Val V} {L : List Nat} (hL : ∀ n ∈ L, Indep f n)
    (ρ : Nat → Val V) (d₁ d₂ : Nat) (hd₁ : d₁ ∉ L) (hd₂ : d₂ ∉ L) (h12 : d₁ ≠ d₂) :
    ∃ P : V → V → Val V, ∀ ρ', (∀ m, m ∉ L → m ≠ d₁ → m ≠ d₂ → ρ' m = ρ m) →
      ρ' d₁ = .set (ρ' d₁).s → ρ' d₂ = .set (ρ' d₂).s →
      f ρ' = P (ρ' d₁).s (ρ' d₂).s := by
  refine ⟨fun a b => f (upd (upd ρ d₁ (.set a)) d₂ (.set b)),
    fun ρ' h hs₁ hs₂ => Indep.agree hL _ _ fun m hm => ?_⟩
  by_cases e₂ : m = d₂
  · subst e₂; rw [upd_same]; exact hs₂
  · rw [upd_ne _ _ e₂]
    by_cases e₁ : m = d₁
    · subst e₁; rw [upd_same]; exact hs₁
    · rw [upd_ne _ _ e₁]; exact h m hm e₁ e₂

/-- Discharges the side conditions of the `norm` lemmas: which names a
valuation changes, and that a name holds a set. -/
macro "upd_disch" : tactic =>
  `(tactic| first
    | (intro m hm₁; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm₁;
       simp_all [upd])
    | (intro m hm₁ hm₂; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm₁;
       simp_all [upd])
    | (intro m hm₁ hm₂ hm₃; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm₁;
       simp_all [upd])
    | simp_all [upd])

/-! ## Definitions -/

theorem def_wb : (model mem).DefValid 2 [(.reg 0 []), (.reg 0 [])] [] (.app 1 [(.app 0 [(.app 0 [(.var 0), (.var 1)]), (.app 1 [(.app 0 [(.var 1), (.var 0)])])])]) := by
  intro ν S η' G' hb hr hd hfresh hind
  have e0 := hr 0 0 [] rfl; have e1 := hr 1 0 [] rfl
  funext ρ
  simp [model, term, bnd, eval_app, eval_var, appendDummies, ← e0, ← e1]

theorem def_wa : (model mem).DefValid 3 [(.reg 0 []), (.reg 0 [])] [] (.app 1 [(.app 0 [(.var 0), (.app 1 [(.var 1)])])]) := by
  intro ν S η' G' hb hr hd hfresh hind
  have e0 := hr 0 0 [] rfl; have e1 := hr 1 0 [] rfl
  funext ρ
  simp [model, term, bnd, eval_app, eval_var, appendDummies, ← e0, ← e1]

theorem def_or : (model mem).DefValid 4 [(.reg 0 []), (.reg 0 [])] [] (.app 0 [(.app 1 [(.var 0)]), (.var 1)]) := by
  intro ν S η' G' hb hr hd hfresh hind
  have e0 := hr 0 0 [] rfl; have e1 := hr 1 0 [] rfl
  funext ρ
  simp [model, term, bnd, eval_app, eval_var, appendDummies, ← e0, ← e1]

theorem def_wex : (model mem).DefValid 7 [(.bound 1), (.reg 0 [0])] [] (.app 1 [(.app 6 [(.var 0), (.app 1 [(.var 1)])])]) := by
  intro ν S η' G' hb hr hd hfresh hind
  have b0 := hb 0 1 rfl; have e1 := hr 1 0 [0] rfl
  funext ρ
  simp [model, term, bnd, eval_app, eval_var, appendDummies, ← b0, ← e1]

theorem def_weu : (model mem).DefValid 10 [(.bound 1), (.reg 0 [0])] [1] (.app 7 [(.var 2), (.app 6 [(.var 0), (.app 2 [(.var 1), (.app 8 [(.var 0), (.var 2)])])])]) := by
  intro ν S η' G' hb hr hd hfresh hind
  have b0 := hb 0 1 rfl; have e1 := hr 1 0 [0] rfl
  have hne : η' 2 ≠ ν 0 := hfresh 0 0 1 (by simp) rfl
  have hi : Indep (S 1) (η' 2) := hind 0 1 0 [0] (by simp) rfl
  funext ρ
  simp [model, term, bnd, eval_app, eval_var, appendDummies, ← b0, ← e1, upd_ne _ _ hne,
    Indep.upd₂ hi (Ne.symm hne)]

theorem def_sb : (model mem).DefValid 11 [(.reg 1 []), (.bound 1), (.reg 0 [1])] [1] (.app 6 [(.var 3), (.app 0 [(.app 8 [(.var 3), (.var 0)]), (.app 6 [(.var 1), (.app 0 [(.app 8 [(.var 1), (.var 3)]), (.var 2)])])])]) := by
  intro ν S η' G' hb hr hd hfresh hind
  have e0 := hr 0 1 [] rfl; have b1 := hb 1 1 rfl; have e2 := hr 2 0 [1] rfl
  have hne : η' 3 ≠ ν 1 := hfresh 0 1 1 (by simp) rfl
  have hi0 : Indep (S 0) (η' 3) := hind 0 0 1 [] (by simp) rfl
  have hi2 : Indep (S 2) (η' 3) := hind 0 2 0 [1] (by simp) rfl
  funext ρ
  simp [model, term, bnd, eval_app, eval_var, appendDummies, ← e0, ← b1, ← e2,
    upd_ne _ _ hne, Indep.upd hi0, Indep.upd₂ hi2 (Ne.symm hne)]

theorem def_wceq : (model mem).DefValid 14 [(.reg 2 []), (.reg 2 [])] [1] (.app 6 [(.var 2), (.app 2 [(.app 13 [(.var 2), (.var 0)]), (.app 13 [(.var 2), (.var 1)])])]) := by
  intro ν S η' G' hb hr hd hfresh hind
  have e0 := hr 0 2 [] rfl; have e1 := hr 1 2 [] rfl
  have hi0 : Indep (S 0) (η' 2) := hind 0 0 2 [] (by simp) rfl
  have hi1 : Indep (S 1) (η' 2) := hind 0 1 2 [] (by simp) rfl
  funext ρ
  simp [model, term, bnd, eval_app, eval_var, appendDummies, ← e0, ← e1,
    Indep.upd hi0, Indep.upd hi1]

theorem def_cv : (model mem).DefValid 15 [(.reg 1 [])] [1] (.app 12 [(.var 1), (.app 9 [(.var 1), (.var 0)])]) := by
  intro ν S η' G' hb hr hd hfresh hind
  have e0 := hr 0 1 [] rfl
  have hi0 : Indep (S 0) (η' 1) := hind 0 0 1 [] (by simp) rfl
  funext ρ
  simp [model, term, bnd, eval_app, eval_var, appendDummies, ← e0, Indep.upd hi0]

theorem def_wcel : (model mem).DefValid 16 [(.reg 2 []), (.reg 2 [])] [1] (.app 7 [(.var 2), (.app 3 [(.app 14 [(.app 15 [(.var 2)]), (.var 0)]), (.app 13 [(.var 2), (.var 1)])])]) := by
  intro ν S η' G' hb hr hd hfresh hind
  have e0 := hr 0 2 [] rfl; have e1 := hr 1 2 [] rfl
  have hi0 : Indep (S 0) (η' 2) := hind 0 0 2 [] (by simp) rfl
  have hi1 : Indep (S 1) (η' 2) := hind 0 1 2 [] (by simp) rfl
  funext ρ
  simp [model, term, bnd, eval_app, eval_var, appendDummies, ← e0, ← e1,
    Indep.upd hi0, Indep.upd hi1]

/-! ## Axioms -/

theorem near_refl {M : Model (Val V)} {Γ : Ctx} {η : Nat → Nat} {ρ₀ : Nat → Val V}
    (hg : Good M Γ η ρ₀) : Near M Γ η ρ₀ ρ₀ := ⟨hg, fun _ _ => rfl⟩

/-- Changing a bound variable to a value of its sort stays near. -/
theorem near_upd {M : Model (Val V)} {Γ : Ctx} {η : Nat → Nat} {ρ₀ ρ : Nat → Val V}
    (hI : Inj Γ η) (hn : Near M Γ η ρ₀ ρ) {v : Nat} {s : SortId}
    (hv : Γ[v]? = some (Binder.bound s)) {a : Val V} (ha : M.sorts s a) :
    Near M Γ η ρ₀ (MM0.upd ρ (η v) a) := by
  refine ⟨fun w s' hw => ?_, fun n hn' => ?_⟩
  · by_cases e : η w = η v
    · have := hI w v s' s hw hv e
      subst this
      rw [hw] at hv; cases hv
      rw [e]; simp only [upd, if_true]; exact ha
    · simp only [upd, if_neg e]; exact hn.1 w s' hw
  · simp only [upd, if_neg (Ne.symm (hn' v s hv))]; exact hn.2 n hn'

/-- Two bound variables of the context have different names. -/
theorem name_ne {Γ : Ctx} {η : Nat → Nat} (hI : Inj Γ η) {v w : Nat} {s s' : SortId}
    (hv : Γ[v]? = some (Binder.bound s)) (hw : Γ[w]? = some (Binder.bound s'))
    (h : v ≠ w) : η v ≠ η w := fun e => h (hI v w s s' hv hw e)

variable (mem)

theorem valid_ax_1 : (model mem).Valid [(.reg 0 []), (.reg 0 [])] [] (.app 0 [(.var 0), (.app 0 [(.var 1), (.var 0)])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  simp [model, term, bnd, eval_app, eval_var]
  exact fun h _ => h

theorem valid_ax_2 : (model mem).Valid [(.reg 0 []), (.reg 0 []), (.reg 0 [])] [] (.app 0 [(.app 0 [(.var 0), (.app 0 [(.var 1), (.var 2)])]), (.app 0 [(.app 0 [(.var 0), (.var 1)]), (.app 0 [(.var 0), (.var 2)])])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  simp [model, term, bnd, eval_app, eval_var]
  exact fun h1 h2 h3 => h1 h3 (h2 h3)

theorem valid_ax_3 : (model mem).Valid [(.reg 0 []), (.reg 0 [])] [] (.app 0 [(.app 0 [(.app 1 [(.var 0)]), (.app 1 [(.var 1)])]), (.app 0 [(.var 1), (.var 0)])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  simp [model, term, bnd, eval_app, eval_var]
  exact fun h1 h2 => Classical.byContradiction fun h3 => h1 h3 h2

theorem valid_ax_mp : (model mem).Valid [(.reg 0 []), (.reg 0 [])] [(.var 0), (.app 0 [(.var 0), (.var 1)])] (.var 1) := by
  intro η G N hI hS hB ρ₀ hgood hH
  simp [model, term, bnd, eval_app, eval_var] at hH ⊢
  exact hH.2 ρ₀ (near_refl hgood) (hH.1 ρ₀ (near_refl hgood))

theorem valid_tru : (model mem).Valid [] [] (.app 5 []) := by
  intro η G N hI hS hB ρ₀ hgood hH
  simp [model, term, bnd, eval_app, eval_var]

theorem valid_ax_gen : (model mem).Valid [(.bound 1), (.reg 0 [0])] [(.var 1)] (.app 6 [(.var 0), (.var 1)]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  simp [model, term, bnd, eval_app, eval_var] at hH ⊢
  intro a
  exact hH _ (near_upd hI (near_refl hgood) (v := 0) rfl trivial)

theorem valid_ax_4 : (model mem).Valid [(.bound 1), (.reg 0 [0]), (.reg 0 [0])] [] (.app 0 [(.app 6 [(.var 0), (.app 0 [(.var 1), (.var 2)])]), (.app 0 [(.app 6 [(.var 0), (.var 1)]), (.app 6 [(.var 0), (.var 2)])])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  simp [model, term, bnd, eval_app, eval_var]
  exact fun h1 h2 a => h1 a (h2 a)

theorem valid_ax_5 : (model mem).Valid [(.bound 1), (.reg 0 [])] [] (.app 0 [(.var 1), (.app 6 [(.var 0), (.var 1)])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  have hi : Indep (G 1) (η 0) := hS 1 0 [] 0 1 rfl rfl (by simp)
  simp [model, term, bnd, eval_app, eval_var, Indep.upd hi]

theorem valid_ax_6 : (model mem).Valid [(.bound 1), (.reg 1 [])] [] (.app 7 [(.var 0), (.app 8 [(.var 0), (.var 1)])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  have hi : Indep (G 1) (η 0) := hS 1 1 [] 0 1 rfl rfl (by simp)
  simp [model, term, bnd, eval_app, eval_var, Indep.upd hi]

theorem valid_ax_7 : (model mem).Valid [(.reg 1 []), (.reg 1 []), (.reg 1 [])] [] (.app 0 [(.app 8 [(.var 0), (.var 1)]), (.app 0 [(.app 8 [(.var 0), (.var 2)]), (.app 8 [(.var 1), (.var 2)])])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  simp [model, term, bnd, eval_app, eval_var]
  exact fun h1 h2 => h1.symm.trans h2

theorem valid_ax_8 : (model mem).Valid [(.reg 1 []), (.reg 1 []), (.reg 1 [])] [] (.app 0 [(.app 8 [(.var 0), (.var 1)]), (.app 0 [(.app 9 [(.var 0), (.var 2)]), (.app 9 [(.var 1), (.var 2)])])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  simp [model, term, bnd, eval_app, eval_var]
  exact fun h1 h2 => h1 ▸ h2

theorem valid_ax_9 : (model mem).Valid [(.reg 1 []), (.reg 1 []), (.reg 1 [])] [] (.app 0 [(.app 8 [(.var 0), (.var 1)]), (.app 0 [(.app 9 [(.var 2), (.var 0)]), (.app 9 [(.var 2), (.var 1)])])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  simp [model, term, bnd, eval_app, eval_var]
  exact fun h1 h2 => h1 ▸ h2

theorem valid_ax_10 : (model mem).Valid [(.bound 1), (.reg 0 [0])] [] (.app 0 [(.app 1 [(.app 6 [(.var 0), (.var 1)])]), (.app 6 [(.var 0), (.app 1 [(.app 6 [(.var 0), (.var 1)])])])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  simp [model, term, bnd, eval_app, eval_var]

theorem valid_ax_11 : (model mem).Valid [(.bound 1), (.bound 1), (.reg 0 [0, 1])] [] (.app 0 [(.app 6 [(.var 0), (.app 6 [(.var 1), (.var 2)])]), (.app 6 [(.var 1), (.app 6 [(.var 0), (.var 2)])])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  have d01 : η 0 ≠ η 1 := name_ne hI (v := 0) (w := 1) rfl rfl (by decide)
  simp [model, term, bnd, eval_app, eval_var]
  intro h a b
  rw [upd_comm _ _ _ d01]; exact h b a

theorem valid_ax_12 : (model mem).Valid [(.bound 1), (.reg 1 []), (.reg 0 [0])] [] (.app 0 [(.app 8 [(.var 0), (.var 1)]), (.app 0 [(.var 2), (.app 6 [(.var 0), (.app 0 [(.app 8 [(.var 0), (.var 1)]), (.var 2)])])])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  have hi : Indep (G 1) (η 0) := hS 1 1 [] 0 1 rfl rfl (by simp)
  have hx := eq_set_of_sorts (hgood 0 1 rfl)
  simp [model, term, bnd, eval_app, eval_var, Indep.upd hi]
  intro h1 h2
  rw [← h1, ← hx, upd_eta]; exact h2

theorem valid_ax_8b : (model mem).Valid [(.reg 1 []), (.reg 1 []), (.reg 2 [])] [] (.app 0 [(.app 8 [(.var 0), (.var 1)]), (.app 0 [(.app 13 [(.var 0), (.var 2)]), (.app 13 [(.var 1), (.var 2)])])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  simp [model, term, bnd, eval_app, eval_var]
  exact fun h1 h2 => h1 ▸ h2

theorem valid_ax_clab : (model mem).Valid [(.reg 1 []), (.bound 1), (.reg 0 [1])] [] (.app 2 [(.app 13 [(.var 0), (.app 12 [(.var 1), (.var 2)])]), (.app 11 [(.var 0), (.var 1), (.var 2)])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  simp [model, term, bnd, eval_app, eval_var]

/-! ### The ZFC axioms -/

variable {mem} (hZ : ZFC mem)
include hZ

theorem valid_ax_ext : (model mem).Valid [(.bound 1), (.reg 1 []), (.reg 1 [])] [] (.app 0 [(.app 6 [(.var 0), (.app 2 [(.app 9 [(.var 0), (.var 1)]), (.app 9 [(.var 0), (.var 2)])])]), (.app 8 [(.var 1), (.var 2)])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  have hi1 : Indep (G 1) (η 0) := hS 1 1 [] 0 1 rfl rfl (by simp)
  have hi2 : Indep (G 2) (η 0) := hS 2 1 [] 0 1 rfl rfl (by simp)
  simp [model, term, bnd, eval_app, eval_var, Indep.upd hi1, Indep.upd hi2]
  exact fun h => hZ.ext _ _ fun x => ⟨(h x).1, (h x).2⟩


/-- Distinct bound positions `i` and `j` of an axiom have distinct names. -/
macro "names_ne" hI:ident i:num j:num : term =>
  `(name_ne $hI (v := $i) (w := $j) rfl rfl (by decide))

omit hZ in
/-- A set variable with no dependencies, among the bound variables at
positions `ws`, is a constant `A` under the valuations an axiom builds. -/
theorem const_of_supp {Γ : Ctx} {η : Nat → Nat} {G : Nat → (Nat → Val V) → Val V}
    (hS : Supp Γ η G) {u : Nat} {s : SortId} (hu : Γ[u]? = some (Binder.reg s []))
    (ρ₀ : Nat → Val V) (ws : List Nat) (hws : ∀ w ∈ ws, ∃ s', Γ[w]? = some (Binder.bound s')) :
    ∃ A, ∀ ρ', (∀ m, m ∉ ws.map η → ρ' m = ρ₀ m) → G u ρ' = A :=
  ⟨_, norm0 (fun n hn => by
    simp only [List.mem_map] at hn
    obtain ⟨w, hw, rfl⟩ := hn
    obtain ⟨s', hs'⟩ := hws w hw
    exact hS u s [] w s' hu hs' (by simp)) ρ₀⟩

theorem valid_ax_pow : (model mem).Valid [(.bound 1), (.bound 1), (.bound 1), (.reg 1 [])] [] (.app 7 [(.var 0), (.app 6 [(.var 1), (.app 0 [(.app 6 [(.var 2), (.app 0 [(.app 9 [(.var 2), (.var 1)]), (.app 9 [(.var 2), (.var 3)])])]), (.app 9 [(.var 1), (.var 0)])])])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  clear hH
  have d01 : η 0 ≠ η 1 := names_ne hI 0 1
  have d02 : η 0 ≠ η 2 := names_ne hI 0 2
  have d12 : η 1 ≠ η 2 := names_ne hI 1 2
  obtain ⟨A, hA⟩ := const_of_supp hS (u := 3) rfl ρ₀ [0, 1, 2] (by simp)
  simp only [List.map_cons, List.map_nil] at hA
  simp [model, term, bnd, eval_app, eval_var]
  simp (disch := upd_disch) only [hA]
  simp [upd, d01, d02, d12, Ne.symm d01, Ne.symm d02, Ne.symm d12]
  obtain ⟨x, hx⟩ := hZ.pow A.s
  exact ⟨x, fun y hy => hx y hy⟩

theorem valid_ax_un : (model mem).Valid [(.bound 1), (.bound 1), (.bound 1), (.reg 1 [])] [] (.app 7 [(.var 0), (.app 6 [(.var 1), (.app 0 [(.app 7 [(.var 2), (.app 3 [(.app 9 [(.var 1), (.var 2)]), (.app 9 [(.var 2), (.var 3)])])]), (.app 9 [(.var 1), (.var 0)])])])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  clear hH
  have d01 : η 0 ≠ η 1 := names_ne hI 0 1
  have d02 : η 0 ≠ η 2 := names_ne hI 0 2
  have d12 : η 1 ≠ η 2 := names_ne hI 1 2
  obtain ⟨A, hA⟩ := const_of_supp hS (u := 3) rfl ρ₀ [0, 1, 2] (by simp)
  simp only [List.map_cons, List.map_nil] at hA
  simp [model, term, bnd, eval_app, eval_var]
  simp (disch := upd_disch) only [hA]
  simp [upd, d01, d02, d12, Ne.symm d01, Ne.symm d02, Ne.symm d12]
  obtain ⟨x, hx⟩ := hZ.un A.s
  exact ⟨x, fun y z h1 h2 => hx y ⟨z, h1, h2⟩⟩

theorem valid_ax_reg : (model mem).Valid [(.bound 1), (.bound 1), (.reg 1 [])] [] (.app 0 [(.app 7 [(.var 0), (.app 9 [(.var 0), (.var 2)])]), (.app 7 [(.var 0), (.app 3 [(.app 9 [(.var 0), (.var 2)]), (.app 6 [(.var 1), (.app 0 [(.app 9 [(.var 1), (.var 0)]), (.app 1 [(.app 9 [(.var 1), (.var 2)])])])])])])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  clear hH
  have d01 : η 0 ≠ η 1 := names_ne hI 0 1
  obtain ⟨A, hA⟩ := const_of_supp hS (u := 2) rfl ρ₀ [0, 1] (by simp)
  simp only [List.map_cons, List.map_nil] at hA
  simp [model, term, bnd, eval_app, eval_var]
  simp (disch := upd_disch) only [hA]
  simp [upd, d01, Ne.symm d01]
  exact fun x hx => hZ.reg A.s ⟨x, hx⟩

theorem valid_ax_inf : (model mem).Valid [(.bound 1), (.reg 1 []), (.bound 1), (.bound 1)] [] (.app 7 [(.var 0), (.app 3 [(.app 9 [(.var 1), (.var 0)]), (.app 6 [(.var 2), (.app 0 [(.app 9 [(.var 2), (.var 0)]), (.app 7 [(.var 3), (.app 3 [(.app 9 [(.var 2), (.var 3)]), (.app 9 [(.var 3), (.var 0)])])])])])])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  clear hH
  have d02 : η 0 ≠ η 2 := names_ne hI 0 2
  have d03 : η 0 ≠ η 3 := names_ne hI 0 3
  have d23 : η 2 ≠ η 3 := names_ne hI 2 3
  obtain ⟨A, hA⟩ := const_of_supp hS (u := 1) rfl ρ₀ [0, 2, 3] (by simp)
  simp only [List.map_cons, List.map_nil] at hA
  simp [model, term, bnd, eval_app, eval_var]
  simp (disch := upd_disch) only [hA]
  simp [upd, d02, d03, d23, Ne.symm d02, Ne.symm d03, Ne.symm d23]
  exact hZ.inf A.s

theorem valid_ax_ac : (model mem).Valid [(.bound 1), (.bound 1), (.reg 1 []), (.bound 1), (.bound 1)] [] (.app 7 [(.var 0), (.app 6 [(.var 1), (.app 0 [(.app 9 [(.var 1), (.var 2)]), (.app 0 [(.app 7 [(.var 3), (.app 9 [(.var 3), (.var 1)])]), (.app 10 [(.var 3), (.app 3 [(.app 9 [(.var 3), (.var 1)]), (.app 7 [(.var 4), (.app 3 [(.app 3 [(.app 9 [(.var 4), (.var 0)]), (.app 9 [(.var 1), (.var 4)])]), (.app 9 [(.var 3), (.var 4)])])])])])])])])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  clear hH
  have d01 : η 0 ≠ η 1 := names_ne hI 0 1
  have d03 : η 0 ≠ η 3 := names_ne hI 0 3
  have d04 : η 0 ≠ η 4 := names_ne hI 0 4
  have d13 : η 1 ≠ η 3 := names_ne hI 1 3
  have d14 : η 1 ≠ η 4 := names_ne hI 1 4
  have d34 : η 3 ≠ η 4 := names_ne hI 3 4
  obtain ⟨A, hA⟩ := const_of_supp hS (u := 2) rfl ρ₀ [0, 1, 3, 4] (by simp)
  simp only [List.map_cons, List.map_nil] at hA
  simp [model, term, bnd, eval_app, eval_var]
  simp (disch := upd_disch) only [hA]
  simp [upd, d01, d03, d04, d13, d14, d34, Ne.symm d01, Ne.symm d03, Ne.symm d04,
    Ne.symm d13, Ne.symm d14, Ne.symm d34]
  obtain ⟨x, hx⟩ := hZ.ac A.s
  refine ⟨x, fun y hy z hz => ?_⟩
  obtain ⟨b, hb⟩ := hx y hy ⟨z, hz⟩
  exact ⟨b, fun z' => ⟨fun h1 w h2 h3 h4 => (hb z').1 ⟨h1, w, h2, h3, h4⟩,
    fun e => (hb z').2 e⟩⟩

theorem valid_ax_rep : (model mem).Valid [(.bound 1), (.bound 1), (.bound 1), (.reg 1 []), (.reg 0 [1, 2])] [] (.app 0 [(.app 6 [(.var 1), (.app 7 [(.var 0), (.app 6 [(.var 2), (.app 0 [(.var 4), (.app 8 [(.var 2), (.var 0)])])])])]), (.app 7 [(.var 0), (.app 6 [(.var 2), (.app 2 [(.app 9 [(.var 2), (.var 0)]), (.app 7 [(.var 1), (.app 3 [(.app 9 [(.var 1), (.var 3)]), (.var 4)])])])])])]) := by
  intro η G N hI hS hB ρ₀ hgood hH
  clear hH
  have d01 : η 0 ≠ η 1 := names_ne hI 0 1
  have d02 : η 0 ≠ η 2 := names_ne hI 0 2
  have d12 : η 1 ≠ η 2 := names_ne hI 1 2
  obtain ⟨A, hA⟩ := const_of_supp hS (u := 3) rfl ρ₀ [0, 1, 2] (by simp)
  simp only [List.map_cons, List.map_nil] at hA
  obtain ⟨P, hP⟩ := norm2 (f := G 4) (L := [η 0])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
        exact hS 4 0 [1, 2] 0 1 rfl rfl (by simp))
    ρ₀ (η 1) (η 2) (by simp [Ne.symm d01]) (by simp [Ne.symm d02]) d12
  simp [model, term, bnd, eval_app, eval_var]
  simp (disch := first
    | (intro m h1; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1
       simp [upd, h1.1, h1.2.1, h1.2.2])
    | (intro m h1 h2 h3; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1
       simp [upd, h1, h2, h3])
    | simp [upd, d01, d02, d12, Ne.symm d01, Ne.symm d02, Ne.symm d12]) only [hA, hP]
  simp [upd, d01, d02, d12, Ne.symm d01, Ne.symm d02, Ne.symm d12]
  intro h
  obtain ⟨x, hx⟩ := hZ.rep (fun y z => (P y z).p) A.s h
  exact ⟨x, fun z => ⟨fun hz => (hx z).1 hz, fun y hy hp => (hx z).2 ⟨y, hy, hp⟩⟩⟩

/-! ## The model -/

/-- What `Model.Of` asks of each declaration. -/
def DeclValid (M : Model (Val V)) : Decl → Prop
  | .defn t a _ (some (ds, val)) => M.DefValid t a ds val
  | .ax a hs r => M.Valid a hs r
  | _ => True

/-- **The model.** In any model of ZFC, the reading of `set.mm0` above is a
model of the environment the parser produces from `examples/set.mm0`. -/
theorem model_of : (model mem).Of setEnv := by
  have key : ∀ d ∈ setEnv, DeclValid (model mem) d := by
    simp only [setEnv, List.forall_mem_cons, List.not_mem_nil, DeclValid,
      false_imp_iff, implies_true, and_true]
    and_intros <;> first
      | trivial
      | exact def_wb | exact def_wa | exact def_or | exact def_wex | exact def_weu
      | exact def_sb | exact def_wceq | exact def_cv | exact def_wcel
      | exact valid_ax_1 mem | exact valid_ax_2 mem | exact valid_ax_3 mem
      | exact valid_ax_mp mem | exact valid_tru mem | exact valid_ax_gen mem
      | exact valid_ax_4 mem | exact valid_ax_5 mem | exact valid_ax_6 mem
      | exact valid_ax_7 mem | exact valid_ax_8 mem | exact valid_ax_9 mem
      | exact valid_ax_10 mem | exact valid_ax_11 mem | exact valid_ax_12 mem
      | exact valid_ax_8b mem | exact valid_ax_clab mem
      | exact valid_ax_ext hZ | exact valid_ax_rep hZ | exact valid_ax_pow hZ
      | exact valid_ax_un hZ | exact valid_ax_reg hZ | exact valid_ax_inf hZ
      | exact valid_ax_ac hZ
  exact {
    agree := model_agree
    frame := model_frame
    defs := fun t a r ds val h => key _ h
    axioms := fun a hs r h => key _ h }

/-- **The theorems of `set.mm0` hold in every model of ZFC**, given proofs of
them (`Env.Proof' setEnv`). Checking `set.mmb` with `mm0-c` establishes
that such proofs exist. Connecting the two needs the `.mmb` semantics of
`mm0-lean/mm0/mm0b.lean`, which is not ported yet. -/
theorem set_sound (hp : Env.Proof' setEnv) (hok : Env.Ok setEnv) :
    ∀ a hs r, Decl.thm a hs r ∈ setEnv → (model mem).Valid a hs r :=
  hp.sound' (model mem) hok (model_of hZ)

end MM0.SetModel
