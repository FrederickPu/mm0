import MM0.Spec

/-!
# A verified checker for MM0 derivations

Computable checkers for MM0's derivability predicate, each proved to imply
the corresponding relation of `MM0.Spec`. This is the trusted core of
`check_sound` (Plan.md): an `.mmb` reader only has to produce the proof terms
below, and it needs no proof itself, because anything it gets wrong is
rejected here.

* `infer` / `checkArgs`: expression typing (`SExpr.Ok`, `SExpr.OkArgs`).
* `hasVarB`: `SExpr.HasVar`.
* `safeSubstB`: `SafeSubst`.
* `checkConv`: conversion proofs (`ConvPf`, after `mm0.mm0`'s `CExpr`) give
  `Conv`.
* `check`: proofs (`Pf`, after `mm0.mm0`'s `VExpr`) give `Proof`.
* `checkFile`: a whole proof file gives `Env.Proof` (`check_sound`).
-/

namespace MM0.Check

/-! ## Looking up terms -/

/-- The first declaration of the term or definition `t`. -/
def findTerm (E : Env) (t : TermId) : Option (Ctx × DepType × Option (List SortId × SExpr)) :=
  E.findSome? fun
    | .term t' a r => if t' = t then some (a, r, none) else none
    | .defn t' a r o => if t' = t then some (a, r, o) else none
    | _ => none

theorem findTerm_sound {E : Env} {t a r o} (h : findTerm E t = some (a, r, o)) :
    E.getTerm t a r o := by
  obtain ⟨d, hd, h⟩ := List.exists_of_findSome?_eq_some h
  match d with
  | .term t' a' r' =>
    simp only at h; split at h
    · next ht =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h; subst ht; exact .term hd
    · simp at h
  | .defn t' a' r' o' =>
    simp only at h; split at h
    · next ht =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h; subst ht; exact .defn hd
    · simp at h
  | .sort .. | .ax .. | .thm .. => simp at h

/-! ## Typing -/

mutual
/-- The sort of a well-formed expression. -/
def infer (E : Env) (Γ : Ctx) : SExpr → Option SortId
  | .var v => Γ[v]?.map Binder.sort
  | .app t es => match findTerm E t with
    | some (args, ret, _) => if checkArgs E Γ es args then some ret.1 else none
    | none => none

/-- The arguments fit the binders. -/
def checkArgs (E : Env) (Γ : Ctx) : List SExpr → List Binder → Bool
  | [], [] => true
  | .var v :: es, .bound s :: bis => (Γ[v]? == some (.bound s)) && checkArgs E Γ es bis
  | e :: es, .reg s _ :: bis => (infer E Γ e == some s) && checkArgs E Γ es bis
  | _, _ => false
end

mutual
theorem infer_sound {E : Env} {Γ : Ctx} :
    ∀ {e s}, infer E Γ e = some s → SExpr.Ok E Γ e s
  | .var v, s, h => by
    simp only [infer, Option.map_eq_some_iff] at h
    obtain ⟨bi, h1, rfl⟩ := h
    exact .var h1
  | .app t es, s, h => by
    simp only [infer] at h
    split at h
    · next args ret o hf =>
      split at h
      · next hc =>
        simp at h; subst h
        exact .app (findTerm_sound hf) (checkArgs_sound hc)
      · simp at h
    · simp at h

theorem checkArgs_sound {E : Env} {Γ : Ctx} :
    ∀ {es bis}, checkArgs E Γ es bis = true → SExpr.OkArgs E Γ es bis
  | [], [], _ => .nil
  | .var v :: es, .bound s :: bis, h => by
    simp only [checkArgs, Bool.and_eq_true, beq_iff_eq] at h
    exact .bound h.1 (checkArgs_sound h.2)
  | .var v :: es, .reg s vs :: bis, h => by
    simp only [checkArgs, Bool.and_eq_true, beq_iff_eq] at h
    exact .reg (infer_sound h.1) (checkArgs_sound h.2)
  | .app t as :: es, .reg s vs :: bis, h => by
    simp only [checkArgs, Bool.and_eq_true, beq_iff_eq] at h
    exact .reg (infer_sound h.1) (checkArgs_sound h.2)
  | .app _ _ :: _, .bound _ :: _, h => by simp [checkArgs] at h
  | [], _ :: _, h => by simp [checkArgs] at h
  | _ :: _, [], h => by simp [checkArgs] at h
end

/-! ## Variable occurrence -/

-- The checker's recursive functions are structural (not well-founded), so
-- that the kernel can evaluate them, e.g. with `decide +kernel`.

mutual
/-- `SExpr.HasVar`, computed. -/
def hasVarB (Γ : Ctx) : SExpr → VarId → Bool
  | .var u, v => match Γ[u]? with
    | some (.bound _) => u == v
    | some (.reg _ vs) => vs.contains v
    | none => false
  | .app _ es, v => hasVarBs Γ es v

def hasVarBs (Γ : Ctx) : List SExpr → VarId → Bool
  | [], _ => false
  | e :: es, v => hasVarB Γ e v || hasVarBs Γ es v
end

mutual
theorem hasVarB_iff (Γ : Ctx) : ∀ (e : SExpr) (v : VarId), hasVarB Γ e v = true ↔ e.HasVar Γ v
  | .var u, v => by
    rw [hasVarB, SExpr.HasVar]
    cases h : Γ[u]? with
    | none => simp
    | some bi => cases bi <;> simp
  | .app t es, v => by
    rw [hasVarB, SExpr.HasVar, hasVarBs_iff]
    simp

theorem hasVarBs_iff (Γ : Ctx) : ∀ (es : List SExpr) (v : VarId),
    hasVarBs Γ es v = true ↔ ∃ e ∈ es, e.HasVar Γ v
  | [], v => by simp [hasVarBs]
  | e :: es, v => by
    rw [hasVarBs, Bool.or_eq_true, hasVarB_iff, hasVarBs_iff]
    simp
end

-- `SExpr.subst`, by structural recursion (`substC_eq`).
mutual
def substC (σ : List SExpr) : SExpr → SExpr
  | .var v => σ.getD v default
  | .app t es => .app t (substCs σ es)

def substCs (σ : List SExpr) : List SExpr → List SExpr
  | [] => []
  | e :: es => substC σ e :: substCs σ es
end

mutual
theorem substC_eq (σ : List SExpr) : ∀ e : SExpr, substC σ e = e.subst σ
  | .var v => by rw [substC, SExpr.subst]
  | .app t es => by rw [substC, SExpr.subst, substCs_eq]

theorem substCs_eq (σ : List SExpr) : ∀ es : List SExpr,
    substCs σ es = es.map fun e => e.subst σ
  | [] => rfl
  | e :: es => by rw [substCs, substC_eq, substCs_eq, List.map_cons]
end

/-! ## Substitutions -/

/-- `SafeSubst`, computed: for each bound position `u` and each position `v`
of the theorem that may not depend on `u`, what `u` is sent to does not
occur in what `v` is sent to. -/
def safeSubstB (Γ args : Ctx) (σ : List SExpr) : Bool :=
  (List.range args.length).all fun u =>
    match args[u]? with
    | some (.bound _) => (List.range args.length).all fun v =>
      hasVarB args (.var v) u ||
        match σ[u]?, σ[v]? with
        | some (.var y), some e2 => !hasVarB Γ e2 y
        | _, _ => true
    | _ => true

theorem safeSubstB_sound {Γ args : Ctx} {σ : List SExpr} (h : safeSubstB Γ args σ = true) :
    SafeSubst Γ args σ := by
  intro u v ⟨s, hu⟩ hv hnot y e2 hy he2 hvar
  have hu' : u < args.length := (List.getElem?_eq_some_iff.1 hu).1
  simp only [safeSubstB, List.all_eq_true, List.mem_range] at h
  have := h u hu'
  rw [hu] at this
  simp only [List.all_eq_true, List.mem_range] at this
  have := this v hv
  rw [hy, he2] at this
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with h1 | h1
  · exact hnot ((hasVarB_iff _ _ _).1 h1)
  · rw [(hasVarB_iff _ _ _).2 hvar] at h1; cases h1

/-- The dummies `zs` are bound variables of the given sorts `ys`. -/
def dummiesB (Γ : Ctx) : List SortId → List VarId → Bool
  | [], [] => true
  | y :: ys, z :: zs => (Γ[z]? == some (.bound y)) && dummiesB Γ ys zs
  | _, _ => false

theorem dummiesB_sound {Γ : Ctx} : ∀ {ys zs}, dummiesB Γ ys zs = true →
    Forall₂ (fun y z => Γ[z]? = some (Binder.bound y)) ys zs
  | [], [], _ => .nil
  | y :: ys, z :: zs, h => by
    simp only [dummiesB, Bool.and_eq_true, beq_iff_eq] at h
    exact .cons h.1 (dummiesB_sound h.2)
  | [], _ :: _, h | _ :: _, [], h => by simp [dummiesB] at h

/-! ## Conversion -/

/-- Conversion proofs (`mm0.mm0`'s `CExpr`). In `cong`, a bound argument is
given as `refl (.var v)`. -/
inductive ConvPf
  | refl (e : SExpr)
  | symm (c : ConvPf)
  | trans (c₁ c₂ : ConvPf)
  | cong (t : TermId) (cs : List ConvPf)
  | unfold (t : TermId) (es : List SExpr) (zs : List VarId)

mutual
/-- The conversion a proof proves: `some (e₁, e₂, s)` for `e₁ ≡ e₂ : s`. -/
def checkConv (E : Env) (Γ : Ctx) : ConvPf → Option (SExpr × SExpr × SortId)
  | .refl e => (infer E Γ e).map fun s => (e, e, s)
  | .symm c => (checkConv E Γ c).map fun (a, b, s) => (b, a, s)
  | .trans c₁ c₂ => match checkConv E Γ c₁, checkConv E Γ c₂ with
    | some (a, b, s), some (b', c, s') => if b = b' ∧ s = s' then some (a, c, s) else none
    | _, _ => none
  | .cong t cs => match findTerm E t with
    | some (args, ret, _) => match checkCongArgs E Γ cs args with
      | some (es₁, es₂) => some (.app t es₁, .app t es₂, ret.1)
      | none => none
    | none => none
  | .unfold t es zs => match findTerm E t with
    | some (args, ret, some (ys, val)) =>
      if checkArgs E Γ es args && dummiesB Γ ys zs && decide zs.Nodup &&
          es.all (fun e => zs.all fun z => !hasVarB Γ e z) then
        some (.app t es, substC (es ++ zs.map .var) val, ret.1)
      else none
    | _ => none

/-- The arguments of a `cong` step. -/
def checkCongArgs (E : Env) (Γ : Ctx) :
    List ConvPf → List Binder → Option (List SExpr × List SExpr)
  | [], [] => some ([], [])
  | .refl (.var v) :: cs, .bound s :: bis =>
    if Γ[v]? = some (.bound s) then
      (checkCongArgs E Γ cs bis).map fun (l₁, l₂) => (.var v :: l₁, .var v :: l₂)
    else none
  | c :: cs, .reg s _ :: bis => match checkConv E Γ c, checkCongArgs E Γ cs bis with
    | some (a, b, s'), some (l₁, l₂) => if s' = s then some (a :: l₁, b :: l₂) else none
    | _, _ => none
  | _, _ => none
end

mutual
theorem checkConv_sound {E : Env} {Γ : Ctx} :
    ∀ {c a b s}, checkConv E Γ c = some (a, b, s) → Conv E Γ a b s
  | .refl e, a, b, s, h => by
    simp only [checkConv, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨s', hs, rfl, rfl, rfl⟩ := h
    exact .refl (infer_sound hs)
  | .symm c, a, b, s, h => by
    simp only [checkConv, Option.map_eq_some_iff] at h
    obtain ⟨⟨a', b', s'⟩, hc, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact .symm (checkConv_sound hc)
  | .trans c₁ c₂, a, b, s, h => by
    simp only [checkConv] at h
    split at h
    · next a' b₁ s₁ b₂ c' s₂ h1 h2 =>
      split at h
      · next he =>
        obtain ⟨rfl, rfl⟩ := he
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .trans (checkConv_sound h1) (checkConv_sound h2)
      · simp at h
    · simp at h
  | .cong t cs, a, b, s, h => by
    simp only [checkConv] at h
    split at h
    · next args ret o hf =>
      split at h
      · next l₁ l₂ hc =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .cong (findTerm_sound hf) (checkCongArgs_sound hc)
      · simp at h
    · simp at h
  | .unfold t es zs, a, b, s, h => by
    simp only [checkConv] at h
    split at h
    · next args ret ys val hf =>
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
          Bool.not_eq_true'] at hc
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rw [substC_eq]
        refine .unfold (findTerm_sound hf) (checkArgs_sound h1) (dummiesB_sound h2) h3 ?_
        intro e he z hz hv
        have := h4 e he z hz
        rw [(hasVarB_iff _ _ _).2 hv] at this; cases this
      · simp at h
    · simp at h

theorem checkCongArgs_sound {E : Env} {Γ : Ctx} :
    ∀ {cs bis l₁ l₂}, checkCongArgs E Γ cs bis = some (l₁, l₂) → ConvArgs E Γ l₁ l₂ bis
  | [], [], l₁, l₂, h => by
    simp only [checkCongArgs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact .nil
  | .refl (.var v) :: cs, .bound s :: bis, l₁, l₂, h => by
    simp only [checkCongArgs] at h
    split at h
    · next hv =>
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨m₁, m₂⟩, hm, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .bound hv (checkCongArgs_sound hm)
    · simp at h
  | c :: cs, .reg s vs :: bis, l₁, l₂, h => by
    simp only [checkCongArgs] at h
    split at h
    · next a b s' m₁ m₂ h1 h2 =>
      split at h
      · next hs =>
        subst hs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .reg (checkConv_sound h1) (checkCongArgs_sound h2)
      · simp at h
    · simp at h
  | .refl (.app _ _) :: _, .bound _ :: _, _, _, h
  | .symm _ :: _, .bound _ :: _, _, _, h
  | .trans _ _ :: _, .bound _ :: _, _, _, h
  | .cong _ _ :: _, .bound _ :: _, _, _, h
  | .unfold _ _ _ :: _, .bound _ :: _, _, _, h
  | [], _ :: _, _, _, h
  | _ :: _, [], _, _, h => by simp [checkCongArgs] at h
end

/-! ## Proofs -/

instance (E : Env) (a h r) : Decidable (E.getThm a h r) := by
  unfold Env.getThm; infer_instance

/-- Proofs (`mm0.mm0`'s `VExpr`): a hypothesis by index, a theorem or axiom
(given by its statement) applied to a substitution and proofs of its
hypotheses, or a conversion. -/
inductive Pf
  | hyp (n : Nat)
  | thm (args : Ctx) (hs : List SExpr) (ret : SExpr) (σ : List SExpr) (ps : List Pf)
  | conv (c : ConvPf) (p : Pf)

mutual
/-- The statement a proof proves, from the hypotheses `hs`. -/
def check (E : Env) (Γ : Ctx) (hs : List SExpr) : Pf → Option SExpr
  | .hyp n => hs[n]?
  | .thm args hs₂ ret σ ps =>
    if decide (E.getThm args hs₂ ret) && checkArgs E Γ σ args && safeSubstB Γ args σ &&
        checkPfs E Γ hs ps (hs₂.map (substC σ)) then
      some (substC σ ret)
    else none
  | .conv c p => match checkConv E Γ c, check E Γ hs p with
    | some (a, b, _), some φ => if φ = a then some b else none
    | _, _ => none

/-- Each proof proves its goal. -/
def checkPfs (E : Env) (Γ : Ctx) (hs : List SExpr) : List Pf → List SExpr → Bool
  | [], [] => true
  | p :: ps, g :: gs => (check E Γ hs p == some g) && checkPfs E Γ hs ps gs
  | _, _ => false
end

mutual
theorem check_sound {E : Env} {Γ : Ctx} {hs : List SExpr} :
    ∀ {p φ}, check E Γ hs p = some φ → Proof E Γ (· ∈ hs) φ
  | .hyp n, φ, h => by
    simp only [check] at h
    exact .hyp (List.mem_of_getElem? h)
  | .thm args hs₂ ret σ ps, φ, h => by
    simp only [check] at h
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
      simp only [Option.some.injEq] at h
      subst h
      rw [substC_eq]
      refine .thm h1 (checkArgs_sound h2) (safeSubstB_sound h3) fun x (hx : x ∈ hs₂) => ?_
      rw [← substC_eq]
      exact checkPfs_sound h4 _ (List.mem_map_of_mem hx)
    · simp at h
  | .conv c p, φ, h => by
    simp only [check] at h
    split at h
    · next a b s ψ h1 h2 =>
      split at h
      · next he =>
        subst he
        simp only [Option.some.injEq] at h
        subst h
        exact .conv (checkConv_sound h1) (check_sound h2)
      · simp at h
    · simp at h

theorem checkPfs_sound {E : Env} {Γ : Ctx} {hs : List SExpr} :
    ∀ {ps gs}, checkPfs E Γ hs ps gs = true → ∀ g ∈ gs, Proof E Γ (· ∈ hs) g
  | [], [], _, g, hg => by simp at hg
  | p :: ps, g' :: gs, h, g, hg => by
    simp only [checkPfs, Bool.and_eq_true, beq_iff_eq] at h
    rcases List.mem_cons.1 hg with rfl | hg
    · exact check_sound h.1
    · exact checkPfs_sound h.2 g hg
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => by simp [checkPfs] at h
end

/-! ## Contexts -/

/-- A binder may be added to the context `pre`: a bound variable's sort is
declared and not `strict`; a regular variable's sort is declared and it
depends only on bound variables of `pre`. -/
def binderOkB (E : Env) (pre : Ctx) : Binder → Bool
  | .bound s => E.any fun
    | .sort s' sd => s' == s && !sd.strict
    | _ => false
  | .reg s vs => (E.any fun
      | .sort s' _ => s' == s
      | _ => false) &&
    vs.all fun x => match pre[x]? with
      | some (.bound _) => true
      | _ => false

/-- `Ctx.Ok`, computed binder by binder. -/
def ctxOkGo (E : Env) (pre : Ctx) : Ctx → Bool
  | [] => true
  | b :: bs => binderOkB E pre b && ctxOkGo E (pre ++ [b]) bs

theorem ctxOkGo_sound {E : Env} : ∀ {pre bs : Ctx}, ctxOkGo E pre bs = true →
    Ctx.Ok E pre → Ctx.Ok E (pre ++ bs)
  | pre, [], _, h => by simpa using h
  | pre, b :: bs, hg, h => by
    simp only [ctxOkGo, Bool.and_eq_true] at hg
    have : Ctx.Ok E (pre ++ [b]) := by
      cases b with
      | bound s =>
        have := hg.1
        simp only [binderOkB, List.any_eq_true] at this
        obtain ⟨d, hd, hds⟩ := this
        match d with
        | .sort s' sd =>
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hds
          obtain ⟨rfl, hs⟩ := hds
          exact .bound hd hs h
        | .term .. | .defn .. | .ax .. | .thm .. => simp at hds
      | reg s vs =>
        have := hg.1
        simp only [binderOkB, Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at this
        obtain ⟨⟨d, hd, hds⟩, hvs⟩ := this
        refine .reg ⟨?_, fun x hx => ?_⟩ h
        · match d with
          | .sort s' sd =>
            simp only [beq_iff_eq] at hds; subst hds; exact ⟨sd, hd⟩
          | .term .. | .defn .. | .ax .. | .thm .. => simp at hds
        · have := hvs x hx
          split at this
          · next s' h' => exact ⟨s', h'⟩
          · cases this
    have := ctxOkGo_sound hg.2 this
    simpa using this

def ctxOkB (E : Env) (Γ : Ctx) : Bool := ctxOkGo E [] Γ

theorem ctxOkB_sound {E : Env} {Γ : Ctx} (h : ctxOkB E Γ = true) : Ctx.Ok E Γ := by
  simpa using ctxOkGo_sound h .nil

/-! ## Proof files -/

/-- A certificate for a theorem of the proof file: its dummies and a proof. -/
structure ThmCert where
  ds : List SortId
  pf : Pf

/-- What a declaration of the proof file needs, given the declarations before
it: nothing for sorts, terms and axioms; a body for definitions; a checked
proof for theorems. -/
def declProofB (pre : Env) : Decl → Option ThmCert → Bool
  | .sort .., _ | .term .., _ | .ax .., _ => true
  | .defn _ _ _ (some _), _ => true
  | .defn _ _ _ none, _ => false
  | .thm a hs r, some c =>
    ctxOkB pre (appendDummies a c.ds) && check pre (appendDummies a c.ds) hs c.pf == some r
  | .thm .., none => false

/-- `Env.Proof'`, computed declaration by declaration. -/
def proofGo (pre : Env) : List Decl → List (Option ThmCert) → Bool
  | [], [] => true
  | d :: ds, c :: cs => declProofB pre d c && proofGo (pre ++ [d]) ds cs
  | _, _ => false

theorem proofGo_sound : ∀ {pre ds : Env} {cs}, proofGo pre ds cs = true →
    Env.Proof' pre → Env.Proof' (pre ++ ds)
  | pre, [], [], _, h => by simpa using h
  | pre, d :: ds, c :: cs, hg, h => by
    simp only [proofGo, Bool.and_eq_true] at hg
    have : Env.Proof' (pre ++ [d]) := by
      match d, c, hg.1 with
      | .sort .., _, _ => exact .sort h
      | .term .., _, _ => exact .term h
      | .ax .., _, _ => exact .ax h
      | .defn _ _ _ (some _), _, _ => exact .defn h
      | .thm a hs r, some ⟨ds', pf⟩, hd =>
        simp only [declProofB, Bool.and_eq_true, beq_iff_eq] at hd
        exact .thm (ctxOkB_sound hd.1) (check_sound hd.2) h
    simpa using proofGo_sound hg.2 this
  | _, [], _ :: _, hg, _ | _, _ :: _, [], hg, _ => by simp [proofGo] at hg

/-- How each declaration of the proof file relates to the `.mm0` file: it is
the next declaration of the `.mm0` file (`keep`), an extra definition or
theorem (`skip`), or the body of the next abstract `def` (`define`). -/
inductive Tag
  | keep
  | skip
  | define

/-- `Env.Extend`, computed: the `.mm0` declarations `E₁` against the proof
file's `E₂`, following the tags. -/
def extendGo : Env → Env → List Tag → Bool
  | [], [], [] => true
  | d :: E₁, d' :: E₂, .keep :: ts => d == d' && extendGo E₁ E₂ ts
  | E₁, .defn .. :: E₂, .skip :: ts => extendGo E₁ E₂ ts
  | E₁, .thm .. :: E₂, .skip :: ts => extendGo E₁ E₂ ts
  | .defn i a r none :: E₁, .defn i' a' r' _ :: E₂, .define :: ts =>
    i == i' && a == a' && r == r' && extendGo E₁ E₂ ts
  | _, _, _ => false

theorem extendGo_sound {E₁ E₂ : Env} {ts : List Tag} (hg : extendGo E₁ E₂ ts = true) :
    ∀ {P₁ P₂ : Env}, Env.Extend P₁ P₂ → Env.Extend (P₁ ++ E₁) (P₂ ++ E₂) := by
  fun_induction extendGo E₁ E₂ ts with
  | case1 => intro P₁ P₂ h; simpa using h
  | case2 d E₁ d' E₂ ts ih =>
    intro P₁ P₂ h
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    obtain ⟨rfl, hg⟩ := hg
    simpa using ih hg (Env.Extend.keep h)
  | case3 E₁ i a r o E₂ ts ih =>
    intro P₁ P₂ h
    simpa using ih hg (Env.Extend.defn_skip h)
  | case4 E₁ a hs r E₂ ts ih =>
    intro P₁ P₂ h
    simpa using ih hg (Env.Extend.thm_skip h)
  | case5 i a r E₁ i' a' r' o E₂ ts ih =>
    intro P₁ P₂ h
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hg⟩ := hg
    simpa using ih hg (Env.Extend.defn_def (o := o) h)
  | case6 => simp at hg

/-! ## `check_sound` -/

/-- Check a proof file `E'` (with tags and certificates) against the `.mm0`
file `E`. -/
def checkFile (E E' : Env) (tags : List Tag) (certs : List (Option ThmCert)) : Bool :=
  extendGo E E' tags && proofGo [] E' certs

/-- **`check_sound`**: if the checker accepts a proof file, the `.mm0` file is
proved. -/
theorem checkFile_sound {E E' : Env} {tags certs} (h : checkFile E E' tags certs = true) :
    E.Proof := by
  simp only [checkFile, Bool.and_eq_true] at h
  exact ⟨E', by simpa using extendGo_sound h.1 Env.Extend.nil,
    by simpa using proofGo_sound h.2 .nil⟩

end MM0.Check
