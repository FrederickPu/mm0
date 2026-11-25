# Plan: an MM0 sanity check for a Lean-in-MM0 formalism

## Goal

The end goal is to port con-leche (https://github.com/leanprover/con-leche) so that its
consistency is fully verified in Metamath Zero (MM0). The MM0 side starts from a multi-sorted
theory **T** of Lean's typing rules (sorts for expressions, universe levels, contexts, …).

Before transpiling anything, we want evidence that **T** is the right theory. The sanity check:

> Implement MM0 in Lean 4, and prove in Lean that **T**, as written in its `.mm0` file,
> (S) is sound for con-leche's set-theoretic model, and therefore consistent, and
> (A) is adequate: it derives everything con-leche's checker accepts.

(S) without (A) is not enough. A theory that is too weak is also consistent, and then the
ported checker would get stuck. (A) without (S) is not enough either, because a theory that
is too strong could be inconsistent.

## What already exists

| Asset | Where | Use |
|---|---|---|
| Lean type theory written in MM0: sorts `level`, `expr`, `ctx`, `indspec`, `cidx`; judgments `G \|- e : A`, `G \|= a = b`; explicit substitution; level arithmetic; inductives via `Ind`/`Ctor`/`Rec`; `quot`, `propext`, `choice` | `digama0/mm0` `examples/lean.mm1` (774 lines) | Starting point for **T** |
| MM0 spec written in MM0 | `examples/mm0.mm0` | Reference to check the Lean spec against |
| Lean 3 spec of MM0 derivability | `mm0-lean/mm0/mm0.lean` | Port to Lean 4 |
| Lean 3 model theory for MM0 (unfinished; valuations and the variables each expression depends on) | `mm0-lean/mm0/model.lean` | Template for the generic soundness theorem |
| Lean 3 semantics of the `.mmb` binary format | `mm0-lean/mm0/mm0b.lean` | Template for an optional checker |
| MM0 soundness for the set.mm axioms (unfinished) | `mm0-lean/mm0/fol.lean` | Example of an end-to-end soundness proof |
| con-leche: verified Lean checker with a set-theoretic model. No dependencies, Lean `v4.36.0` | `leanprover/con-leche` | Semantic target for (S) and rule target for (A) |
| Self-contained version of con-leche (no literals, projections or structure eta; ~35k lines; has its own `model_exists`) | `con-leche/whitepaper/Fragment/` | First, smaller target |
| Set-theory interface: `lam`, `pi`, `app`, `univ`, `pt`, quotients, `schoice`, … | `con-leche/ConLeche/SetTheory/` | Building blocks for the model |

## Theorems to prove

### (S) Soundness and consistency

```
theorem T_sound  {V} [SetTheory V] : Derivable T J → Holds V J
theorem T_consistent {V} [SetTheory V] : ¬ Derivable T ⟦nil |- p : False⟧
```

Prove it in two layers.

1. **Generic MM0 soundness** (independent of Lean).
   - An MM0 model gives each sort a carrier set and each term constructor a function.
   - An expression is read under a valuation of its variables.
   - Regular variables may depend only on the variables listed in their dependency sets.
   - Theorem: if a model satisfies every axiom of an environment, it satisfies every theorem
     derivable from it.
2. **The Lean model.** Interpret T directly in con-leche's `SetTheory V`, with no syntax in
   between:
   - `level` ↦ `ℕ`, given values for the level variables; `l_S`, `l_max`, `l_imax` as usual.
   - `expr` ↦ `V`, with `Sort u ↦ univ u`, `app ↦ SetTheory.app`,
     `lambda {x} t e ↦ SetTheory.lam ⟦t⟧ (fun x => ⟦e⟧)`, `Pi ↦ SetTheory.pi`.
   - `ctx` ↦ a condition on variable assignments: `nil ↦ True`, and `G, x : t` holds when
     G holds and `ρ x ∈ ⟦t⟧ ρ`.
   - `G |- e : A` ↦ for every assignment ρ satisfying G, `⟦e⟧ρ ∈ ⟦A⟧ρ`.
   - `G |= a = b` ↦ for every assignment ρ satisfying G, `⟦a⟧ρ = ⟦b⟧ρ`.
   - Substitution predicates (`subst:`, `l_subst:`, `substIS:`) ↦ semantic equality with the
     updated assignment.

   Reading T semantically means (S) never needs a translation between de Bruijn and named
   variables.

   Then prove each axiom of T valid, one lemma per axiom (~200 for `lean.mm1`):
   - The structural, conversion, proof-irrelevance, eta, `quot`, `propext` and `choice`
     axioms should follow quickly from con-leche's `SetTheory` lemmas.
   - The inductive axioms (`ty_Ind`, `ty_Ctor`, `ty_Rec`, `conv_iota`, and the `LE_*`
     large-elimination rules) are the bulk. Borrow from con-leche's inductive model
     constructions (`whitepaper/Fragment/LfpSet.lean`, `IndSem.lean`, `IndRec.lean`).

The consistency is **relative** to con-leche's `SetTheory` class, which is essentially
Tarski–Grothendieck set theory. That is the same assumption con-leche itself rests on.

### (A) Adequacy, which shows the port is possible

```
theorem T_adequate : Fragment.Infer env Γ e A → Derivable T ⟦tr Γ |- tr e : tr A⟧
-- likewise for Red, DefEq and DefEqIn; then for ConLeche/Rules/Rel.lean
```

- Needs a translation `tr` from con-leche's de Bruijn `Expr` to MM0 expressions with named
  bound variables. This includes choosing fresh names and proving that translation commutes
  with `liftN`/`inst` and with MM0 substitution. This is the main technical pain point.
- The proof is a set of derived rules in T, one per con-leche rule constructor. These derived
  rules are exactly the proof-producing step the ported checker needs, so the work carries over.
- Rules con-leche has that T lacks show up here as unprovable cases. That list says what T
  needs to gain.

### Tying the Lean statements to the real file

Neither (S) nor (A) needs an MM0 verifier to *run*, because both quantify over all
derivations. The Lean MM0 implementation exists so that the `T` in the theorems is provably
the bytes of the `.mm0` file, not a hand-written copy of it:

```
def T : MM0.Env := parseMM0! "lean.mm0"          -- produced by the parser, not hand-written
theorem check_sound : checkMMB T bytes = .ok → ∀ φ ∈ theorems bytes, Derivable T φ  -- optional
```

## Where `lean.mm1` doesn't match con-leche (settle before transpiling)

| Topic | `lean.mm1` | con-leche | Decision needed |
|---|---|---|---|
| Constants | none; everything is inline MM0 `def`s | environment of named, universe-polymorphic constants, with δ-unfolding | Add an `env` sort with lookup. The environment must be **data inside the logic**, not new MM0 axioms per declaration, or the final MM0 theorem cannot quantify over all inputs |
| Inductives | anonymous single inductive `Ind t F K` (indices allowed through `F`) | named, mutual and nested inductives via a positivity analysis | Add mutual and nested inductives, or an encoding that matches con-leche's uniform fixpoint approach |
| Projections and structure eta | absent | present | Add them |
| Nat/String literals and accelerated arithmetic | absent (`nat` is an `Ind`) | literals, with `Nat` operations computed natively | Add literals plus computation rules. The arithmetic proofs in MM0 must stay efficient |
| Theorem bodies | n/a | opaque, plus a K-like hack for `And` | Model the opacity; decide whether the `And` hack is part of T |
| `conv_trans` | an axiom | `DefEq` deliberately has no transitivity | Harmless: the model satisfies it for (S), and (A) doesn't need it |
| Axioms | `quot`, `propext`, `choice` | the same three standard axioms | Matches |
| Level reasoning | complete case-splitting procedure (`l_pl_cases`) | a level oracle (`LevelOracle`) | Check that the oracle's verdicts are derivable in T, as part of (A) |

## Milestones

### M0: Set up
- [ ] Lean 4 package on `leanprover/lean4:v4.36.0`, with `require` on con-leche (no transitive dependencies).
- [ ] Vendor `lean.mm1` and split it into `lean.mm0` (the statements we trust) and `lean.mm1` (proofs).
- [ ] Build `lean.mmb` with `mm0-rs`; CI also runs `mm0-c` on it.

### M1: MM0 in Lean 4
- [ ] Port `mm0-lean/mm0/mm0.lean`: sorts with modifiers, terms, defs with unfolding, axioms, theorems, bound vs regular variables, dependency sets, `Derivable`.
- [ ] Cross-check it rule by rule against `examples/mm0.mm0`.
- [ ] `.mm0` parser in Lean, so `T : MM0.Env` is produced from the file. Test it on `examples/*.mm0`.
- [ ] (Optional) `.mmb` checker, porting `mm0b.lean`, with `check_sound`.

### M2: Generic MM0 model soundness
- [ ] Define MM0 models (modernizing `model.lean`).
- [ ] Prove `sound : Model.satisfiesAxioms M E → Derivable E φ → M ⊨ φ`.
- [ ] Sanity instance: a small toy theory (e.g. `examples/peano.mm0`).

### M3: (S) for the part without inductives
- [ ] Interpret `level`, `expr` and `ctx` in `Fragment`'s `SetTheory V` model.
- [ ] Prove validity of the substitution, typing, conversion, `let`/ζ, proof-irrelevance and η axioms.
- [ ] Corollary: consistency of the part of T without inductives.

### M4: Extend T, then (S) for all of it
- [ ] Add the `env` sort, named constants, δ, and universe-level instantiation to T.
- [ ] Prove validity of the inductive axioms and of `quot`/`propext`/`choice`.
- [ ] `T_consistent`.

### M5: (A) against the Fragment
- [ ] `tr` and its substitution lemmas.
- [ ] Derived rules in T for each constructor of `Red`/`DefEq`/`DefEqIn`/`Infer`.
- [ ] `T_adequate` for the Fragment.

### M6: Scale to full con-leche
- [ ] Literals, projections, structure eta, nested inductives, the `And` hack.
- [ ] (S) and (A) against `ConLeche/Rules/Rel.lean` and `ConLeche.Denotes`.
- [ ] Freeze `lean.mm0`. This is the point to start transpiling.

## Risks

- **Translating bound variables (A).** Named variables with dependency sets on the MM0 side,
  de Bruijn indices on con-leche's. Keep `tr` in one module with a small interface.
- **Proof size of the inductive axioms (S).** This is the largest part of con-leche's own
  proof. Reuse its definitions rather than re-deriving them.
- **Lean copy and `.mm0` file drifting apart.** Prevented by producing `T` with the parser
  (M1) and checking in CI.
- **Efficient arithmetic in MM0.** Native `Nat` computation in con-leche will need an
  efficient representation in T (cf. `examples/peano_hex.mm0`) to keep the final MM0 proofs
  small.
- **Upstream drift.** con-leche changes quickly. Pin a commit and update deliberately.