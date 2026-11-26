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

**Approach: encode T into con-leche and reuse its soundness proof.** con-leche already
gives its deductive system a model (`PConst` and so on as the base, with a shallow
interpretation of `Expr`) and proves the system sound in it. T is meant to be the same
deductive system written in MM0. So (S) needs no new model. Map every T derivation to a
con-leche derivation, then apply con-leche's soundness theorem. All the semantic work stays
in con-leche.

```
enc : MM0 expr/level/ctx (named variables) → con-leche Expr/Level/context (de Bruijn)

theorem T_to_conleche : Derivable T ⟦G |- e : A⟧ → ConLeche.HasType (enc G) (enc e) (enc A)
-- likewise ⟦G |= a = b⟧; then compose with con-leche's soundness theorem
```

The encoding always goes **from T into con-leche**. (S) never runs `tr` (the con-leche → T
translation in (A)) backwards.

1. **The encoding `enc`.** Read each MM0 expression as a con-leche `Expr`:
   - `Sort u ↦ .sort (enc u)`, `app ↦ .app`, `Pi`/`lambda {x} t e ↦ .forallE`/`.lam`,
     with the named bound variable `x` turned into a de Bruijn index.
   - `ctx ↦` con-leche context: `nil ↦ []`, `G, x : t ↦ enc t :: enc G`.
   - Lemmas: `enc` commutes with MM0 substitution (`subst:`, `l_subst:`, `substIS:`)
     against con-leche's `inst`/`liftN`, and respects MM0 dependency sets (no variable
     capture).
2. **Generic MM0 layer** (independent of Lean). MM0's own proof rules (instantiating a
   theorem, `conv`, definition unfolding) are preserved: if every axiom of an environment
   holds in the target system under `enc`, every theorem derivable from it does too.
   This is induction on MM0 derivations and is routine.
3. **One case per axiom of T** (~200 for `lean.mm1`). Each one is a con-leche rule, a
   derived rule, or one of the exceptions below. Most are short adapter lemmas.

**Exceptions: rules of T with no con-leche rule to land on.**
- `conv_trans`: con-leche's `DefEq` deliberately has no transitivity. Encode
  `G |= a = b` into the equality judgment con-leche's soundness theorem *produces*
  (the semantic equality of the interpretations, or the transitive closure of `DefEq`),
  not into `DefEq` itself. Transitivity then holds for free.
- `l_pl_cases` (level case-splitting): prove it in con-leche's level semantics.
- The anonymous `Ind t F K` and its rules (`ty_Ind`, `ty_Ctor`, `ty_Rec`, `conv_iota`,
  `LE_*`): need `Ind` to encode into con-leche's named inductive declarations. This is the
  largest exception. If it doesn't encode cleanly, change T to match con-leche (see the
  table below).

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
| `conv_trans` | an axiom | `DefEq` deliberately has no transitivity | Harmless if `G \|= a = b` encodes into con-leche's semantic equality, not `DefEq` (see (S)). (A) doesn't need it |
| Axioms | `quot`, `propext`, `choice` | the same three standard axioms | Matches |
| Level reasoning | complete case-splitting procedure (`l_pl_cases`) | a level oracle (`LevelOracle`) | Check that the oracle's verdicts are derivable in T, as part of (A) |

## Milestones

### M0: Set up
- [x] Lean 4 package on `leanprover/lean4:v4.36.0`, with `require` on con-leche (no transitive dependencies). Done: `mm0-lean4/` (MM0 itself, no dependencies) and `mm0-sanity/` (the con-leche part; requires `mm0-lean4` and con-leche, pinned at `bc66761`).
- [ ] Vendor `lean.mm1` and split it into `lean.mm0` (the statements we trust) and `lean.mm1` (proofs).
- [ ] Build `lean.mmb` with `mm0-rs`; CI also runs `mm0-c` on it.

### M1: MM0 in Lean 4
- [x] Port `mm0-lean/mm0/mm0.lean` (`mm0-lean4/MM0/Spec.lean`): sorts with modifiers, terms, defs with unfolding, axioms, theorems, bound vs regular variables, dependency sets, `Derivable`.
- [ ] Cross-check it rule by rule against `examples/mm0.mm0`. Found so far: `DefOk` in
      `mm0.mm0` (and the Lean 3 port) lets free variables of `free` sorts escape a definition,
      while mm0-c forbids dummies of `free` sorts and requires every free variable to be in the
      return dependencies. Decide which one T's soundness proof uses.
- [x] `.mm0` parser in Lean, so `T : MM0.Env` is produced from the file
      (`mm0-lean4/MM0/Parse.lean`). Agrees with mm0-rs on all of `examples/*.mm0` and
      `tests/mm0_mmu`, except where it follows `mm0.md`/mm0-c on purpose.
- [x] Regression and differential fuzz tests against mm0-rs and mm0-c
      (`mm0-lean4/tests/run.sh`, `mm0-lean4/Fuzz.lean`). Known differences, including
      apparent mm0-rs/mm0-c bugs, are listed in `mm0-lean4/README.md`.
- [ ] Not yet proved: that the parser's output satisfies `Env.Ok`. Today the parser is tested,
      not verified.
- [ ] (Optional) `.mmb` checker, porting `mm0b.lean`, with `check_sound`.

### M2: The encoding and the generic layer
- [x] Generic MM0 soundness (`mm0-lean4/MM0/Model.lean`, `MM0/Sound.lean`, no `sorry`):
      `Env.Proof'.sound` says every theorem of a well-formed, proved environment is valid in
      every model of it (`Model.Of`: agrees with the binders, satisfies `Frame`, interprets
      definitions by their bodies, satisfies the axioms). Variables are read nominally
      (expressions denote functions of a valuation of names), as in `model.lean`.
- [x] Fixing the spec so the theorem holds. `mm0.mm0` (and the Lean 3 port) checks a theorem
      instantiation's side conditions against the proof's context instead of the theorem's
      binders, and does not require the dummies of an unfolded definition to be distinct. The
      Lean 3 port also drops their freshness. `MM0/Spec.lean` uses the versions mm0-c enforces;
      its module docs list each change. Report these upstream.
- [x] Sanity instance (`mm0-lean4/MM0Examples/SetModel.lean`): `examples/set.mm0`, as
      produced by the parser, has a model in any model of ZFC (`model_of`). Every axiom and
      definition is checked. This caught a flaw in the first version of the semantics (no sort
      carriers, so bound variables could take junk values and `ax_12` failed). The fix follows
      the Lean 3 `model.lean`, ported faithfully in `MM0/Lean3Model.lean`.
- [x] Port `mm0-lean/mm0/mm0b.lean` (`.mmb` semantics): `mm0-lean4/MM0/Lean3MMB.lean`. The
      Lean 3 file proves nothing and has an empty `initial_state`. The port keeps that, and a
      typo (its `unfold` rule is stated for the `cong` command).
- [x] `check_sound`, verified core (`mm0-lean4/MM0/Check.lean`): `checkFile_sound` says that if
      the checker accepts a proof file (declarations, keep/skip/define tags against the `.mm0`
      file, and a proof term per theorem), then `Env.Proof` holds. The checker is structurally
      recursive, so the kernel can run it (`MM0Examples/CheckExample.lean`).
- [ ] `.mmb` reader: turn an `.mmb` file into the checker's input. Unverified by design: a
      wrong reading is rejected by the checker. Then the theorems of a `.mm0` file follow from
      running the checker on its `.mmb`, so that
      `set_sound` can take its
      `Env.Proof'` from a checked `set.mmb` instead of as a hypothesis.
- [ ] `enc` from T's `level`/`expr`/`ctx` into the Fragment's `Level`/`Expr`/contexts, or a
      `Model` built from con-leche's set-theoretic interpretation (see M3).

### M3: (S) for the part without inductives
- [ ] One case per axiom: substitution, typing, conversion, `let`/ζ, proof irrelevance, η,
      each mapped to a Fragment rule or derived rule.
- [ ] Exceptions: `conv_trans` (via the semantic equality judgment) and `l_pl_cases`.
- [ ] Corollary, via the Fragment's `model_exists`: consistency of the part of T without inductives.

### M4: Extend T, then (S) for all of it
- [ ] Add the `env` sort, named constants, δ, and universe-level instantiation to T.
- [ ] Encode `Ind`/`Ctor`/`Rec` into con-leche's inductive declarations; map `ty_Ind`,
      `ty_Ctor`, `ty_Rec`, `conv_iota`, `LE_*`, and `quot`/`propext`/`choice`.
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

- **Translating bound variables (S and A).** Named variables with dependency sets on the MM0
  side, de Bruijn indices on con-leche's. `enc` (S) and `tr` (A) face the same problem in
  opposite directions. Keep both in one module with a small interface.
- **`Ind` not matching con-leche's inductives (S).** If T's anonymous `Ind` doesn't encode
  into con-leche's named inductives, the reuse breaks for the inductive axioms. Settle this
  early, changing T if needed, rather than proving those axioms semantically from scratch.
- **Lean copy and `.mm0` file drifting apart.** Prevented by producing `T` with the parser
  (M1) and checking in CI.
- **Efficient arithmetic in MM0.** Native `Nat` computation in con-leche will need an
  efficient representation in T (cf. `examples/peano_hex.mm0`) to keep the final MM0 proofs
  small.
- **Upstream drift.** con-leche changes quickly. Pin a commit and update deliberately.
