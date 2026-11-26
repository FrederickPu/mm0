import MM0Sanity.ConLeche
import MM0Sanity.T

/-!
# The con-leche sanity check

Root of the `MM0Sanity` library, the con-leche half of Plan.md. It will prove
that T, the Lean type theory written in MM0, is sound for con-leche's model,
and so consistent. The MM0 side it builds on is the `MM0` library in
`../mm0-lean4`.

* `MM0Sanity.T`: T itself, `MM0.T : MM0.Env`, the parser's output for
  `T/lean.mm0` (generated from `examples/lean.mm1` by `mm0-lean genmm0`).
* `MM0Sanity.ConLeche`: checks that the pinned con-leche Fragment builds and
  is importable.
-/
