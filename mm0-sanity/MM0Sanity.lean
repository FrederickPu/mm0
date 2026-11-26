import MM0Sanity.ConLeche

/-!
# The con-leche sanity check

Root of the `MM0Sanity` library, the con-leche half of Plan.md. It will prove
that T, the Lean type theory written in MM0 (`examples/lean.mm1`), is sound
for con-leche's model, by encoding T's derivations into con-leche's rules.
The MM0 side it builds on is the `MM0` library in `../mm0-lean4`.

* `MM0Sanity.ConLeche`: checks that the pinned con-leche Fragment builds and
  is importable.
-/
