import MM0.Spec
import MM0.Parse
import MM0.Lean3Model
import MM0.Lean3MMB
import MM0.Model
import MM0.Sound

/-!
# MM0 in Lean 4

Root of the `MM0` library: Metamath Zero formalized in Lean 4, independent
of con-leche so that it can be mainlined.

* `MM0.Spec`: what an MM0 environment is, when it is well formed, and what
  is derivable in it (a port of `mm0-lean/mm0/mm0.lean`).
* `MM0.Parse`: the `.mm0` parser and elaborator, which turns the bytes of a
  `.mm0` file into an `MM0.Env`.
* `MM0.Lean3Model`, `MM0.Lean3MMB`: faithful ports of the Lean 3
  `mm0-lean/mm0/model.lean` and `mm0b.lean`, both unfinished there.
* `MM0.Model`: models of MM0 (a meaning for each term, read nominally) and
  what it means for a model to satisfy an environment.
* `MM0.Sound`: soundness. In a well-formed environment whose theorems all
  have proofs, every theorem is valid in every model (`Env.Proof'.sound`).
-/
