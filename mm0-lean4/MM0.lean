import MM0.Spec
import MM0.Parse

/-!
# MM0 in Lean 4

Root of the `MM0` library: Metamath Zero formalized in Lean 4, independent
of con-leche so that it can be mainlined.

* `MM0.Spec`: what an MM0 environment is, when it is well formed, and what
  is derivable in it (a port of `mm0-lean/mm0/mm0.lean`).
* `MM0.Parse`: the `.mm0` parser and elaborator, which turns the bytes of a
  `.mm0` file into an `MM0.Env`.

Generic model soundness (Plan.md, M2) will also go here.
-/
