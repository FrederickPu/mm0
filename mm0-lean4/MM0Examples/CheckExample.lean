import MM0.Check
import MM0Examples.SetEnv

/-!
# The verified checker on a small proof

`a1i` from `examples/set.mm0` (`$ ph $ > $ ps -> ph $`), proved by `ax_mp`
applied to the hypothesis and `ax_1`, as a `Pf` written by hand. The kernel
runs the checker (`decide +kernel`), and `check_sound` turns its answer into
a `Proof`.
-/

namespace MM0.CheckExample

open MM0.Check

def a1iPf : Pf :=
  .thm [(.reg 0 []), (.reg 0 [])] [(.var 0), (.app 0 [(.var 0), (.var 1)])] (.var 1)
    [(.var 0), (.app 0 [(.var 1), (.var 0)])]
    [.hyp 0,
     .thm [(.reg 0 []), (.reg 0 [])] [] (.app 0 [(.var 0), (.app 0 [(.var 1), (.var 0)])])
       [(.var 0), (.var 1)] []]

example : Proof setEnv [(.reg 0 []), (.reg 0 [])] (· ∈ [(.var 0)]) (.app 0 [(.var 1), (.var 0)]) :=
  check_sound (p := a1iPf) (by decide +kernel)

end MM0.CheckExample
