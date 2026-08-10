import Mathlib

set_option autoImplicit false

namespace IrreducibleScratch

open Polynomial

abbrev F5 := ZMod 5

def q5 : Polynomial F5 :=
  X ^ 6 + C 3 * X ^ 5 + C 2 * X ^ 4 + X ^ 2 + C 3 * X + C 1

example : Irreducible q5 := by
  native_decide

end IrreducibleScratch
