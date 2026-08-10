import Mathlib

set_option autoImplicit false

namespace IrreducibilityScratch

open Polynomial

noncomputable section

def QZ : Polynomial ℤ :=
  C 144 * X ^ 6 - C 528 * X ^ 5 + C 648 * X ^ 4
    - C 220 * X ^ 3 - C 71 * X ^ 2 + C 42 * X - C 31

def QQ : Polynomial ℚ := QZ.map (Int.castRingHom ℚ)

example : Irreducible QQ := by
  native_decide

end
end IrreducibilityScratch
