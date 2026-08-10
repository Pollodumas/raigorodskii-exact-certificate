import Mathlib

set_option autoImplicit false

namespace IrreducibilityMod5Scratch

open Polynomial

noncomputable section

def QZ : Polynomial ℤ :=
  C 144 * X ^ 6 - C 528 * X ^ 5 + C 648 * X ^ 4
    - C 220 * X ^ 3 - C 71 * X ^ 2 + C 42 * X - C 31

def Q5 : Polynomial (ZMod 5) :=
  QZ.map (Int.castRingHom (ZMod 5))

example : Irreducible Q5 := by
  native_decide

end
end IrreducibilityMod5Scratch
