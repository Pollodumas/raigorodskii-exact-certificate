import Mathlib

set_option autoImplicit false

namespace IrreducibilityQZLiftScratch

open Polynomial

noncomputable section

def QZ : Polynomial ℤ :=
  C 144 * X ^ 6 - C 528 * X ^ 5 + C 648 * X ^ 4
    - C 220 * X ^ 3 - C 71 * X ^ 2 + C 42 * X - C 31

def Q5 : Polynomial (ZMod 5) :=
  QZ.map (Int.castRingHom (ZMod 5))

def QQ : Polynomial ℚ :=
  QZ.map (Int.castRingHom ℚ)

lemma Q5_irreducible : Irreducible Q5 := by
  native_decide

lemma QZ_primitive : QZ.IsPrimitive := by
  native_decide

lemma QZ_irreducible : Irreducible QZ := by
  have hmod : Irreducible (QZ.map (Int.castRingHom (ZMod 5))) := by
    simpa [Q5] using Q5_irreducible
  have hdeg : (QZ.map (Int.castRingHom (ZMod 5))).natDegree = QZ.natDegree := by
    native_decide
  exact?

lemma QQ_irreducible : Irreducible QQ := by
  have hz : Irreducible QZ := QZ_irreducible
  have hp : QZ.IsPrimitive := QZ_primitive
  exact?

end
end IrreducibilityQZLiftScratch
