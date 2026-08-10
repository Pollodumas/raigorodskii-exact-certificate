import Mathlib

set_option autoImplicit false

namespace IrreducibilityLiftScratch

open Polynomial

noncomputable section

def RZ : Polynomial ℤ :=
  X ^ 6 - C 22 * X ^ 5 + C 162 * X ^ 4 - C 330 * X ^ 3
    - C 639 * X ^ 2 + C 2268 * X - C 10044

def R5 : Polynomial (ZMod 5) :=
  RZ.map (Int.castRingHom (ZMod 5))

def RQ : Polynomial ℚ :=
  RZ.map (Int.castRingHom ℚ)

lemma RZ_monic : RZ.Monic := by
  norm_num [RZ]

lemma R5_irreducible : Irreducible R5 := by
  native_decide

lemma RZ_irreducible : Irreducible RZ := by
  have hmod : Irreducible (RZ.map (Int.castRingHom (ZMod 5))) := by
    simpa [R5] using R5_irreducible
  have hdeg : (RZ.map (Int.castRingHom (ZMod 5))).natDegree = RZ.natDegree := by
    native_decide
  exact?

lemma RQ_irreducible : Irreducible RQ := by
  have hz : Irreducible RZ := RZ_irreducible
  have hp : RZ.IsPrimitive := RZ_monic.isPrimitive
  exact?

end
end IrreducibilityLiftScratch
