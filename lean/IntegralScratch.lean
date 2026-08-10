import Mathlib

set_option autoImplicit false

namespace IntegralScratch

open Polynomial

noncomputable section

def Q (x : ℝ) : ℝ :=
  144 * x ^ 6 - 528 * x ^ 5 + 648 * x ^ 4 - 220 * x ^ 3
    - 71 * x ^ 2 + 42 * x - 31

def RZ : Polynomial ℤ :=
  X ^ 6 - C 22 * X ^ 5 + C 162 * X ^ 4 - C 330 * X ^ 3
    - C 639 * X ^ 2 + C 2268 * X - C 10044

lemma RZ_monic : RZ.Monic := by
  unfold RZ
  monicity <;> norm_num

lemma RZ_eval_identity (x : ℝ) :
    eval₂ (algebraMap ℤ ℝ) (6 * x) RZ = 324 * Q x := by
  simp [RZ, Q]
  ring

theorem six_mul_isIntegral_of_Q_root (gamma : ℝ) (hQ : Q gamma = 0) :
    IsIntegral ℤ (6 * gamma) := by
  refine ⟨RZ, RZ_monic, ?_⟩
  rw [RZ_eval_identity, hQ]
  norm_num

end
end IntegralScratch
