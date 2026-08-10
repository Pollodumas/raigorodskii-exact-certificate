import RaigorodskiiCertificate

set_option autoImplicit false

namespace Raigorodskii

open Polynomial

noncomputable section

lemma RZ_monic_verified : RZ.Monic := by
  norm_num [RZ]

lemma RZ_aeval_relation_verified (x : ℝ) :
    aeval (6 * x) RZ = 324 * Q x := by
  simp [RZ, Q, aeval_def]
  ring

theorem six_mul_gamma_isIntegral_verified : IsIntegral ℤ (6 * gamma) := by
  refine ⟨RZ, RZ_monic_verified, ?_⟩
  rw [RZ_aeval_relation_verified, Q_gamma, mul_zero]

end
end Raigorodskii
