import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace QuadraticDivisorScratch

open Polynomial

noncomputable section

abbrev F5 := ZMod 5
local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

noncomputable def q5 : Polynomial F5 :=
  X ^ 6 + C 3 * X ^ 5 + C 2 * X ^ 4 + X ^ 2 + C 3 * X + C 1

noncomputable def quad (a b : F5) : Polynomial F5 :=
  X ^ 2 + C b * X + C a

lemma q5_monic : q5.Monic := by
  unfold q5
  monicity <;> norm_num

lemma q5_natDegree : q5.natDegree = 6 := by
  unfold q5
  compute_degree! <;> norm_num

lemma q5_ne_zero : q5 ≠ 0 := q5_monic.ne_zero

lemma quad_monic (a b : F5) : (quad a b).Monic := by
  unfold quad
  monicity

lemma quad_natDegree (a b : F5) : (quad a b).natDegree = 2 := by
  unfold quad
  compute_degree!

lemma coeff_quad_mul_zero (a b : F5) (h : Polynomial F5) :
    (quad a b * h).coeff 0 = a * h.coeff 0 := by
  simp [quad, add_mul, mul_assoc]

lemma coeff_quad_mul_one (a b : F5) (h : Polynomial F5) :
    (quad a b * h).coeff 1 = b * h.coeff 0 + a * h.coeff 1 := by
  simp [quad, add_mul, mul_assoc]

lemma coeff_quad_mul_succ2 (a b : F5) (h : Polynomial F5) (n : ℕ) :
    (quad a b * h).coeff (n + 2) =
      h.coeff n + b * h.coeff (n + 1) + a * h.coeff (n + 2) := by
  simp [quad, add_mul, mul_assoc]

lemma quad_not_dvd_q5 (a b : F5) : ¬ quad a b ∣ q5 := by
  rintro ⟨h, hfac⟩
  have hh0 : h ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hfac
    exact q5_ne_zero hfac
  have hdeg : h.natDegree = 4 := by
    have hn := congrArg Polynomial.natDegree hfac
    rw [q5_natDegree, (quad_monic a b).natDegree_mul' hh0, quad_natDegree] at hn
    omega
  have h5 : h.coeff 5 = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    omega
  have h6 : h.coeff 6 = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    omega
  have hc6 := congrArg (fun p : Polynomial F5 => p.coeff 6) hfac
  have hm6 := coeff_quad_mul_succ2 a b h 4
  have h4 : h.coeff 4 = 1 := by
    rw [hm6] at hc6
    simp [q5, coeff_one, h5, h6] at hc6
    exact hc6.symm
  have hc5 := congrArg (fun p : Polynomial F5 => p.coeff 5) hfac
  have hm5 := coeff_quad_mul_succ2 a b h 3
  have h3 : h.coeff 3 = 3 - b := by
    rw [hm5] at hc5
    simp [q5, coeff_one, h4, h5] at hc5
    linear_combination -hc5
  have hc4 := congrArg (fun p : Polynomial F5 => p.coeff 4) hfac
  have hm4 := coeff_quad_mul_succ2 a b h 2
  have h2 : h.coeff 2 = -a + b ^ 2 - 3 * b + 2 := by
    rw [hm4] at hc4
    simp [q5, coeff_one, h3, h4] at hc4
    linear_combination -hc4
  have hc3 := congrArg (fun p : Polynomial F5 => p.coeff 3) hfac
  have hm3 := coeff_quad_mul_succ2 a b h 1
  have h1 : h.coeff 1 =
      2 * a * b - 3 * a - b ^ 3 + 3 * b ^ 2 - 2 * b := by
    rw [hm3] at hc3
    simp [q5, coeff_one, h2, h3] at hc3
    linear_combination -hc3
  have hc2 := congrArg (fun p : Polynomial F5 => p.coeff 2) hfac
  have hm2 := coeff_quad_mul_succ2 a b h 0
  have h0 : h.coeff 0 =
      a ^ 2 - 3 * a * b ^ 2 + 6 * a * b - 2 * a
        + b ^ 4 - 3 * b ^ 3 + 2 * b ^ 2 + 1 := by
    rw [hm2] at hc2
    simp [q5, coeff_one, h1, h2] at hc2
    linear_combination -hc2
  have hc1 := congrArg (fun p : Polynomial F5 => p.coeff 1) hfac
  have hm1 := coeff_quad_mul_one a b h
  rw [hm1] at hc1
  simp [q5, coeff_one, h0, h1] at hc1
  have hc0 := congrArg (fun p : Polynomial F5 => p.coeff 0) hfac
  have hm0 := coeff_quad_mul_zero a b h
  rw [hm0] at hc0
  simp [q5, coeff_one, h0] at hc0
  have hbad : ¬(
      (1 : F5) = a * (a ^ 2 - 3 * a * b ^ 2 + 6 * a * b - 2 * a
        + b ^ 4 - 3 * b ^ 3 + 2 * b ^ 2 + 1)
      ∧
      (3 : F5) = b * (a ^ 2 - 3 * a * b ^ 2 + 6 * a * b - 2 * a
        + b ^ 4 - 3 * b ^ 3 + 2 * b ^ 2 + 1)
        + a * (2 * a * b - 3 * a - b ^ 3 + 3 * b ^ 2 - 2 * b)) := by
    fin_cases a <;> fin_cases b <;> native_decide
  exact hbad ⟨hc0, hc1⟩

end
end QuadraticDivisorScratch
