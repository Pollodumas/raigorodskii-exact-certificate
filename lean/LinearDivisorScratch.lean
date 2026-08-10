import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LinearDivisorScratch

open Polynomial

noncomputable section

abbrev F5 := ZMod 5
local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

noncomputable def q5 : Polynomial F5 :=
  X ^ 6 + C 3 * X ^ 5 + C 2 * X ^ 4 + X ^ 2 + C 3 * X + C 1

noncomputable def lin (a : F5) : Polynomial F5 := X + C a

def linRem (a : F5) : F5 :=
  a ^ 6 - 3 * a ^ 5 + 2 * a ^ 4 + a ^ 2 - 3 * a + 1

lemma q5_monic : q5.Monic := by
  unfold q5
  monicity <;> norm_num

lemma q5_natDegree : q5.natDegree = 6 := by
  unfold q5
  compute_degree! <;> norm_num

lemma q5_ne_zero : q5 ≠ 0 := q5_monic.ne_zero

lemma lin_monic (a : F5) : (lin a).Monic := by
  unfold lin
  monicity

lemma lin_natDegree (a : F5) : (lin a).natDegree = 1 := by
  unfold lin
  compute_degree!

lemma coeff_lin_mul_zero (a : F5) (h : Polynomial F5) :
    (lin a * h).coeff 0 = a * h.coeff 0 := by
  simp [lin, add_mul]

lemma coeff_lin_mul_succ (a : F5) (h : Polynomial F5) (n : ℕ) :
    (lin a * h).coeff (n + 1) = h.coeff n + a * h.coeff (n + 1) := by
  simp [lin, add_mul]

lemma linRem_ne_zero (a : F5) : linRem a ≠ 0 := by
  fin_cases a <;> native_decide

lemma lin_not_dvd_q5 (a : F5) : ¬ lin a ∣ q5 := by
  rintro ⟨h, hfac⟩
  have hh0 : h ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hfac
    exact q5_ne_zero hfac
  have hdeg : h.natDegree = 5 := by
    have hn := congrArg Polynomial.natDegree hfac
    rw [q5_natDegree, (lin_monic a).natDegree_mul' hh0, lin_natDegree] at hn
    omega
  have h6 : h.coeff 6 = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    omega
  have hc6 := congrArg (fun p : Polynomial F5 => p.coeff 6) hfac
  have h5 : h.coeff 5 = 1 := by
    rw [show 6 = 5 + 1 by omega, coeff_lin_mul_succ] at hc6
    norm_num [q5, h6] at hc6
    exact hc6.symm
  have hc5 := congrArg (fun p : Polynomial F5 => p.coeff 5) hfac
  have h4 : h.coeff 4 = 3 - a := by
    rw [show 5 = 4 + 1 by omega, coeff_lin_mul_succ] at hc5
    norm_num [q5, h5] at hc5
    linear_combination -hc5
  have hc4 := congrArg (fun p : Polynomial F5 => p.coeff 4) hfac
  have h3 : h.coeff 3 = a ^ 2 - 3 * a + 2 := by
    rw [show 4 = 3 + 1 by omega, coeff_lin_mul_succ] at hc4
    norm_num [q5, h4] at hc4
    linear_combination -hc4
  have hc3 := congrArg (fun p : Polynomial F5 => p.coeff 3) hfac
  have h2 : h.coeff 2 = -a ^ 3 + 3 * a ^ 2 - 2 * a := by
    rw [show 3 = 2 + 1 by omega, coeff_lin_mul_succ] at hc3
    norm_num [q5, h3] at hc3
    linear_combination -hc3
  have hc2 := congrArg (fun p : Polynomial F5 => p.coeff 2) hfac
  have h1 : h.coeff 1 = a ^ 4 - 3 * a ^ 3 + 2 * a ^ 2 + 1 := by
    rw [show 2 = 1 + 1 by omega, coeff_lin_mul_succ] at hc2
    norm_num [q5, h2] at hc2
    linear_combination -hc2
  have hc1 := congrArg (fun p : Polynomial F5 => p.coeff 1) hfac
  have h0 : h.coeff 0 = -a ^ 5 + 3 * a ^ 4 - 2 * a ^ 3 - a + 3 := by
    rw [show 1 = 0 + 1 by omega, coeff_lin_mul_succ] at hc1
    norm_num [q5, h1] at hc1
    linear_combination -hc1
  have hc0 := congrArg (fun p : Polynomial F5 => p.coeff 0) hfac
  have hrem : linRem a = 0 := by
    rw [coeff_lin_mul_zero] at hc0
    norm_num [q5, h0, linRem] at hc0
    linear_combination hc0
  exact linRem_ne_zero a hrem

end
end LinearDivisorScratch
