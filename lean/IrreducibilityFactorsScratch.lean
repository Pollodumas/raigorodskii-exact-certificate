import Mathlib

set_option autoImplicit false

namespace IrreducibilityFactorsScratch

open Polynomial

noncomputable section

abbrev F5 := ZMod 5

noncomputable def q5 : Polynomial F5 :=
  X ^ 6 + C 3 * X ^ 5 + C 2 * X ^ 4 + X ^ 2 + C 3 * X + C 1

lemma q5_monic : q5.Monic := by
  unfold q5
  monicity <;> norm_num

lemma q5_natDegree : q5.natDegree = 6 := by
  unfold q5
  compute_degree! <;> norm_num

lemma q5_ne_one : q5 ≠ 1 := by
  intro h
  have hd := congrArg Polynomial.natDegree h
  rw [q5_natDegree, natDegree_one] at hd
  omega

noncomputable def lin (a : F5) : Polynomial F5 := X + C a

noncomputable def linQuot (a : F5) : Polynomial F5 :=
  X ^ 5 + C (3 - a) * X ^ 4 + C (a ^ 2 - 3 * a + 2) * X ^ 3
    + C (-a ^ 3 + 3 * a ^ 2 - 2 * a) * X ^ 2
    + C (a ^ 4 - 3 * a ^ 3 + 2 * a ^ 2 + 1) * X
    + C (-a ^ 5 + 3 * a ^ 4 - 2 * a ^ 3 - a + 3)

def linRem (a : F5) : F5 :=
  a ^ 6 - 3 * a ^ 5 + 2 * a ^ 4 + a ^ 2 - 3 * a + 1

lemma q5_lin_identity (a : F5) :
    q5 = lin a * linQuot a + C (linRem a) := by
  unfold q5 lin linQuot linRem
  ring

lemma lin_monic (a : F5) : (lin a).Monic := by
  unfold lin
  monicity

lemma lin_natDegree (a : F5) : (lin a).natDegree = 1 := by
  unfold lin
  compute_degree!

lemma linRem_ne_zero (a : F5) : linRem a ≠ 0 := by
  fin_cases a <;> native_decide

lemma lin_not_dvd_q5 (a : F5) : ¬ lin a ∣ q5 := by
  intro hdvd
  have hprod : lin a ∣ lin a * linQuot a := dvd_mul_right _ _
  have hsub : lin a ∣ q5 - lin a * linQuot a := dvd_sub hdvd hprod
  have hrem : q5 - lin a * linQuot a = C (linRem a) := by
    rw [q5_lin_identity]
    ring
  rw [hrem] at hsub
  have hC : C (linRem a) ≠ (0 : Polynomial F5) := by
    simp [linRem_ne_zero]
  have hdeg : (C (linRem a)).natDegree < (lin a).natDegree := by
    rw [lin_natDegree]
    simp [linRem_ne_zero]
  exact (lin_monic a).not_dvd_of_natDegree_lt hC hdeg hsub

noncomputable def quad (a b : F5) : Polynomial F5 :=
  X ^ 2 + C b * X + C a

noncomputable def quadQuot (a b : F5) : Polynomial F5 :=
  X ^ 4 + C (3 - b) * X ^ 3 + C (-a + b ^ 2 - 3 * b + 2) * X ^ 2
    + C (2 * a * b - 3 * a - b ^ 3 + 3 * b ^ 2 - 2 * b) * X
    + C (a ^ 2 - 3 * a * b ^ 2 + 6 * a * b - 2 * a
      + b ^ 4 - 3 * b ^ 3 + 2 * b ^ 2 + 1)

def quadRem1 (a b : F5) : F5 :=
  -3 * a ^ 2 * b + 3 * a ^ 2 + 4 * a * b ^ 3 - 9 * a * b ^ 2
    + 4 * a * b - b ^ 5 + 3 * b ^ 4 - 2 * b ^ 3 - b + 3

def quadRem0 (a b : F5) : F5 :=
  -a ^ 3 + 3 * a ^ 2 * b ^ 2 - 6 * a ^ 2 * b + 2 * a ^ 2
    - a * b ^ 4 + 3 * a * b ^ 3 - 2 * a * b ^ 2 - a + 1

noncomputable def quadRem (a b : F5) : Polynomial F5 :=
  C (quadRem1 a b) * X + C (quadRem0 a b)

lemma q5_quad_identity (a b : F5) :
    q5 = quad a b * quadQuot a b + quadRem a b := by
  unfold q5 quad quadQuot quadRem quadRem1 quadRem0
  ring

lemma quad_monic (a b : F5) : (quad a b).Monic := by
  unfold quad
  monicity

lemma quad_natDegree (a b : F5) : (quad a b).natDegree = 2 := by
  unfold quad
  compute_degree!

lemma quadRem_coeff_nonzero (a b : F5) :
    quadRem0 a b ≠ 0 ∨ quadRem1 a b ≠ 0 := by
  fin_cases a <;> fin_cases b <;> native_decide

lemma quadRem_ne_zero (a b : F5) : quadRem a b ≠ 0 := by
  intro hzero
  rcases quadRem_coeff_nonzero a b with h0 | h1
  · apply h0
    have hc := congrArg (fun p : Polynomial F5 => p.coeff 0) hzero
    simpa [quadRem] using hc
  · apply h1
    have hc := congrArg (fun p : Polynomial F5 => p.coeff 1) hzero
    simpa [quadRem] using hc

lemma quadRem_natDegree_lt (a b : F5) :
    (quadRem a b).natDegree < (quad a b).natDegree := by
  have hle : (quadRem a b).natDegree ≤ 1 := by
    unfold quadRem
    compute_degree
  rw [quad_natDegree]
  omega

lemma quad_not_dvd_q5 (a b : F5) : ¬ quad a b ∣ q5 := by
  intro hdvd
  have hprod : quad a b ∣ quad a b * quadQuot a b := dvd_mul_right _ _
  have hsub : quad a b ∣ q5 - quad a b * quadQuot a b := dvd_sub hdvd hprod
  have hrem : q5 - quad a b * quadQuot a b = quadRem a b := by
    rw [q5_quad_identity]
    ring
  rw [hrem] at hsub
  exact (quad_monic a b).not_dvd_of_natDegree_lt
    (quadRem_ne_zero a b) (quadRem_natDegree_lt a b) hsub

noncomputable def cubic (a b c : F5) : Polynomial F5 :=
  X ^ 3 + C c * X ^ 2 + C b * X + C a

noncomputable def cubicQuot (a b c : F5) : Polynomial F5 :=
  X ^ 3 + C (3 - c) * X ^ 2 + C (2 - b - 3 * c + c ^ 2) * X
    + C (-a + 2 * b * c - 3 * b - c ^ 3 + 3 * c ^ 2 - 2 * c)

def cubicRem2 (a b c : F5) : F5 :=
  2 * a * c - 3 * a + b ^ 2 - 3 * b * c ^ 2 + 6 * b * c - 2 * b
    + c ^ 4 - 3 * c ^ 3 + 2 * c ^ 2 + 1

def cubicRem1 (a b c : F5) : F5 :=
  2 * a * b - a * c ^ 2 + 3 * a * c - 2 * a - 2 * b ^ 2 * c
    + 3 * b ^ 2 + b * c ^ 3 - 3 * b * c ^ 2 + 2 * b * c + 3

def cubicRem0 (a b c : F5) : F5 :=
  a ^ 2 - 2 * a * b * c + 3 * a * b + a * c ^ 3 - 3 * a * c ^ 2
    + 2 * a * c + 1

noncomputable def cubicRem (a b c : F5) : Polynomial F5 :=
  C (cubicRem2 a b c) * X ^ 2 + C (cubicRem1 a b c) * X + C (cubicRem0 a b c)

lemma q5_cubic_identity (a b c : F5) :
    q5 = cubic a b c * cubicQuot a b c + cubicRem a b c := by
  unfold q5 cubic cubicQuot cubicRem cubicRem2 cubicRem1 cubicRem0
  ring

lemma cubic_monic (a b c : F5) : (cubic a b c).Monic := by
  unfold cubic
  monicity

lemma cubic_natDegree (a b c : F5) : (cubic a b c).natDegree = 3 := by
  unfold cubic
  compute_degree!

lemma cubicRem_coeff_nonzero (a b c : F5) :
    cubicRem0 a b c ≠ 0 ∨ cubicRem1 a b c ≠ 0 ∨ cubicRem2 a b c ≠ 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> native_decide

lemma cubicRem_ne_zero (a b c : F5) : cubicRem a b c ≠ 0 := by
  intro hzero
  rcases cubicRem_coeff_nonzero a b c with h0 | h1 | h2
  · apply h0
    have hc := congrArg (fun p : Polynomial F5 => p.coeff 0) hzero
    simpa [cubicRem] using hc
  · apply h1
    have hc := congrArg (fun p : Polynomial F5 => p.coeff 1) hzero
    simpa [cubicRem] using hc
  · apply h2
    have hc := congrArg (fun p : Polynomial F5 => p.coeff 2) hzero
    simpa [cubicRem] using hc

lemma cubicRem_natDegree_lt (a b c : F5) :
    (cubicRem a b c).natDegree < (cubic a b c).natDegree := by
  have hle : (cubicRem a b c).natDegree ≤ 2 := by
    unfold cubicRem
    compute_degree
  rw [cubic_natDegree]
  omega

lemma cubic_not_dvd_q5 (a b c : F5) : ¬ cubic a b c ∣ q5 := by
  intro hdvd
  have hprod : cubic a b c ∣ cubic a b c * cubicQuot a b c := dvd_mul_right _ _
  have hsub : cubic a b c ∣ q5 - cubic a b c * cubicQuot a b c := dvd_sub hdvd hprod
  have hrem : q5 - cubic a b c * cubicQuot a b c = cubicRem a b c := by
    rw [q5_cubic_identity]
    ring
  rw [hrem] at hsub
  exact (cubic_monic a b c).not_dvd_of_natDegree_lt
    (cubicRem_ne_zero a b c) (cubicRem_natDegree_lt a b c) hsub

lemma monic_degree_one_form (g : Polynomial F5) (hg : g.Monic)
    (hdeg : g.natDegree = 1) :
    g = X + C (g.coeff 0) := by
  rw [hg.as_sum, hdeg]
  norm_num [Finset.sum_range_succ]
  ring

lemma monic_degree_two_form (g : Polynomial F5) (hg : g.Monic)
    (hdeg : g.natDegree = 2) :
    g = X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) := by
  rw [hg.as_sum, hdeg]
  norm_num [Finset.sum_range_succ]
  ring

lemma monic_degree_three_form (g : Polynomial F5) (hg : g.Monic)
    (hdeg : g.natDegree = 3) :
    g = X ^ 3 + C (g.coeff 2) * X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) := by
  rw [hg.as_sum, hdeg]
  norm_num [Finset.sum_range_succ]
  ring

theorem q5_irreducible : Irreducible q5 := by
  rw [q5_monic.irreducible_iff_lt_natDegree_lt q5_ne_one]
  intro g hg hdeg hdvd
  have hrange : 0 < g.natDegree ∧ g.natDegree ≤ 3 := by
    simpa [q5_natDegree] using hdeg
  have hcases : g.natDegree = 1 ∨ g.natDegree = 2 ∨ g.natDegree = 3 := by
    omega
  rcases hcases with h1 | h2 | h3
  · rw [monic_degree_one_form g hg h1] at hdvd
    exact lin_not_dvd_q5 (g.coeff 0) hdvd
  · rw [monic_degree_two_form g hg h2] at hdvd
    exact quad_not_dvd_q5 (g.coeff 0) (g.coeff 1) hdvd
  · rw [monic_degree_three_form g hg h3] at hdvd
    exact cubic_not_dvd_q5 (g.coeff 0) (g.coeff 1) (g.coeff 2) hdvd

end
end IrreducibilityFactorsScratch
