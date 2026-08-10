import Mathlib

set_option autoImplicit false

namespace IrreducibilityExhaustiveScratch

open Polynomial

abbrev F5 := ZMod 5

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

def q5 : Polynomial F5 :=
  X ^ 6 + C 3 * X ^ 5 + C 2 * X ^ 4 + X ^ 2 + C 3 * X + C 1

def lin (a : F5) : Polynomial F5 := X + C a

def quad (a b : F5) : Polynomial F5 :=
  X ^ 2 + C b * X + C a

def cubic (a b c : F5) : Polynomial F5 :=
  X ^ 3 + C c * X ^ 2 + C b * X + C a

lemma lin_not_dvd_q5 (a : F5) : ¬ lin a ∣ q5 := by
  fin_cases a <;> native_decide

lemma quad_not_dvd_q5 (a b : F5) : ¬ quad a b ∣ q5 := by
  fin_cases a <;> fin_cases b <;> native_decide

lemma cubic_not_dvd_q5 (a b c : F5) : ¬ cubic a b c ∣ q5 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> native_decide

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

lemma monic_degree_one_form (g : Polynomial F5) (hg : g.Monic)
    (hdeg : g.natDegree = 1) :
    g = lin (g.coeff 0) := by
  rw [hg.as_sum, hdeg]
  norm_num [Finset.sum_range_succ, lin]

lemma monic_degree_two_form (g : Polynomial F5) (hg : g.Monic)
    (hdeg : g.natDegree = 2) :
    g = quad (g.coeff 0) (g.coeff 1) := by
  rw [hg.as_sum, hdeg]
  norm_num [Finset.sum_range_succ, quad] <;> ring

lemma monic_degree_three_form (g : Polynomial F5) (hg : g.Monic)
    (hdeg : g.natDegree = 3) :
    g = cubic (g.coeff 0) (g.coeff 1) (g.coeff 2) := by
  rw [hg.as_sum, hdeg]
  norm_num [Finset.sum_range_succ, cubic] <;> ring

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

end IrreducibilityExhaustiveScratch
