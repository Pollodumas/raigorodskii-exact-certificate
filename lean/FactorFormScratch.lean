import Mathlib

set_option autoImplicit false

namespace FactorFormScratch

open Polynomial

noncomputable section

abbrev F5 := ZMod 5

noncomputable def q5 : Polynomial F5 :=
  X ^ 6 + C 3 * X ^ 5 + C 2 * X ^ 4 + X ^ 2 + C 3 * X + C 1

lemma q5_monic : q5.Monic := by
  unfold q5
  monicity

lemma q5_natDegree : q5.natDegree = 6 := by
  rw [q5_monic.natDegree_eq_iff_degree_eq]
  norm_num [q5]

lemma q5_no_root (x : F5) : ¬ IsRoot q5 x := by
  fin_cases x <;> norm_num [q5, IsRoot]

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

end
end FactorFormScratch
