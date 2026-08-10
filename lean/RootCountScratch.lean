import RootSignScratch

set_option autoImplicit false

namespace Raigorodskii

open Set
open Polynomial

noncomputable section

def QnegDer (t : ℝ) : ℝ :=
  864 * t ^ 5 + 2640 * t ^ 4 + 2592 * t ^ 3
    + 660 * t ^ 2 - 142 * t - 42

def qNegPoly : Polynomial ℝ :=
  C 144 * X ^ 6 + C 528 * X ^ 5 + C 648 * X ^ 4 + C 220 * X ^ 3
    - C 71 * X ^ 2 - C 42 * X - C 31

lemma Qneg_eq_eval (t : ℝ) : Qneg t = qNegPoly.eval t := by
  simp [Qneg, Q, qNegPoly]
  ring

lemma deriv_Qneg (t : ℝ) : deriv Qneg t = QnegDer t := by
  have hfun : Qneg = fun x => qNegPoly.eval x := by
    funext x
    exact Qneg_eq_eval x
  rw [hfun]
  simpa [qNegPoly, QnegDer] using (qNegPoly.hasDerivAt t).deriv

lemma QnegDer_pos {t : ℝ} (ht : (2 : ℝ) / 5 ≤ t) : 0 < QnegDer t := by
  let y : ℝ := t - (2 : ℝ) / 5
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have ht0 : 0 ≤ t := by linarith
  have hrepr : t = (2 : ℝ) / 5 + y := by dsimp [y]; ring
  have hquad : 0 < 660 * t ^ 2 - 142 * t - 42 := by
    rw [hrepr]
    nlinarith [sq_nonneg y]
  have ht3 : 0 ≤ t ^ 3 := by positivity
  have ht4 : 0 ≤ t ^ 4 := by positivity
  have ht5 : 0 ≤ t ^ 5 := by positivity
  unfold QnegDer
  nlinarith

lemma Qneg_strictMonoOn : StrictMonoOn Qneg (Ici ((2 : ℝ) / 5)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici ((2 : ℝ) / 5))
  · unfold Qneg Q
    fun_prop
  · intro t ht
    rw [deriv_Qneg]
    exact QnegDer_pos (le_of_lt (by simpa using ht))

lemma Qneg_two_fifths_neg : Qneg ((2 : ℝ) / 5) < 0 := by
  exact Qneg_neg_on_zero_to_two_fifths (by norm_num) (by norm_num)

lemma Qneg_one_pos : 0 < Qneg 1 := by
  norm_num [Qneg, Q]

lemma exists_Qneg_root :
    ∃ t ∈ Ioo ((2 : ℝ) / 5) 1, Qneg t = 0 := by
  have hcont : ContinuousOn Qneg (Icc ((2 : ℝ) / 5) 1) := by
    unfold Qneg Q
    fun_prop
  have hzero : (0 : ℝ) ∈ Ioo (Qneg ((2 : ℝ) / 5)) (Qneg 1) := by
    exact ⟨Qneg_two_fifths_neg, Qneg_one_pos⟩
  rcases (intermediate_value_Ioo' (a := (2 : ℝ) / 5) (b := 1) (f := Qneg)
      (by norm_num) hcont hzero) with ⟨t, ht, hQt⟩
  exact ⟨t, ht, hQt⟩

lemma Qneg_root_unique {a b : ℝ}
    (ha : (2 : ℝ) / 5 ≤ a) (hb : (2 : ℝ) / 5 ≤ b)
    (hQa : Qneg a = 0) (hQb : Qneg b = 0) : a = b := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hba
  · have h := Qneg_strictMonoOn ha hb hab
    rw [hQa, hQb] at h
    exact (lt_irrefl 0) h
  · have h := Qneg_strictMonoOn hb ha hba
    rw [hQb, hQa] at h
    exact (lt_irrefl 0) h

def tneg : ℝ := Classical.choose exists_Qneg_root
lemma tneg_mem : tneg ∈ Ioo ((2 : ℝ) / 5) 1 :=
  (Classical.choose_spec exists_Qneg_root).1
lemma tneg_root : Qneg tneg = 0 :=
  (Classical.choose_spec exists_Qneg_root).2

def negroot : ℝ := -tneg

lemma negroot_neg : negroot < 0 := by
  unfold negroot
  linarith [tneg_mem.1]

lemma negroot_root : Q negroot = 0 := by
  have h := tneg_root
  simpa [Qneg, negroot] using h

lemma negative_Q_root_eq_negroot {x : ℝ} (hx : x < 0) (hQx : Q x = 0) :
    x = negroot := by
  let t : ℝ := -x
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have hQt : Qneg t = 0 := by
    dsimp [t]
    simpa [Qneg] using hQx
  have ht : (2 : ℝ) / 5 ≤ t := by
    by_contra hnot
    have hlt : t < (2 : ℝ) / 5 := lt_of_not_ge hnot
    have hneg := Qneg_neg_on_zero_to_two_fifths ht0 (le_of_lt hlt)
    rw [hQt] at hneg
    exact (lt_irrefl 0) hneg
  have heq : t = tneg :=
    Qneg_root_unique ht (le_of_lt tneg_mem.1) hQt tneg_root
  unfold negroot
  dsimp [t] at heq
  linarith

lemma nonnegative_Q_root_eq_gamma {x : ℝ} (hx : 0 ≤ x) (hQx : Q x = 0) :
    x = gamma := by
  have hdom : (6 : ℝ) / 5 ≤ x := by
    by_contra hnot
    have hxle : x ≤ (6 : ℝ) / 5 := le_of_not_ge hnot
    have hneg := Q_neg_on_zero_to_six_fifths hx hxle
    rw [hQx] at hneg
    exact (lt_irrefl 0) hneg
  exact Q_root_unique_above_six_fifths hdom hQx

lemma Q_root_iff (x : ℝ) : Q x = 0 ↔ x = negroot ∨ x = gamma := by
  constructor
  · intro hQx
    rcases lt_or_ge x 0 with hx | hx
    · exact Or.inl (negative_Q_root_eq_negroot hx hQx)
    · exact Or.inr (nonnegative_Q_root_eq_gamma hx hQx)
  · rintro (rfl | rfl)
    · exact negroot_root
    · exact Q_gamma

theorem Q_has_exactly_two_real_roots_verified :
    Set.encard {x : ℝ | Q x = 0} = 2 := by
  have hset : {x : ℝ | Q x = 0} = {negroot, gamma} := by
    ext x
    simp [Q_root_iff]
  rw [hset]
  have hne : negroot ≠ gamma := by
    linarith [negroot_neg, gamma_gt_six_fifths]
  simp [hne]

end
end Raigorodskii
