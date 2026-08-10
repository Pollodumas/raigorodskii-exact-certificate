import RaigorodskiiCertificate

set_option autoImplicit false

namespace Raigorodskii

open Set

noncomputable section

lemma Qder_left_shift (y : ℝ) :
    Qder (-(1 : ℝ) / 4 - y) =
      -864 * y ^ 5 - 3720 * y ^ 4 - 5772 * y ^ 3
        - 3729 * y ^ 2 - (6847 / 8 : ℝ) * y - (493 / 32 : ℝ) := by
  unfold Qder
  ring

lemma Qder_neg_left {x : ℝ} (hx : x ≤ -(1 : ℝ) / 4) : Qder x < 0 := by
  let y : ℝ := -(1 : ℝ) / 4 - x
  have hy : 0 ≤ y := by
    dsimp [y]
    linarith
  have hxrepr : x = -(1 : ℝ) / 4 - y := by
    dsimp [y]
    ring
  have hy2 : 0 ≤ y ^ 2 := by positivity
  have hy3 : 0 ≤ y ^ 3 := by positivity
  have hy4 : 0 ≤ y ^ 4 := by positivity
  have hy5 : 0 ≤ y ^ 5 := by positivity
  rw [hxrepr, Qder_left_shift]
  nlinarith

lemma Q_strictAntiOn_left : StrictAntiOn Q (Iic (-(1 : ℝ) / 4)) := by
  apply strictAntiOn_of_deriv_neg (convex_Iic (-(1 : ℝ) / 4))
  · unfold Q
    fun_prop
  · intro x hx
    rw [deriv_Q]
    exact Qder_neg_left (le_of_lt (by simpa using hx))

lemma Q_negative_signs :
    0 < Q (-(1 : ℝ) / 2) ∧ Q (-(1 : ℝ) / 4) < 0 := by
  norm_num [Q]

lemma exists_Q_negative_root :
    ∃ x ∈ Ioo (-(1 : ℝ) / 2) (-(1 : ℝ) / 4), Q x = 0 := by
  have hcont : ContinuousOn Q (Icc (-(1 : ℝ) / 2) (-(1 : ℝ) / 4)) := by
    unfold Q
    fun_prop
  have hzero :
      (0 : ℝ) ∈ Ioo (Q (-(1 : ℝ) / 4)) (Q (-(1 : ℝ) / 2)) := by
    norm_num [Q]
  rcases (intermediate_value_Ioo'
      (a := (-(1 : ℝ) / 2)) (b := (-(1 : ℝ) / 4)) (f := Q)
      (by norm_num) hcont hzero) with ⟨x, hx, hQx⟩
  exact ⟨x, hx, hQx⟩

def rneg : ℝ := Classical.choose exists_Q_negative_root

lemma rneg_mem : rneg ∈ Ioo (-(1 : ℝ) / 2) (-(1 : ℝ) / 4) :=
  (Classical.choose_spec exists_Q_negative_root).1

lemma rneg_root : Q rneg = 0 :=
  (Classical.choose_spec exists_Q_negative_root).2

lemma Q_root_unique_left {x : ℝ}
    (hx : x ≤ -(1 : ℝ) / 4) (hQx : Q x = 0) : x = rneg := by
  have hr : rneg ≤ -(1 : ℝ) / 4 := le_of_lt rneg_mem.2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hxr | hrx
  · have h := Q_strictAntiOn_left hx hr hxr
    rw [hQx, rneg_root] at h
    exact (lt_irrefl 0) h
  · have h := Q_strictAntiOn_left hr hx hrx
    rw [rneg_root, hQx] at h
    exact (lt_irrefl 0) h

def BernsteinRhs (u v : ℝ) : ℝ :=
  3311109375 * v ^ 7
    + 25054246875 * u * v ^ 6
    + 5214142500 * u ^ 2 * v ^ 5
    + 84458871000 * u ^ 3 * v ^ 4
    + 135071764800 * u ^ 4 * v ^ 3
    + 44905827120 * u ^ 5 * v ^ 2
    + 11087239296 * u ^ 6 * v
    + 265310976 * u ^ 7

lemma bernstein_identity (x : ℝ) :
    (84000000 : ℝ) * 29 ^ 7 * (-Q x) =
      BernsteinRhs (20 * x + 5) (24 - 20 * x) := by
  unfold BernsteinRhs Q
  ring

lemma BernsteinRhs_pos {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : 0 < u + v) :
    0 < BernsteinRhs u v := by
  have hpos : 0 < u ∨ 0 < v := by
    nlinarith
  rcases hpos with hu' | hv'
  · unfold BernsteinRhs
    positivity
  · unfold BernsteinRhs
    positivity

lemma Q_neg_middle {x : ℝ}
    (hx : x ∈ Icc (-(1 : ℝ) / 4) ((6 : ℝ) / 5)) : Q x < 0 := by
  let u : ℝ := 20 * x + 5
  let v : ℝ := 24 - 20 * x
  have hu : 0 ≤ u := by
    dsimp [u]
    linarith [hx.1]
  have hv : 0 ≤ v := by
    dsimp [v]
    linarith [hx.2]
  have huv : 0 < u + v := by
    dsimp [u, v]
    norm_num
  have hB : 0 < BernsteinRhs u v := BernsteinRhs_pos hu hv huv
  have hid := bernstein_identity x
  change (84000000 : ℝ) * 29 ^ 7 * (-Q x) = BernsteinRhs u v at hid
  have hscale : 0 < (84000000 : ℝ) * 29 ^ 7 := by norm_num
  nlinarith

lemma Q_root_eq_rneg_or_gamma {x : ℝ} (hQx : Q x = 0) :
    x = rneg ∨ x = gamma := by
  by_cases hxleft : x ≤ -(1 : ℝ) / 4
  · exact Or.inl (Q_root_unique_left hxleft hQx)
  · have hxgt : -(1 : ℝ) / 4 < x := lt_of_not_ge hxleft
    by_cases hxright : (6 : ℝ) / 5 ≤ x
    · exact Or.inr (Q_root_unique_above_six_fifths hxright hQx)
    · have hxmid : x ∈ Icc (-(1 : ℝ) / 4) ((6 : ℝ) / 5) :=
        ⟨le_of_lt hxgt, le_of_not_ge hxright⟩
      have hneg := Q_neg_middle hxmid
      rw [hQx] at hneg
      exact (lt_irrefl 0 hneg).elim

lemma roots_set_eq : {x : ℝ | Q x = 0} = {rneg, gamma} := by
  ext x
  constructor
  · intro hx
    rcases Q_root_eq_rneg_or_gamma hx with h | h
    · simp [h]
    · simp [h]
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact rneg_root
    · exact Q_gamma

lemma rneg_ne_gamma : rneg ≠ gamma := by
  have hlt : rneg < gamma := by
    calc
      rneg < -(1 : ℝ) / 4 := rneg_mem.2
      _ < (6 : ℝ) / 5 := by norm_num
      _ < gamma := gamma_gt_six_fifths
  exact ne_of_lt hlt

theorem Q_has_exactly_two_real_roots_scratch :
    Set.encard {x : ℝ | Q x = 0} = 2 := by
  rw [roots_set_eq]
  simp [rneg_ne_gamma]

end
end Raigorodskii
