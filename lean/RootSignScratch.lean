import RaigorodskiiCertificate

set_option autoImplicit false

namespace Raigorodskii

noncomputable section

def Qneg (t : ℝ) : ℝ := Q (-t)

lemma bernstein_sum_six (u : ℝ) :
    (1 - u) ^ 6
      + 6 * u * (1 - u) ^ 5
      + 15 * u ^ 2 * (1 - u) ^ 4
      + 20 * u ^ 3 * (1 - u) ^ 3
      + 15 * u ^ 4 * (1 - u) ^ 2
      + 6 * u ^ 5 * (1 - u)
      + u ^ 6 = 1 := by
  ring

lemma Q_positive_interval_bernstein (u : ℝ) :
    Q (((6 : ℝ) / 5) * u) =
      (-31 : ℝ) * (1 - u) ^ 6
      + (-(113 : ℝ) / 5) * (6 * u * (1 - u) ^ 5)
      + (-(2627 : ℝ) / 125) * (15 * u ^ 2 * (1 - u) ^ 4)
      + (-(5657 : ℝ) / 125) * (20 * u ^ 3 * (1 - u) ^ 3)
      + (-(77339 : ℝ) / 3125) * (15 * u ^ 4 * (1 - u) ^ 2)
      + (-(57233 : ℝ) / 3125) * (6 * u ^ 5 * (1 - u))
      + (-(49351 : ℝ) / 15625) * u ^ 6 := by
  unfold Q
  ring

lemma Q_negative_interval_bernstein (u : ℝ) :
    Qneg (((2 : ℝ) / 5) * u) =
      (-31 : ℝ) * (1 - u) ^ 6
      + (-(169 : ℝ) / 5) * (6 * u * (1 - u) ^ 5)
      + (-(14009 : ℝ) / 375) * (15 * u ^ 2 * (1 - u) ^ 4)
      + (-(5121 : ℝ) / 125) * (20 * u ^ 3 * (1 - u) ^ 3)
      + (-(133819 : ℝ) / 3125) * (15 * u ^ 4 * (1 - u) ^ 2)
      + (-(366587 : ℝ) / 9375) * (6 * u ^ 5 * (1 - u))
      + (-(351479 : ℝ) / 15625) * u ^ 6 := by
  unfold Qneg Q
  ring

lemma Q_neg_on_zero_to_six_fifths {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ (6 : ℝ) / 5) : Q x < 0 := by
  let u : ℝ := ((5 : ℝ) / 6) * x
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; nlinarith
  have h1u : 0 ≤ 1 - u := by linarith
  have hxrepr : x = ((6 : ℝ) / 5) * u := by dsimp [u]; ring
  have hB0 : 0 ≤ (1 - u) ^ 6 := by positivity
  have hB1 : 0 ≤ 6 * u * (1 - u) ^ 5 := by positivity
  have hB2 : 0 ≤ 15 * u ^ 2 * (1 - u) ^ 4 := by positivity
  have hB3 : 0 ≤ 20 * u ^ 3 * (1 - u) ^ 3 := by positivity
  have hB4 : 0 ≤ 15 * u ^ 4 * (1 - u) ^ 2 := by positivity
  have hB5 : 0 ≤ 6 * u ^ 5 * (1 - u) := by positivity
  have hB6 : 0 ≤ u ^ 6 := by positivity
  have h0 : (-31 : ℝ) * (1 - u) ^ 6 ≤
      (-(49351 : ℝ) / 15625) * (1 - u) ^ 6 := by
    exact mul_le_mul_of_nonneg_right (by norm_num) hB0
  have h1 : (-(113 : ℝ) / 5) * (6 * u * (1 - u) ^ 5) ≤
      (-(49351 : ℝ) / 15625) * (6 * u * (1 - u) ^ 5) := by
    exact mul_le_mul_of_nonneg_right (by norm_num) hB1
  have h2 : (-(2627 : ℝ) / 125) * (15 * u ^ 2 * (1 - u) ^ 4) ≤
      (-(49351 : ℝ) / 15625) * (15 * u ^ 2 * (1 - u) ^ 4) := by
    exact mul_le_mul_of_nonneg_right (by norm_num) hB2
  have h3 : (-(5657 : ℝ) / 125) * (20 * u ^ 3 * (1 - u) ^ 3) ≤
      (-(49351 : ℝ) / 15625) * (20 * u ^ 3 * (1 - u) ^ 3) := by
    exact mul_le_mul_of_nonneg_right (by norm_num) hB3
  have h4 : (-(77339 : ℝ) / 3125) * (15 * u ^ 4 * (1 - u) ^ 2) ≤
      (-(49351 : ℝ) / 15625) * (15 * u ^ 4 * (1 - u) ^ 2) := by
    exact mul_le_mul_of_nonneg_right (by norm_num) hB4
  have h5 : (-(57233 : ℝ) / 3125) * (6 * u ^ 5 * (1 - u)) ≤
      (-(49351 : ℝ) / 15625) * (6 * u ^ 5 * (1 - u)) := by
    exact mul_le_mul_of_nonneg_right (by norm_num) hB5
  have h6 : (-(49351 : ℝ) / 15625) * u ^ 6 ≤
      (-(49351 : ℝ) / 15625) * u ^ 6 := le_rfl
  have hsum := bernstein_sum_six u
  rw [hxrepr, Q_positive_interval_bernstein]
  nlinarith

lemma Qneg_neg_on_zero_to_two_fifths {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ (2 : ℝ) / 5) : Qneg t < 0 := by
  let u : ℝ := ((5 : ℝ) / 2) * t
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; nlinarith
  have h1u : 0 ≤ 1 - u := by linarith
  have htrepr : t = ((2 : ℝ) / 5) * u := by dsimp [u]; ring
  have hB0 : 0 ≤ (1 - u) ^ 6 := by positivity
  have hB1 : 0 ≤ 6 * u * (1 - u) ^ 5 := by positivity
  have hB2 : 0 ≤ 15 * u ^ 2 * (1 - u) ^ 4 := by positivity
  have hB3 : 0 ≤ 20 * u ^ 3 * (1 - u) ^ 3 := by positivity
  have hB4 : 0 ≤ 15 * u ^ 4 * (1 - u) ^ 2 := by positivity
  have hB5 : 0 ≤ 6 * u ^ 5 * (1 - u) := by positivity
  have hB6 : 0 ≤ u ^ 6 := by positivity
  have h0 : (-31 : ℝ) * (1 - u) ^ 6 ≤
      (-(351479 : ℝ) / 15625) * (1 - u) ^ 6 := by
    exact mul_le_mul_of_nonneg_right (by norm_num) hB0
  have h1 : (-(169 : ℝ) / 5) * (6 * u * (1 - u) ^ 5) ≤
      (-(351479 : ℝ) / 15625) * (6 * u * (1 - u) ^ 5) := by
    exact mul_le_mul_of_nonneg_right (by norm_num) hB1
  have h2 : (-(14009 : ℝ) / 375) * (15 * u ^ 2 * (1 - u) ^ 4) ≤
      (-(351479 : ℝ) / 15625) * (15 * u ^ 2 * (1 - u) ^ 4) := by
    exact mul_le_mul_of_nonneg_right (by norm_num) hB2
  have h3 : (-(5121 : ℝ) / 125) * (20 * u ^ 3 * (1 - u) ^ 3) ≤
      (-(351479 : ℝ) / 15625) * (20 * u ^ 3 * (1 - u) ^ 3) := by
    exact mul_le_mul_of_nonneg_right (by norm_num) hB3
  have h4 : (-(133819 : ℝ) / 3125) * (15 * u ^ 4 * (1 - u) ^ 2) ≤
      (-(351479 : ℝ) / 15625) * (15 * u ^ 4 * (1 - u) ^ 2) := by
    exact mul_le_mul_of_nonneg_right (by norm_num) hB4
  have h5 : (-(366587 : ℝ) / 9375) * (6 * u ^ 5 * (1 - u)) ≤
      (-(351479 : ℝ) / 15625) * (6 * u ^ 5 * (1 - u)) := by
    exact mul_le_mul_of_nonneg_right (by norm_num) hB5
  have h6 : (-(351479 : ℝ) / 15625) * u ^ 6 ≤
      (-(351479 : ℝ) / 15625) * u ^ 6 := le_rfl
  have hsum := bernstein_sum_six u
  rw [htrepr, Q_negative_interval_bernstein]
  nlinarith

end
end Raigorodskii
