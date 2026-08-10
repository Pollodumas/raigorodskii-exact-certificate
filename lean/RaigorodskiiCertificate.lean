import Mathlib

/-!
# Exact algebraic certificate for the Raigorodskii constant

This file formalizes the elementary real-algebraic core of the certificate in
J. Paz Marchese, "An Exact Algebraic Certificate for the Raigorodskii
Lower-Bound Constant", draft v0.8 (28 July 2026).

STATUS
* The exact polynomial identities and rational sign checks are written as
  kernel-checkable Lean proofs.
* The calculus/ordering proof of the unique maximizer is included.
* Four declarations remain `sorry`:
  (1) irreducibility of the sextic over Q from the finite-field certificate;
  (2) the exact count of all real roots;
  (3) algebraic integrality of 6 * gamma in the chosen `IsIntegral` interface;
  (4) minimality of the scaling factor 6.
* The Galois-group and "not expressible by radicals" claims are not stated:
  current Mathlib has splitting-field/Galois infrastructure, but no convenient
  end-to-end theorem implementing the paper's Dedekind-cycle argument.
-/

set_option autoImplicit false

namespace Raigorodskii

open Set
open Polynomial

noncomputable section

def N (s : ℝ) : ℝ := 1 + s + s ^ 3
def D (s : ℝ) : ℝ := 1 + s ^ 2 + s ^ 4
def F (s : ℝ) : ℝ := N s / D s

def P (s : ℝ) : ℝ :=
  1 - 2 * s + 2 * s ^ 2 - 4 * s ^ 3 - 2 * s ^ 4 - s ^ 6

def Pder (s : ℝ) : ℝ :=
  -2 + 4 * s - 12 * s ^ 2 - 8 * s ^ 3 - 6 * s ^ 5

def Q (x : ℝ) : ℝ :=
  144 * x ^ 6 - 528 * x ^ 5 + 648 * x ^ 4 - 220 * x ^ 3
    - 71 * x ^ 2 + 42 * x - 31

def Qder (x : ℝ) : ℝ :=
  864 * x ^ 5 - 2640 * x ^ 4 + 2592 * x ^ 3
    - 660 * x ^ 2 - 142 * x + 42

lemma D_pos (s : ℝ) : 0 < D s := by
  unfold D
  nlinarith [sq_nonneg s, sq_nonneg (s ^ 2)]

lemma D_ne_zero (s : ℝ) : D s ≠ 0 := ne_of_gt (D_pos s)

lemma deriv_P (s : ℝ) : deriv P s = Pder s := by
  unfold P Pder
  simp
  ring

lemma Pder_neg {s : ℝ} (hs : 0 < s) : Pder s < 0 := by
  have hquad : 0 < 12 * s ^ 2 - 4 * s + 2 := by
    nlinarith [sq_nonneg (6 * s - 1)]
  have hs3 : 0 ≤ s ^ 3 := by positivity
  have hs5 : 0 ≤ s ^ 5 := by positivity
  unfold Pder
  nlinarith

lemma P_strictAntiOn_pos : StrictAntiOn P (Ioi (0 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
  · unfold P
    fun_prop
  · intro x hx
    rw [deriv_P]
    exact Pder_neg (by simpa using hx)

lemma P_zero_and_one : P 0 = 1 ∧ P 1 = -6 := by
  norm_num [P]

lemma exists_P_root : ∃ s ∈ Ioo (0 : ℝ) 1, P s = 0 := by
  have hcont : ContinuousOn P (Icc (0 : ℝ) 1) := by
    unfold P
    fun_prop
  have hzero : (0 : ℝ) ∈ Ioo (P 1) (P 0) := by
    norm_num [P]
  rcases (intermediate_value_Ioo' (a := (0 : ℝ)) (b := 1) (f := P)
      (by norm_num) hcont hzero) with ⟨s, hs, hPs⟩
  exact ⟨s, hs, hPs⟩

lemma P_root_unique {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hPa : P a = 0) (hPb : P b = 0) : a = b := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hba
  · have h := P_strictAntiOn_pos ha.1 hb.1 hab
    rw [hPa, hPb] at h
    exact (lt_irrefl 0) h
  · have h := P_strictAntiOn_pos hb.1 ha.1 hba
    rw [hPb, hPa] at h
    exact (lt_irrefl 0) h

def sstar : ℝ := Classical.choose exists_P_root
lemma sstar_mem : sstar ∈ Ioo (0 : ℝ) 1 := (Classical.choose_spec exists_P_root).1
lemma sstar_root : P sstar = 0 := (Classical.choose_spec exists_P_root).2

lemma sstar_unique {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hPs : P s = 0) : s = sstar :=
  P_root_unique hs sstar_mem hPs sstar_root

lemma P_nine_twentieths_pos : 0 < P ((9 : ℝ) / 20) := by norm_num [P]

lemma sstar_gt_nine_twentieths : (9 : ℝ) / 20 < sstar := by
  by_contra hnot
  have hle : sstar ≤ (9 : ℝ) / 20 := le_of_not_gt hnot
  have hne : sstar ≠ (9 : ℝ) / 20 := by
    intro heq
    have h := sstar_root
    rw [heq] at h
    norm_num [P] at h
  have hlt : sstar < (9 : ℝ) / 20 := lt_of_le_of_ne hle hne
  have hanti := P_strictAntiOn_pos sstar_mem.1 (by norm_num) hlt
  rw [sstar_root] at hanti
  have hp := P_nine_twentieths_pos
  nlinarith

def A (s t : ℝ) : ℝ :=
  s ^ 2 * (t ^ 3 + t + 1)
    + s * (t ^ 4 + t ^ 2 + 2 * t - 1)
    + (t ^ 5 + 2 * t ^ 3 + 3 * t ^ 2 - t + 1)

lemma comparison_identity (s t : ℝ) :
    N t * D s - N s * D t = (s - t) ^ 2 * A s t - (s - t) * P t := by
  unfold N D A P
  ring

lemma A_pos {s t : ℝ} (hs : 0 ≤ s) (ht : (9 : ℝ) / 20 < t) : 0 < A s t := by
  have ht0 : 0 < t := by nlinarith
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have ht3 : 0 ≤ t ^ 3 := by positivity
  have ht4 : 0 ≤ t ^ 4 := by positivity
  have ht5 : 0 ≤ t ^ 5 := by positivity
  have hprod : 0 < (t - (9 : ℝ) / 20) * (t + (9 : ℝ) / 20) := by
    apply mul_pos
    · linarith
    · nlinarith
  have ht2lower : ((9 : ℝ) / 20) ^ 2 < t ^ 2 := by nlinarith
  have hc1 : 0 < t ^ 3 + t + 1 := by nlinarith
  have hc2 : 0 < t ^ 4 + t ^ 2 + 2 * t - 1 := by nlinarith
  have hc3 : 0 < t ^ 5 + 2 * t ^ 3 + 3 * t ^ 2 - t + 1 := by
    have hquad : 0 < 3 * t ^ 2 - t + 1 := by
      nlinarith [sq_nonneg (6 * t - 1)]
    nlinarith
  have hterm1 : 0 ≤ s ^ 2 * (t ^ 3 + t + 1) :=
    mul_nonneg (sq_nonneg s) (le_of_lt hc1)
  have hterm2 : 0 ≤ s * (t ^ 4 + t ^ 2 + 2 * t - 1) :=
    mul_nonneg hs (le_of_lt hc2)
  unfold A
  nlinarith

lemma F_le_sstar {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : F s ≤ F sstar := by
  have hA : 0 < A s sstar := A_pos hs.1 sstar_gt_nine_twentieths
  have hid : N sstar * D s - N s * D sstar = (s - sstar) ^ 2 * A s sstar := by
    have h := comparison_identity s sstar
    rw [sstar_root] at h
    simpa using h
  have hcross : N s * D sstar ≤ N sstar * D s := by
    have hnonneg : 0 ≤ (s - sstar) ^ 2 * A s sstar :=
      mul_nonneg (sq_nonneg (s - sstar)) (le_of_lt hA)
    nlinarith
  unfold F
  exact (div_le_div_iff₀ (D_pos s) (D_pos sstar)).2 hcross

lemma F_lt_sstar {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hne : s ≠ sstar) : F s < F sstar := by
  have hA : 0 < A s sstar := A_pos hs.1 sstar_gt_nine_twentieths
  have hdiff : s - sstar ≠ 0 := sub_ne_zero.mpr hne
  have hsquare : 0 < (s - sstar) ^ 2 := by
    simpa [pow_two] using (mul_self_pos.mpr hdiff)
  have hid : N sstar * D s - N s * D sstar = (s - sstar) ^ 2 * A s sstar := by
    have h := comparison_identity s sstar
    rw [sstar_root] at h
    simpa using h
  have hcross : N s * D sstar < N sstar * D s := by
    have hpos : 0 < (s - sstar) ^ 2 * A s sstar := mul_pos hsquare hA
    nlinarith
  unfold F
  exact (div_lt_div_iff₀ (D_pos s) (D_pos sstar)).2 hcross

theorem sstar_is_unique_maximizer :
    sstar ∈ Ioo (0 : ℝ) 1 ∧
      (∀ s ∈ Icc (0 : ℝ) 1, F s ≤ F sstar) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, F s = F sstar → s = sstar) := by
  refine ⟨sstar_mem, ?_, ?_⟩
  · intro s hs; exact F_le_sstar hs
  · intro s hs heq
    by_contra hne
    have hlt := F_lt_sstar hs hne
    linarith

def H (s : ℝ) : ℝ :=
  31 * s ^ 12 - 42 * s ^ 11 + 133 * s ^ 10 - 112 * s ^ 9
    + 191 * s ^ 8 - 86 * s ^ 7 + 103 * s ^ 6 + 12 * s ^ 5
    + 17 * s ^ 4 + 34 * s ^ 3 + 19 * s ^ 2 + 8 * s + 16

lemma elimination_identity (s : ℝ) : D s ^ 6 * Q (F s) = -P s ^ 2 * H s := by
  have hd : D s ≠ 0 := D_ne_zero s
  unfold F Q
  field_simp [hd]
  unfold N D P H
  ring

def gamma : ℝ := F sstar

theorem Q_gamma : Q gamma = 0 := by
  have h := elimination_identity sstar
  have hzero : D sstar ^ 6 * Q (F sstar) = 0 := by
    simpa [sstar_root] using h
  have hq : Q (F sstar) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 6 (D_ne_zero sstar))
  simpa [gamma] using hq

lemma deriv_Q (x : ℝ) : deriv Q x = Qder x := by
  unfold Q Qder
  simp
  ring

lemma Qder_shift (y : ℝ) :
    Qder ((6 : ℝ) / 5 + y) =
      864 * y ^ 5 + 2544 * y ^ 4 + (11808 / 5 : ℝ) * y ^ 3
        + (19788 / 25 : ℝ) * y ^ 2 + (22714 / 125 : ℝ) * y
        + (236814 / 3125 : ℝ) := by
  unfold Qder
  ring

lemma Qder_pos {x : ℝ} (hx : (6 : ℝ) / 5 ≤ x) : 0 < Qder x := by
  let y : ℝ := x - (6 : ℝ) / 5
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hxrepr : x = (6 : ℝ) / 5 + y := by dsimp [y]; ring
  rw [hxrepr, Qder_shift]
  positivity

lemma Q_strictMonoOn : StrictMonoOn Q (Ici ((6 : ℝ) / 5)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici ((6 : ℝ) / 5))
  · unfold Q
    fun_prop
  · intro x hx
    rw [deriv_Q]
    exact Qder_pos (le_of_lt (by simpa using hx))

lemma F_half : F ((1 : ℝ) / 2) = (26 : ℝ) / 21 := by norm_num [F, N, D]

lemma gamma_gt_six_fifths : (6 : ℝ) / 5 < gamma := by
  have hmax : F ((1 : ℝ) / 2) ≤ F sstar := F_le_sstar (by norm_num)
  rw [F_half] at hmax
  unfold gamma
  nlinarith

lemma Q_six_fifths : Q ((6 : ℝ) / 5) = -(49351 : ℝ) / 15625 := by norm_num [Q]
lemma Q_thirteen_tenths : Q ((13 : ℝ) / 10) = (88379 : ℝ) / 15625 := by norm_num [Q]

theorem Q_root_unique_above_six_fifths {x : ℝ}
    (hx : (6 : ℝ) / 5 ≤ x) (hQx : Q x = 0) : x = gamma := by
  have hgamma : (6 : ℝ) / 5 ≤ gamma := le_of_lt gamma_gt_six_fifths
  by_contra hne
  rcases lt_or_gt_of_ne hne with hxg | hgx
  · have hlt := Q_strictMonoOn hx hgamma hxg
    rw [hQx, Q_gamma] at hlt
    exact (lt_irrefl 0) hlt
  · have hlt := Q_strictMonoOn hgamma hx hgx
    rw [Q_gamma, hQx] at hlt
    exact (lt_irrefl 0) hlt

def gammaLower : ℝ :=
  (12395667407265985397097751707397283370137 : ℝ) / 10 ^ 40

def gammaUpper : ℝ :=
  (12395667407265985397097751707397283370138 : ℝ) / 10 ^ 40

lemma Q_gammaLower_neg : Q gammaLower < 0 := by norm_num [gammaLower, Q]
lemma Q_gammaUpper_pos : 0 < Q gammaUpper := by norm_num [gammaUpper, Q]

theorem gamma_exact_enclosure : gammaLower < gamma ∧ gamma < gammaUpper := by
  have hLdom : (6 : ℝ) / 5 ≤ gammaLower := by norm_num [gammaLower]
  have hUdom : (6 : ℝ) / 5 ≤ gammaUpper := by norm_num [gammaUpper]
  have hgdom : (6 : ℝ) / 5 ≤ gamma := le_of_lt gamma_gt_six_fifths
  constructor
  · by_contra hnot
    have hge : gamma ≤ gammaLower := le_of_not_gt hnot
    rcases eq_or_lt_of_le hge with heq | hlt
    · have hsign := Q_gammaLower_neg
      rw [← heq, Q_gamma] at hsign
      exact (lt_irrefl 0) hsign
    · have hmono := Q_strictMonoOn hgdom hLdom hlt
      rw [Q_gamma] at hmono
      nlinarith [Q_gammaLower_neg]
  · by_contra hnot
    have hle : gammaUpper ≤ gamma := le_of_not_gt hnot
    rcases eq_or_lt_of_le hle with heq | hlt
    · have hsign := Q_gammaUpper_pos
      rw [heq, Q_gamma] at hsign
      exact (lt_irrefl 0) hsign
    · have hmono := Q_strictMonoOn hUdom hgdom hlt
      rw [Q_gamma] at hmono
      nlinarith [Q_gammaUpper_pos]

def sLower : ℝ := (464087083432496056 : ℝ) / 10 ^ 18
def sUpper : ℝ := (464087083432496057 : ℝ) / 10 ^ 18

lemma P_sLower_pos : 0 < P sLower := by norm_num [sLower, P]
lemma P_sUpper_neg : P sUpper < 0 := by norm_num [sUpper, P]

theorem sstar_exact_enclosure : sLower < sstar ∧ sstar < sUpper := by
  have hLpos : 0 < sLower := by norm_num [sLower]
  have hUpos : 0 < sUpper := by norm_num [sUpper]
  constructor
  · by_contra hnot
    have hle : sstar ≤ sLower := le_of_not_gt hnot
    rcases eq_or_lt_of_le hle with heq | hlt
    · have hsign := P_sLower_pos
      rw [← heq, sstar_root] at hsign
      exact (lt_irrefl 0) hsign
    · have hanti := P_strictAntiOn_pos sstar_mem.1 hLpos hlt
      rw [sstar_root] at hanti
      nlinarith [P_sLower_pos]
  · by_contra hnot
    have hle : sUpper ≤ sstar := le_of_not_gt hnot
    rcases eq_or_lt_of_le hle with heq | hlt
    · have hsign := P_sUpper_neg
      rw [heq, sstar_root] at hsign
      exact (lt_irrefl 0) hsign
    · have hanti := P_strictAntiOn_pos hUpos sstar_mem.1 hlt
      rw [sstar_root] at hanti
      nlinarith [P_sUpper_neg]

def QZ : Polynomial ℤ :=
  C 144 * X ^ 6 - C 528 * X ^ 5 + C 648 * X ^ 4
    - C 220 * X ^ 3 - C 71 * X ^ 2 + C 42 * X - C 31

def QQ : Polynomial ℚ := QZ.map (Int.castRingHom ℚ)

theorem QQ_irreducible : Irreducible QQ := by
  sorry

theorem Q_has_exactly_two_real_roots : Set.encard {x : ℝ | Q x = 0} = 2 := by
  sorry

def RZ : Polynomial ℤ :=
  X ^ 6 - C 22 * X ^ 5 + C 162 * X ^ 4 - C 330 * X ^ 3
    - C 639 * X ^ 2 + C 2268 * X - C 10044

theorem six_mul_gamma_isIntegral : IsIntegral ℤ (6 * gamma) := by
  sorry

theorem six_is_minimal_integral_scaling {d : ℕ}
    (hd : IsIntegral ℤ ((d : ℝ) * gamma)) : 6 ∣ d := by
  sorry

end
end Raigorodskii
