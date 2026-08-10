from pathlib import Path

path = Path("lean/RaigorodskiiCertificate.lean")
text = path.read_text(encoding="utf-8")

old_header = """* Four declarations remain `sorry`:
  (1) irreducibility of the sextic over Q from the finite-field certificate;
  (2) the exact count of all real roots;
  (3) algebraic integrality of 6 * gamma in the chosen `IsIntegral` interface;
  (4) minimality of the scaling factor 6.
"""
new_header = """* Two declarations remain `sorry`:
  (1) irreducibility of the sextic over Q from the finite-field certificate;
  (2) minimality of the scaling factor 6.
"""

qder_marker = """def Qder (x : ℝ) : ℝ :=
  864 * x ^ 5 - 2640 * x ^ 4 + 2592 * x ^ 3
    - 660 * x ^ 2 - 142 * x + 42
"""
qder_insert = qder_marker + """

def pPoly : Polynomial ℝ :=
  C 1 - C 2 * X + C 2 * X ^ 2 - C 4 * X ^ 3 - C 2 * X ^ 4 - X ^ 6

def qPoly : Polynomial ℝ :=
  C 144 * X ^ 6 - C 528 * X ^ 5 + C 648 * X ^ 4 - C 220 * X ^ 3
    - C 71 * X ^ 2 + C 42 * X - C 31

lemma P_eq_eval (s : ℝ) : P s = pPoly.eval s := by
  simp [P, pPoly]

lemma Q_eq_eval (x : ℝ) : Q x = qPoly.eval x := by
  simp [Q, qPoly]
"""

old_p = """lemma deriv_P (s : ℝ) : deriv P s = Pder s := by
  unfold P Pder
  simp
  ring
"""
new_p = """lemma deriv_P (s : ℝ) : deriv P s = Pder s := by
  have hfun : P = fun x => pPoly.eval x := by
    funext x
    exact P_eq_eval x
  rw [hfun]
  rw [Polynomial.deriv]
  simp [pPoly, Pder]
  ring
"""

old_q = """lemma deriv_Q (x : ℝ) : deriv Q x = Qder x := by
  unfold Q Qder
  simp
  ring
"""
new_q = """lemma deriv_Q (x : ℝ) : deriv Q x = Qder x := by
  have hfun : Q = fun y => qPoly.eval y := by
    funext y
    exact Q_eq_eval y
  rw [hfun]
  rw [Polynomial.deriv]
  simp [qPoly, Qder]
  ring
"""

old_roots = """theorem Q_has_exactly_two_real_roots : Set.encard {x : ℝ | Q x = 0} = 2 := by
  sorry
"""
new_roots = """lemma Qder_left_shift (y : ℝ) :
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
    by_cases hu0 : u = 0
    · right
      rw [hu0, zero_add] at huv
      exact huv
    · left
      exact lt_of_le_of_ne hu (Ne.symm hu0)
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
    nlinarith
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

theorem Q_has_exactly_two_real_roots : Set.encard {x : ℝ | Q x = 0} = 2 := by
  rw [roots_set_eq]
  have hnot : rneg ∉ ({gamma} : Set ℝ) := by
    simpa using rneg_ne_gamma
  rw [Set.encard_insert_of_notMem hnot, Set.encard_singleton]
  norm_num
"""

rz_marker = """def RZ : Polynomial ℤ :=
  X ^ 6 - C 22 * X ^ 5 + C 162 * X ^ 4 - C 330 * X ^ 3
    - C 639 * X ^ 2 + C 2268 * X - C 10044
"""
rz_insert = rz_marker + """

lemma RZ_monic : RZ.Monic := by
  unfold RZ
  monicity <;> norm_num

lemma RZ_eval_identity (x : ℝ) :
    eval₂ (algebraMap ℤ ℝ) (6 * x) RZ = 324 * Q x := by
  simp [RZ, Q]
  ring
"""

old_integral = """theorem six_mul_gamma_isIntegral : IsIntegral ℤ (6 * gamma) := by
  sorry
"""
new_integral = """theorem six_mul_gamma_isIntegral : IsIntegral ℤ (6 * gamma) := by
  refine ⟨RZ, RZ_monic, ?_⟩
  rw [RZ_eval_identity, Q_gamma]
  norm_num
"""

for old, new, label in [
    (old_header, new_header, "status header"),
    (qder_marker, qder_insert, "polynomial models"),
    (old_p, new_p, "deriv_P"),
    (old_q, new_q, "deriv_Q"),
    (old_roots, new_roots, "exact real-root count"),
    (rz_marker, rz_insert, "integral model lemmas"),
    (old_integral, new_integral, "six_mul_gamma_isIntegral"),
]:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"Expected exactly one {label} block, found {count}")
    text = text.replace(old, new, 1)

path.write_text(text, encoding="utf-8")
print("Patched derivative, real-root, and integrality proofs.")
