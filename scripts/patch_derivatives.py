from pathlib import Path

path = Path("lean/RaigorodskiiCertificate.lean")
text = path.read_text(encoding="utf-8")

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
    (qder_marker, qder_insert, "polynomial models"),
    (old_p, new_p, "deriv_P"),
    (old_q, new_q, "deriv_Q"),
    (rz_marker, rz_insert, "integral model lemmas"),
    (old_integral, new_integral, "six_mul_gamma_isIntegral"),
]:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"Expected exactly one {label} block, found {count}")
    text = text.replace(old, new, 1)

path.write_text(text, encoding="utf-8")
print("Patched derivative and integrality proofs.")
