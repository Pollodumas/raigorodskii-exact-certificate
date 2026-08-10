from pathlib import Path

path = Path("lean/RaigorodskiiCertificate.lean")
text = path.read_text(encoding="utf-8")

marker = """def Qder (x : ℝ) : ℝ :=
  864 * x ^ 5 - 2640 * x ^ 4 + 2592 * x ^ 3
    - 660 * x ^ 2 - 142 * x + 42
"""
insert = marker + """

def pPoly : Polynomial ℝ :=
  C 1 - C 2 * X + C 2 * X ^ 2 - C 4 * X ^ 3 - C 2 * X ^ 4 - X ^ 6

def qPoly : Polynomial ℝ :=
  C 144 * X ^ 6 - C 528 * X ^ 5 + C 648 * X ^ 4 - C 220 * X ^ 3
    - C 71 * X ^ 2 + C 42 * X - C 31

lemma P_eq_eval (s : ℝ) : P s = pPoly.eval s := by
  simp [P, pPoly]
  ring

lemma Q_eq_eval (x : ℝ) : Q x = qPoly.eval x := by
  simp [Q, qPoly]
  ring
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
"""

for old, new, label in [
    (marker, insert, "polynomial models"),
    (old_p, new_p, "deriv_P"),
    (old_q, new_q, "deriv_Q"),
]:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"Expected exactly one {label} block, found {count}")
    text = text.replace(old, new, 1)

path.write_text(text, encoding="utf-8")
print("Patched polynomial derivative proofs.")
