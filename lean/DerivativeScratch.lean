import Mathlib

set_option autoImplicit false

namespace DerivativeScratch

open Polynomial

noncomputable section

def P (s : ℝ) : ℝ :=
  1 - 2 * s + 2 * s ^ 2 - 4 * s ^ 3 - 2 * s ^ 4 - s ^ 6

def Pder (s : ℝ) : ℝ :=
  -2 + 4 * s - 12 * s ^ 2 - 8 * s ^ 3 - 6 * s ^ 5

def pPoly : Polynomial ℝ :=
  C 1 - C 2 * X + C 2 * X ^ 2 - C 4 * X ^ 3 - C 2 * X ^ 4 - X ^ 6

lemma P_eq_eval (s : ℝ) : P s = pPoly.eval s := by
  simp [P, pPoly]
  ring

lemma deriv_P (s : ℝ) : deriv P s = Pder s := by
  have hfun : P = fun x => pPoly.eval x := by
    funext x
    exact P_eq_eval x
  rw [hfun]
  rw [Polynomial.deriv]
  simp [pPoly, Pder]
  ring


def Q (x : ℝ) : ℝ :=
  144 * x ^ 6 - 528 * x ^ 5 + 648 * x ^ 4 - 220 * x ^ 3
    - 71 * x ^ 2 + 42 * x - 31

def Qder (x : ℝ) : ℝ :=
  864 * x ^ 5 - 2640 * x ^ 4 + 2592 * x ^ 3
    - 660 * x ^ 2 - 142 * x + 42

def qPoly : Polynomial ℝ :=
  C 144 * X ^ 6 - C 528 * X ^ 5 + C 648 * X ^ 4 - C 220 * X ^ 3
    - C 71 * X ^ 2 + C 42 * X - C 31

lemma Q_eq_eval (x : ℝ) : Q x = qPoly.eval x := by
  simp [Q, qPoly]
  ring

lemma deriv_Q (x : ℝ) : deriv Q x = Qder x := by
  have hfun : Q = fun y => qPoly.eval y := by
    funext y
    exact Q_eq_eval y
  rw [hfun]
  rw [Polynomial.deriv]
  simp [qPoly, Qder]
  ring

end
end DerivativeScratch
