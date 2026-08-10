#!/usr/bin/env python3
"""Promote the publication-ready, kernel-checked Lean core.

The script rewrites only exact source blocks that are present in the original
autoformalization, checks the resulting module with Lean, and leaves the tree
untouched if the check fails.  It removes statements that are not yet
formalized rather than retaining `sorry` placeholders.
"""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
TARGET = ROOT / "lean" / "RaigorodskiiCertificate.lean"


def run_lean(path: pathlib.Path) -> bool:
    proc = subprocess.run(
        ["lake", "env", "lean", str(path.relative_to(ROOT))],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    print(proc.stdout)
    return proc.returncode == 0


def replace_once(text: str, label: str, old: str, new: str) -> str:
    count = text.count(old)
    if count == 0:
        print(f"[{label}] source block already absent or already promoted")
        return text
    if count != 1:
        raise RuntimeError(f"[{label}] expected one source block, found {count}")
    print(f"[{label}] applying")
    return text.replace(old, new, 1)


HEADER_OLD = """STATUS
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
"""

HEADER_NEW = """STATUS
* This module compiles without placeholder proofs.
* It kernel-checks the analytic and real-algebraic core: positivity of the
  denominator, existence and uniqueness of the maximizer, the elimination
  identity, the sextic relation, strict monotonicity, exact rational
  enclosures, and algebraic integrality of `6 * gamma`.
* Irreducibility over `ℚ`, the global real-root count, minimality of the scaling
  factor `6`, and the Galois-group corollary are kept outside this core module
  unless and until their separate Lean developments compile without axioms.
"""

P_EVAL_OLD = """lemma P_eq_eval (s : ℝ) : P s = pPoly.eval s := by
  simp [P, pPoly]
  ring
"""
P_EVAL_NEW = """lemma P_eq_eval (s : ℝ) : P s = pPoly.eval s := by
  simp [P, pPoly]
"""

Q_EVAL_OLD = """lemma Q_eq_eval (x : ℝ) : Q x = qPoly.eval x := by
  simp [Q, qPoly]
  ring
"""
Q_EVAL_NEW = """lemma Q_eq_eval (x : ℝ) : Q x = qPoly.eval x := by
  simp [Q, qPoly]
"""

DERIV_P_OLD = """lemma deriv_P (s : ℝ) : deriv P s = Pder s := by
  have hfun : P = fun x => pPoly.eval x := by
    funext x
    exact P_eq_eval x
  rw [hfun]
  simpa [pPoly, Pder] using (pPoly.hasDerivAt s).deriv
"""
DERIV_P_NEW = """lemma deriv_P (s : ℝ) : deriv P s = Pder s := by
  have hfun : P = fun x => pPoly.eval x := by
    funext x
    exact P_eq_eval x
  rw [hfun]
  rw [Polynomial.deriv]
  simp [pPoly, Pder]
  ring
"""

DERIV_Q_OLD = """lemma deriv_Q (x : ℝ) : deriv Q x = Qder x := by
  have hfun : Q = fun y => qPoly.eval y := by
    funext y
    exact Q_eq_eval y
  rw [hfun]
  simpa [qPoly, Qder] using (qPoly.hasDerivAt x).deriv
"""
DERIV_Q_NEW = """lemma deriv_Q (x : ℝ) : deriv Q x = Qder x := by
  have hfun : Q = fun y => qPoly.eval y := by
    funext y
    exact Q_eq_eval y
  rw [hfun]
  rw [Polynomial.deriv]
  simp [qPoly, Qder]
  ring
"""

UNFORMALIZED_OLD = """theorem QQ_irreducible : Irreducible QQ := by
  sorry

theorem Q_has_exactly_two_real_roots : Set.encard {x : ℝ | Q x = 0} = 2 := by
  sorry

"""
UNFORMALIZED_NEW = """/-!
The accompanying exact-arithmetic verifiers certify irreducibility of `QQ` and
that `Q` has exactly two real roots.  These claims are not asserted as theorems
in this core module; the real-root statement is developed separately.
-/

"""

INTEGRAL_OLD = """theorem six_mul_gamma_isIntegral : IsIntegral ℤ (6 * gamma) := by
  sorry
"""
INTEGRAL_NEW = """lemma RZ_monic : RZ.Monic := by
  unfold RZ
  monicity <;> norm_num

lemma RZ_eval_identity (x : ℝ) :
    eval₂ (algebraMap ℤ ℝ) (6 * x) RZ = 324 * Q x := by
  simp [RZ, Q]
  ring

theorem six_mul_gamma_isIntegral : IsIntegral ℤ (6 * gamma) := by
  refine ⟨RZ, RZ_monic, ?_⟩
  rw [RZ_eval_identity, Q_gamma]
  norm_num
"""

MINIMAL_OLD = """theorem six_is_minimal_integral_scaling {d : ℕ}
    (hd : IsIntegral ℤ ((d : ℝ) * gamma)) : 6 ∣ d := by
  sorry
"""
MINIMAL_NEW = """/-!
Minimality of the positive integral scaling factor `6` is certified in the
paper and by the exact-arithmetic verification programs, but is not asserted
as a Lean theorem in this core module.
-/
"""


def main() -> int:
    original = TARGET.read_text(encoding="utf-8")
    candidate = original
    for label, old, new in [
        ("status header", HEADER_OLD, HEADER_NEW),
        ("P evaluation", P_EVAL_OLD, P_EVAL_NEW),
        ("Q evaluation", Q_EVAL_OLD, Q_EVAL_NEW),
        ("derivative P", DERIV_P_OLD, DERIV_P_NEW),
        ("derivative Q", DERIV_Q_OLD, DERIV_Q_NEW),
        ("unformalized declarations", UNFORMALIZED_OLD, UNFORMALIZED_NEW),
        ("integrality of 6 gamma", INTEGRAL_OLD, INTEGRAL_NEW),
        ("minimal scaling placeholder", MINIMAL_OLD, MINIMAL_NEW),
    ]:
        candidate = replace_once(candidate, label, old, new)

    if re.search(r"(?m)^\s*sorry\s*$", candidate):
        print("publication core still contains a placeholder proof", file=sys.stderr)
        return 1

    if candidate == original:
        print("No source changes required.")
        return 0

    TARGET.write_text(candidate, encoding="utf-8")
    if not run_lean(TARGET):
        TARGET.write_text(original, encoding="utf-8")
        print("Publication core failed Lean; restored original source.", file=sys.stderr)
        return 1

    print("Publication core compiled and contains no placeholder proofs.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
