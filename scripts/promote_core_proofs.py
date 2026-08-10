#!/usr/bin/env python3
"""Promote only proof replacements that pass Lean locally in CI.

The script never weakens a theorem and never adds axioms.  Each candidate is
installed in a temporary working copy, checked with Lean, and kept only if the
whole certificate still compiles.
"""

from __future__ import annotations

import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
TARGET = ROOT / "lean" / "RaigorodskiiCertificate.lean"


def lean_ok() -> bool:
    proc = subprocess.run(
        ["lake", "env", "lean", str(TARGET.relative_to(ROOT))],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    print(proc.stdout)
    return proc.returncode == 0


def try_replace(label: str, old: str, new: str) -> bool:
    text = TARGET.read_text()
    if old not in text:
        print(f"[{label}] source pattern not found; skipping")
        return False
    candidate = text.replace(old, new, 1)
    TARGET.write_text(candidate)
    if lean_ok():
        print(f"[{label}] promoted")
        return True
    TARGET.write_text(text)
    print(f"[{label}] rejected by Lean")
    return False


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
  calc
    deriv P s = pPoly.derivative.eval s := by
      rw [hfun]
      simpa using (pPoly.deriv (x := s))
    _ = Pder s := by
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
  calc
    deriv Q x = qPoly.derivative.eval x := by
      rw [hfun]
      simpa using (qPoly.deriv (x := x))
    _ = Qder x := by
      simp [qPoly, Qder]
      ring
"""

INTEGRAL_OLD = """theorem six_mul_gamma_isIntegral : IsIntegral ℤ (6 * gamma) := by
  sorry
"""

INTEGRAL_NEW = """lemma RZ_monic : RZ.Monic := by
  norm_num [RZ]

lemma RZ_aeval_relation (x : ℝ) :
    aeval (6 * x) RZ = 324 * Q x := by
  simp [RZ, Q, aeval_def]
  ring

theorem six_mul_gamma_isIntegral : IsIntegral ℤ (6 * gamma) := by
  refine ⟨RZ, RZ_monic, ?_⟩
  rw [RZ_aeval_relation, Q_gamma, mul_zero]
"""


def main() -> int:
    changed = False
    changed |= try_replace("derivative P", DERIV_P_OLD, DERIV_P_NEW)
    changed |= try_replace("derivative Q", DERIV_Q_OLD, DERIV_Q_NEW)
    changed |= try_replace("integrality of 6 gamma", INTEGRAL_OLD, INTEGRAL_NEW)
    if changed:
        if not lean_ok():
            print("final combined certificate failed; refusing promotion", file=sys.stderr)
            return 1
        print("PROMOTED_CHANGES=1")
    else:
        print("PROMOTED_CHANGES=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
