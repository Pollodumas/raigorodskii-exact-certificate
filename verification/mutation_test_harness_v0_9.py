#!/usr/bin/env python3
"""Directed mutation tests for both exact verifiers.

This harness checks that the v0.9 verifiers behave identically in normal and
optimized (`python -O`) execution, then injects representative corruptions and
requires every corruption to be rejected in both modes.

A mutation harness cannot detect deletion of the check that is supposed to
catch a mutation. Its role is therefore complementary to the independent
implementations, Lean checks, and external review.
"""
from __future__ import annotations

from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent

MUTATIONS = {
    "sympy_Q_constant": (
        "verify_raigorodskii_certificate_v0_9.py",
        "+ 42 * x - 31\n    R =",
        "+ 42 * x - 30\n    R =",
    ),
    "sympy_gamma_lower_endpoint": (
        "verify_raigorodskii_certificate_v0_9.py",
        "70137, 10 ** 40",
        "70136, 10 ** 40",
    ),
    "sympy_bernstein_coefficient": (
        "verify_raigorodskii_certificate_v0_9.py",
        "sp.Rational(90089305534379, 976562500000000)",
        "sp.Rational(90089305534380, 976562500000000)",
    ),
    "sympy_cycle_prime": (
        "verify_raigorodskii_certificate_v0_9.py",
        "first_five_cycle_prime == 61",
        "first_five_cycle_prime == 59",
    ),
    "stdlib_Q_constant": (
        "verify_raigorodskii_certificate_stdlib_v0_9.py",
        "Q_desc = [144, -528, 648, -220, -71, 42, -31]",
        "Q_desc = [144, -528, 648, -220, -71, 42, -30]",
    ),
    "stdlib_gamma_lower_endpoint": (
        "verify_raigorodskii_certificate_stdlib_v0_9.py",
        "70137, 10 ** 40",
        "70136, 10 ** 40",
    ),
    "stdlib_bernstein_coefficient": (
        "verify_raigorodskii_certificate_stdlib_v0_9.py",
        "Fraction(90089305534379, 976562500000000)",
        "Fraction(90089305534380, 976562500000000)",
    ),
    "stdlib_cycle_prime": (
        "verify_raigorodskii_certificate_stdlib_v0_9.py",
        "first_five_cycle_prime == 61",
        "first_five_cycle_prime == 59",
    ),
}

OPTIMIZED_MUTATIONS = {
    "sympy_Q_constant",
    "sympy_bernstein_coefficient",
    "stdlib_gamma_lower_endpoint",
    "stdlib_cycle_prime",
}


def run(arguments: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        arguments,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )


def main() -> int:
    failures: list[str] = []
    files = sorted({entry[0] for entry in MUTATIONS.values()})

    print("BASELINES")
    for filename in files:
        normal = run([sys.executable, str(ROOT / filename)])
        optimized = run([sys.executable, "-O", str(ROOT / filename)])
        normal_ok = normal.returncode == 0
        optimized_ok = optimized.returncode == 0
        outputs_match = normal.stdout == optimized.stdout
        print(
            filename,
            f"normal={'PASS' if normal_ok else 'FAIL'}",
            f"optimized={'PASS' if optimized_ok else 'FAIL'}",
            f"same_output={outputs_match}",
        )
        if not normal_ok:
            failures.append(f"normal baseline failed: {filename}\n{normal.stdout}")
        if not optimized_ok:
            failures.append(f"optimized baseline failed: {filename}\n{optimized.stdout}")
        if not outputs_match:
            failures.append(f"normal and optimized outputs differ: {filename}")

    print("\nDIRECTED MUTATIONS")
    for name, (filename, old, new) in MUTATIONS.items():
        source = (ROOT / filename).read_text(encoding="utf-8")
        occurrences = source.count(old)
        if occurrences != 1:
            print(name, f"HARNESS ERROR: expected one anchor, found {occurrences}")
            failures.append(f"invalid mutation anchor: {name}")
            continue

        with tempfile.TemporaryDirectory() as temporary_directory:
            mutated_path = Path(temporary_directory) / filename
            mutated_path.write_text(source.replace(old, new, 1), encoding="utf-8")
            results = {"normal": run([sys.executable, str(mutated_path)])}
            if name in OPTIMIZED_MUTATIONS:
                results["optimized"] = run(
                    [sys.executable, "-O", str(mutated_path)]
                )
            detected = {mode: result.returncode != 0 for mode, result in results.items()}
            print(
                name,
                " ".join(
                    f"{mode}={'DETECTED' if value else 'MISSED'}"
                    for mode, value in detected.items()
                ),
            )
            for mode, value in detected.items():
                if not value:
                    failures.append(f"mutation missed in {mode} mode: {name}")

    if failures:
        print("\nFAILURES")
        for failure in failures:
            print(failure)
        return 1

    print("\nAll directed mutations were detected; representative mutations also passed optimized-mode testing.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
