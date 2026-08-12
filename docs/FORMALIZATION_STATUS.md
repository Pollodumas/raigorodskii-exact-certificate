# Formalization status

The Lean companion is a verified partial formalization of manuscript v0.9, pinned to Lean `v4.32.1` and Mathlib commit `520045ab14e26149ee970e2e617ca04b09bde5d6`.

## Kernel-checked in Lean 4

- positivity of the rational-function denominator;
- existence and uniqueness of the optimizer in `(0,1)`;
- uniqueness of the maximum on `[0,1]`;
- the exact elimination identity and `Q(γ_R)=0`;
- strict monotonicity of `Q` on `[6/5,∞)`;
- the exact 40-decimal rational enclosure of `γ_R`;
- the exact 18-decimal rational enclosure of the optimizer;
- algebraic integrality of `6γ_R`.

The published Lean source contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declarations. CI searches these tokens without requiring them to begin a line, builds the module, runs `lean/AxiomsAudit.lean`, rejects `sorryAx`, and uploads the `#print axioms` output.

## Certified outside Lean

The manuscript and both exact-arithmetic verifiers establish:

- irreducibility of the sextic over `ℚ`;
- the exact count of two real roots, by both Sturm theory and an elementary Bernstein-positivity certificate;
- minimality of the positive integral scaling factor `6`;
- the discriminants and modular factorization certificates;
- the `S₆` Galois-group and non-radicality conclusions.

These claims are not represented as completed Lean theorems in the published core.

## Build

```bash
lake update
lake exe cache get
lake build
lake env lean lean/AxiomsAudit.lean
```

The remaining formalization plan and the exact Mathlib interfaces available at the pinned revision are recorded in `FORMALIZATION_ROADMAP.md`.
