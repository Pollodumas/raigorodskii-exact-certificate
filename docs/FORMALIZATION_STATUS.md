# Formalization status

The Lean companion is a verified partial formalization of the manuscript.

## Kernel-checked in Lean 4

- positivity of the rational-function denominator;
- existence and uniqueness of the optimizer in `(0,1)`;
- uniqueness of the maximum on `[0,1]`;
- the exact elimination identity and `Q(γ_R)=0`;
- strict monotonicity of `Q` on `[6/5,∞)`;
- the exact 40-decimal rational enclosure of `γ_R`;
- the exact 18-decimal rational enclosure of the optimizer;
- algebraic integrality of `6γ_R`.

The published Lean source contains no `sorry`, `admit`, or added axioms.

## Certified outside Lean

The manuscript and both exact-arithmetic verifiers establish:

- irreducibility of the sextic over `ℚ`;
- the exact count of two real roots;
- minimality of the positive integral scaling factor `6`;
- the modular factorization certificates and the `S₆` Galois-group conclusion.

These claims are not represented as completed Lean theorems in the published core.

## Build

```bash
lake update
lake exe cache get
lake build
```
