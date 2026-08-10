# Formalization status

The Lean companion is a verified partial formalization, not a formalization of every theorem in the manuscript.

## Kernel-checked in Lean 4

- positivity of the rational-function denominator;
- existence and uniqueness of the optimizer in `(0,1)`;
- uniqueness of the maximum on `[0,1]`;
- the exact elimination identity and the sextic relation `Q(gamma_R)=0`;
- strict monotonicity of `Q` on `[6/5, infinity)`;
- the 40-decimal rational enclosure of `gamma_R`;
- the 18-decimal rational enclosure of the optimizer;
- algebraic integrality of `6 gamma_R`.

The distributed core contains no `sorry` declarations or added axioms.

## Certified outside Lean

The manuscript and both exact-arithmetic verifiers establish:

- irreducibility of the sextic over `Q`;
- the exact count of two real roots;
- minimality of the positive integral scaling factor `6`;
- the modular factorization certificates and the `S_6` Galois-group conclusion.

These claims are deliberately not represented as completed Lean theorems in the publication core.
