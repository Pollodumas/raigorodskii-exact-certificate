# Formalization audit

The initial package supplied by Ingo Althöfer contained only `RaigorodskiiCertificate.lean` and `README_Raigorodskii_Lean.md`. It explicitly stated that the Lean source had not been compiled.

This repository pins Lean and Mathlib, runs `lake build` in CI, and separates compiler/API failures from genuine mathematical proof obligations.

## Initial proof obligations

1. irreducibility of `Q` over `ℚ`;
2. exact count of the two real roots;
3. algebraic integrality of `6 * gamma`;
4. minimality of the positive integral scaling factor `6`.

## Work order

1. Compile the existing non-`sorry` core unchanged as far as possible.
2. Fix only genuine Lean API/syntax incompatibilities exposed by the compiler.
3. Close `6 * gamma` integrality from the explicit monic polynomial `RZ`.
4. Formalize irreducibility from the mod-5 finite certificate and Gauss's lemma.
5. Formalize the real-root count from a compact Sturm certificate or a simpler exact alternative.
6. Derive scaling minimality from the identified minimal polynomial.
7. Treat the Galois-group / radicals paragraph as an optional separate module.

No claim is considered formally verified until the corresponding declaration compiles without `sorry`.
