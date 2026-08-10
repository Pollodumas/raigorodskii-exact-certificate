# Raigorodskii exact certificate

Exact algebraic certification and Lean formalization of the one-variable constant appearing in the Raigorodskii lower bound for the chromatic number of Euclidean space, as recovered through Näslund's formulation.

## Current status

The mathematical note is at draft **v0.8**. The exact-computation package has two independent verification programs and checksums. A Lean 4 + Mathlib formalization is in progress.

The Lean development currently targets the elementary real-algebraic core:

- positivity of the denominator;
- existence and uniqueness of the optimizer `sstar`;
- uniqueness of the maximizer of the rational function;
- the direct elimination identity yielding `Q(gamma)=0`;
- strict monotonicity of `Q` above `6/5`;
- exact enclosures of `gamma` and `sstar`;
- the integral model for `6 * gamma`.

The initial autoformalization received from Ingo Althöfer contained four `sorry` declarations and had not been compiled. This repository pins Lean and Mathlib and uses CI so that every subsequent claim is checked by the Lean kernel.

## Formalization gaps being closed

1. irreducibility of the sextic over `ℚ`;
2. exact count of the real roots;
3. algebraic integrality of `6 * gamma`;
4. minimality of the positive integral scaling factor `6`.

The Galois-group / non-solvability-by-radicals corollary is treated as a separate later module.

## Build

```bash
lake update
lake exe cache get
lake build
```

The CI workflow runs the same build against the pinned toolchain.

## Paper and exact verification

See `paper/` and `verification/`.

## Authorship and provenance

Joaquín Paz Marchese. The project uses a multi-model AI-assisted research workflow together with exact computation and adversarial cross-checking. AI systems are not listed as authors.
