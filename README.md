# Exact algebraic certificate for the Raigorodskii lower-bound constant

This repository contains a short mathematical note, two independent exact-arithmetic verifiers, and a Lean 4 formalization of the analytic and real-algebraic core.

For Naslund's one-variable formulation at `(k,m,l) = (1,1,3)`, define

\[
F(s)=\frac{1+s+s^3}{1+s^2+s^4}, \qquad 0<s<1.
\]

Its maximum `gamma_R` is the unique real root greater than `1.2` of

\[
144x^6-528x^5+648x^4-220x^3-71x^2+42x-31.
\]

The exact certified enclosure is

\[
1.2395667407265985397097751707397283370137
< \gamma_R <
1.2395667407265985397097751707397283370138.
\]

## Contents

- `paper/`: manuscript v0.8 in PDF and LaTeX, plus its changelog.
- `verification/verify_raigorodskii_certificate_v0_8.py`: exact SymPy verifier.
- `verification/verify_raigorodskii_certificate_stdlib_v0_8.py`: independent verifier using only the Python standard library.
- `docs/Raigorodskii_Exact_Certificate_Audit_v0_8.md`: adversarial audit and reproducibility record.
- `lean/RaigorodskiiCertificate.lean`: kernel-checked Lean core with no placeholder proofs.

## Exact verification

```bash
python -m pip install -r verification/requirements_raigorodskii_v0_8.txt
python verification/verify_raigorodskii_certificate_v0_8.py
python verification/verify_raigorodskii_certificate_stdlib_v0_8.py
sha256sum -c SHA256SUMS
```

The two programs independently check the elimination polynomial, irreducibility, exact root isolation, the two-real-root count, the integral model for `6 gamma_R`, the minimal scaling factor `6`, and the modular certificates used for the `S_6` Galois-group conclusion.

## Lean status

```bash
lake update
lake exe cache get
lake build
```

The Lean module formalizes:

- positivity of the denominator;
- existence and uniqueness of the optimizer;
- uniqueness of the maximizer on `[0,1]`;
- the elimination identity and `Q(gamma_R)=0`;
- strict monotonicity of `Q` above `6/5`;
- exact rational enclosures of the optimizer and the constant;
- algebraic integrality of `6 gamma_R`.

It deliberately does **not** claim a complete formalization of irreducibility over `Q`, the global two-real-root count, minimality of the scaling factor, or the Galois group. Those statements remain certified by the independent exact-arithmetic programs and proved in the manuscript.

## Scope

The result does not improve Raigorodskii's asymptotic lower bound. It gives an explicit exact algebraic certificate for the numerical constant recovered through Naslund's formulation.

## Provenance and AI assistance

Joaquin Paz Marchese directed a multi-model AI-assisted research process combining mathematical sources, exact computation, adversarial review, and repeated independent cross-checking. The manuscript contains a detailed disclosure. AI systems are not listed as authors.
