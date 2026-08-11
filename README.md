# Exact algebraic certificate for the Raigorodskii lower-bound constant

This repository contains a short mathematical note, two independent exact-arithmetic verifiers, and a Lean 4 formalization of the analytic and real-algebraic core.

Starting from Näslund's one-variable formulation at `(k,m,ℓ) = (1,1,3)`, define

\[
F(s)=\frac{1+s+s^3}{1+s^2+s^4}, \qquad 0<s<1.
\]

Its maximum \(\gamma_{\mathrm R}\) is the unique real root greater than \(1.2\) of

\[
144x^6-528x^5+648x^4-220x^3-71x^2+42x-31.
\]

The exact certified enclosure is

\[
1.2395667407265985397097751707397283370137
< \gamma_{\mathrm R} <
1.2395667407265985397097751707397283370138.
\]

## Repository contents

- `paper/`: manuscript v0.8 in PDF and LaTeX.
- `verification/`: independent SymPy and Python-standard-library verifiers.
- `lean/RaigorodskiiCertificate.lean`: placeholder-free Lean core.
- `docs/VERIFICATION_REPORT.md`: final exact-verification report.
- `docs/FORMALIZATION_STATUS.md`: precise scope of the Lean companion.
- `dist/Raigorodskii_Exact_Certificate_v0_8.zip`: complete reproducibility package.
- `SHA256SUMS`: hashes for the published source and verification artifacts.

## Exact verification

```bash
python -m pip install -r verification/requirements_raigorodskii_v0_8.txt
python verification/verify_raigorodskii_certificate_v0_8.py
python verification/verify_raigorodskii_certificate_stdlib_v0_8.py
sha256sum -c SHA256SUMS
```

The two programs independently verify the elimination polynomial, irreducibility certificate, exact root isolation, the two-real-root count, the integral model for \(6\gamma_{\mathrm R}\), minimality of the scaling factor `6`, and the modular certificates used for the \(S_6\) Galois-group conclusion.

## Lean verification

```bash
lake update
lake exe cache get
lake build
```

The Lean module formalizes:

- positivity of the denominator;
- existence and uniqueness of the optimizer;
- uniqueness of the maximizer on `[0,1]`;
- the elimination identity and `Q(γ_R)=0`;
- strict monotonicity of `Q` above `6/5`;
- exact rational enclosures of the optimizer and the constant;
- algebraic integrality of \(6\gamma_{\mathrm R}\).

It does not claim a complete Lean formalization of irreducibility over \(\mathbb Q\), the global two-real-root count, minimality of the scaling factor, or the Galois group. Those claims are proved in the manuscript and checked by both exact-arithmetic verifiers.

## Scope and status

This result does not improve Raigorodskii's asymptotic chromatic lower bound and does not solve Erdős Problem 704. It makes the numerical lower-bound base algebraically explicit and independently reproducible.

The manuscript is a public preprint, not a peer-reviewed publication. Bibliographic priority remains subject to specialist review.

## Provenance and AI assistance

Joaquín Paz Marchese directed a multi-model AI-assisted research process combining mathematical sources, exact computation, adversarial review, and repeated independent cross-checking. The manuscript contains the full disclosure. AI systems are not listed as authors.
