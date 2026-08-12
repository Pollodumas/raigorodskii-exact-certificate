# Verification report

**Artifact:** *An Exact Algebraic Certificate for the Raigorodskii Lower-Bound Constant*, v0.9  
**Status:** exact-computation, formalization, and adversarial-review report; not peer review

## 1. Certified object

For

\[
F(s)=\frac{1+s+s^3}{1+s^2+s^4},\qquad 0<s<1,
\]

the manuscript defines \(\gamma_{\mathrm R}=\max F(s)\). The optimizer is the unique root in \((0,1)\) of

\[
P(s)=1-2s+2s^2-4s^3-2s^4-s^6.
\]

Eliminating \(s\) gives

\[
Q(x)=144x^6-528x^5+648x^4-220x^3-71x^2+42x-31,
\]

and

\[
1.2395667407265985397097751707397283370137
<\gamma_{\mathrm R}<
1.2395667407265985397097751707397283370138.
\]

## 2. Exact checks

The SymPy verifier and the independent standard-library verifier check, using exact arithmetic:

1. the derivative identity for \(F\) and the exact positivity decomposition of \(-P'\);
2. positivity of the denominator;
3. the full symbolic Sylvester resultant \(\operatorname{Res}_s(P,xD-N)=3Q(x)\);
4. primitivity and irreducibility of \(Q\) using a Rabin certificate modulo `5`;
5. exact optimizer and constant enclosures of widths \(10^{-18}\) and \(10^{-40}\);
6. an exact Sturm count of the two real roots;
7. an independent elementary root-count certificate using positive power and Bernstein coefficients;
8. strict monotonicity of \(Q\) on \([6/5,\infty)\);
9. the monic integral model
   \[
   R(y)=y^6-22y^5+162y^4-330y^3-639y^2+2268y-10044;
   \]
10. minimality of the positive integral scaling factor `6`;
11. the discriminants of \(Q\) and \(R\);
12. the modular factorizations at `61` and `107` and all Dedekind hypotheses;
13. that `61` and `107` are the least unramified primes with patterns `[1,5]` and `[1,1,1,1,2]`;
14. the group-theoretic conclusion \(\operatorname{Gal}(Q/\mathbb Q)\cong S_6\).

The standard-library verifier computes its symbolic resultant by fraction-free Bareiss elimination over \(\mathbb Z[x]\). Its finite-field, Sturm, discriminant, Bernstein, and permutation-group routines do not call a computer-algebra system.

All checks use explicit exceptions rather than Python `assert`. The scripts produce the same output under normal execution and `python -O`.

## 3. Mutation testing

`mutation_test_harness_v0_9.py` verifies normal and optimized-mode baselines and injects directed corruptions into:

- the defining sextic;
- the 40-decimal enclosure;
- the Bernstein certificate;
- the minimal Dedekind-prime claim.

All eight corruptions must fail in normal execution; representative corruptions are repeated under optimized execution. This does not solve the intrinsic self-test limitation that deleting a check cannot be detected by that same check. Independence of implementations and external review remain necessary.

## 4. Expected output

```text
All exact certificate checks passed.
Independent standard-library audit passed.
Full symbolic resultant coefficients (low first): [-93, 126, -213, -660, 1944, -1584, 432]
disc(R): 1618922648989369652871168
Elementary two-root positivity certificate: True
Galois group order: 720
Least primes for cycle patterns [1,5] and [1,1,1,1,2]: 61 107
Orders from <6-cycle, transposition> over all transpositions: [24, 72, 720]
Least positive integral scaling factor: 6
```

No floating-point approximation is used in a logical step.

## 5. Lean companion

The Lean 4 module is pinned to Lean `v4.32.1` and Mathlib commit `520045ab14e26149ee970e2e617ca04b09bde5d6`. It compiles without placeholders or added axioms and formalizes the analytic core, exact enclosures, and integrality of `6γ_R`.

CI performs a non-line-anchored token scan, builds the module, executes `lean/AxiomsAudit.lean`, rejects `sorryAx`, and uploads the `#print axioms` log. The arithmetic and Galois layers remain outside the claimed Lean scope.

## 6. Adversarial review incorporated into v0.9

An independent multi-engine review dated 11 August 2026 classified the mathematics as sound and publication-ready after minor tooling edits. It rederived the central claims using an independent SymPy path, a from-scratch exact Python engine, and PARI/GP. Its required patches are incorporated here:

- checks remain active under `python -O`;
- the Lean placeholder guard is not line-anchored and CI records axiom output;
- the quadratic discriminant check is tied explicitly to the decomposition of `-P'`.

The review also supplied the elementary Bernstein root certificate and the verified Mathlib roadmap now included in the repository.

## 7. Reproduction

```bash
python -m pip install -r verification/requirements_raigorodskii_v0_9.txt
python verification/verify_raigorodskii_certificate_v0_9.py
python verification/verify_raigorodskii_certificate_stdlib_v0_9.py
python verification/mutation_test_harness_v0_9.py
lake update
lake exe cache get
lake build
lake env lean lean/AxiomsAudit.lean
sha256sum -c SHA256SUMS
```

## 8. Limitations

- The manuscript has not been peer reviewed.
- Bibliographic priority remains unresolved after a documented but non-exhaustive search.
- The identification with Raigorodskii's lower-bound base follows Näslund's stated recovery at `(k,m,ℓ)=(1,1,3)`; the original 2000 construction is not re-derived.
- The arXiv v2 reciprocal-display issue has been checked; the journal rendering remains unverified.
- The result certifies a known lower-bound base. It does not improve the asymptotic chromatic bound or solve Erdős Problem 704.
