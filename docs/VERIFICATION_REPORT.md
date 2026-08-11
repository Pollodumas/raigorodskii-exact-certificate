# Verification report

**Artifact:** *An Exact Algebraic Certificate for the Raigorodskii Lower-Bound Constant*, v0.8  
**Status:** exact-computation and formalization report, not peer review

## 1. Certified object

For

\[
F(s)=\frac{1+s+s^3}{1+s^2+s^4},\qquad 0<s<1,
\]

the manuscript defines \(\gamma_{\mathrm R}=\max F(s)\). The optimizer is the unique root in \((0,1)\) of

\[
P(s)=1-2s+2s^2-4s^3-2s^4-s^6.
\]

Eliminating \(s\) from \(P(s)=0\) and

\[
x(1+s^2+s^4)=1+s+s^3
\]

gives

\[
Q(x)=144x^6-528x^5+648x^4-220x^3-71x^2+42x-31.
\]

The relevant root satisfies

\[
1.2395667407265985397097751707397283370137
<\gamma_{\mathrm R}<
1.2395667407265985397097751707397283370138.
\]

## 2. Exact checks

The distributed SymPy verifier and the independent standard-library verifier check, using exact arithmetic:

1. the derivative identity for \(F\);
2. positivity of the denominator on the real line;
3. the symbolic Sylvester resultant
   \[
   \operatorname{Res}_s(P,xD-N)=3Q(x);
   \]
4. primitivity of \(Q\);
5. irreducibility modulo \(5\) via Rabin's criterion, followed by the integral/rational irreducibility conclusion;
6. exact signs at the rational endpoints isolating \(s_*\) and \(\gamma_{\mathrm R}\);
7. width \(10^{-18}\) for the optimizer enclosure and \(10^{-40}\) for the constant enclosure;
8. the Sturm count showing that \(Q\) has exactly two real roots;
9. strict positivity of the shifted derivative of \(Q\) on \([6/5,\infty)\);
10. the monic integral model
    \[
    R(y)=y^6-22y^5+162y^4-330y^3-639y^2+2268y-10044
    \]
    for \(y=6\gamma_{\mathrm R}\);
11. minimality of the positive integral scaling factor \(6\);
12. the discriminant
    \[
    \operatorname{disc}(R)=2^{17}3^{13}47^3 421^3;
    \]
13. the modular factorization certificates at \(61\) and \(107\), producing cycle types \([1,5]\) and \([1,1,1,1,2]\);
14. the group-theoretic conclusion \(\operatorname{Gal}(Q/\mathbb Q)\cong S_6\).

The standard-library verifier computes its symbolic resultant by fraction-free Bareiss elimination over \(\mathbb Z[x]\). Its finite-field, Sturm, discriminant, and permutation-group routines do not call a computer-algebra system.

## 3. Expected verifier output

```text
All exact certificate checks passed.
Independent standard-library audit passed.
Full symbolic resultant coefficients (low first): [-93, 126, -213, -660, 1944, -1584, 432]
disc(R): 1618922648989369652871168
Galois group order: 720
Dedekind primes and leading coefficients verified: True
Orders from <6-cycle, transposition> over all transpositions: [24, 72, 720]
Least positive integral scaling factor: 6
```

No floating-point approximation is used in a logical step.

## 4. Lean companion

The Lean 4 module is pinned to Lean `v4.32.1` and Mathlib `v4.32.1`. It compiles without `sorry`, `admit`, or added axioms and formalizes:

- positivity of the denominator;
- existence and uniqueness of the critical point in \((0,1)\);
- uniqueness of the maximizer on \([0,1]\);
- the elimination identity and \(Q(\gamma_{\mathrm R})=0\);
- strict monotonicity of \(Q\) on \([6/5,\infty)\);
- the exact rational enclosures of \(s_*\) and \(\gamma_{\mathrm R}\);
- algebraic integrality of \(6\gamma_{\mathrm R}\).

It does not claim formalization of the finite-field irreducibility argument, the global two-real-root count, minimality of the scaling factor, or the Galois-group argument.

## 5. Reproduction

```bash
python -m pip install -r verification/requirements_raigorodskii_v0_8.txt
python verification/verify_raigorodskii_certificate_v0_8.py
python verification/verify_raigorodskii_certificate_stdlib_v0_8.py
lake update
lake exe cache get
lake build
sha256sum -c SHA256SUMS
```

## 6. Limitations

- The manuscript has not been peer reviewed.
- Bibliographic priority remains unresolved.
- The identification of this optimum with Raigorodskii's lower-bound base follows Näslund's stated recovery of the bound at `(k,m,ℓ)=(1,1,3)`; the 2000 construction is not re-derived here.
- The result certifies a known lower-bound base. It does not improve the asymptotic chromatic bound or solve Erdős Problem 704.
