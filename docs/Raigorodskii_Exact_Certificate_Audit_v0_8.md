# Exhaustive audit of the Raigorodskii algebraic certificate

**Document audited:** `Raigorodskii_Exact_Certificate_Draft_v0_8`  
**Audit date:** 28 July 2026  
**Status:** internal technical audit, not peer review

## 1. Executive verdict

The exact algebraic certificate survives. No mathematical error was found in the chain

\[
\gamma_{\mathrm R}=\max_{0<s<1}\frac{1+s+s^3}{1+s^2+s^4}
\quad\Longrightarrow\quad
144\gamma_{\mathrm R}^6-528\gamma_{\mathrm R}^5+648\gamma_{\mathrm R}^4
-220\gamma_{\mathrm R}^3-71\gamma_{\mathrm R}^2+42\gamma_{\mathrm R}-31=0.
\]

The draft now proves that:

1. the optimizer is unique;
2. the displayed sextic is primitive and irreducible over \(\mathbb Q\);
3. \(\gamma_{\mathrm R}\) has algebraic degree six;
4. the relevant root is unique above \(1.2\);
5. its exact rational enclosure has width \(10^{-40}\);
6. the sextic has exactly two real roots;
7. its Galois group is \(S_6\), so \(\gamma_{\mathrm R}\) is not expressible by radicals;
8. \(\gamma_{\mathrm R}\) is not an algebraic integer, while \(6\gamma_{\mathrm R}\) is, and 6 is the least positive integral scaling factor.

Two independent executable implementations pass:

- SymPy 1.14.0, including resultant, Groebner elimination, exact `RootOf` minimal polynomial, finite-field certificates, Sturm counts, and a diagnostic Galois-group computation;
- Python standard library only, including a full symbolic Sylvester determinant over \(\mathbb Z[x]\), independently derived finite-field reductions, rational Sturm sequences, and the modular factorization certificates for \(S_6\).

The draft is suitable for expert review. It is not yet peer reviewed, and bibliographic priority remains unresolved.

## 2. Changes made after the adversarial review

The second adversarial pass independently confirmed the modular factorizations and the group-theoretic step, then identified three genuine presentation improvements: the minimal integral scaling is 6 rather than 144; the Dedekind hypotheses must appear in the proof; and the LMFDB discussion should rely only on the fact that LMFDB is not a bibliographic index. A third pass confirmed all v0.6 arithmetic and identified two final exposition gaps: the leading coefficient of the nonmonic polynomial must remain a unit after reduction, and the phrase "unramified-prime hypotheses" should be replaced by the exact condition used, namely \(p\nmid\operatorname{disc}(R)\). Version v0.8 incorporates both corrections and explains why the prime producing a 5-cycle is used instead of the already available 6-cycle modulo 5. A final clean-package audit verified all checksums and executable outputs, identified a broken inline LaTeX command in the Markdown audit, and requested an explicit assertion that the rational isolating endpoints for \(s_*\) are consecutive at 18 decimal places. Version v0.8 repairs the audit text and adds that assertion to both distributed verifiers.

### 2.1 Identification of the constant

The softest point in v0.4 was not the algebra but the historical identification. The new text states precisely:

- Naeslund's Theorem 3 produces the one-variable optimum for \((k,m,\ell)=(1,1,3)\);
- Naeslund explicitly says that this case retrieves Raigorodskii's lower bound;
- the present note inherits that identification and certifies the exact algebraic value of Naeslund's specific optimum.

The note no longer presents the identification as something independently re-proved from Raigorodskii's original parameterization.

### 2.2 Resultant implication

The proof now says explicitly that, at \(x=\gamma_{\mathrm R}\), the optimizer \(s_*\) is a common root of

\[
P(s),\qquad xD(s)-N(s),
\]

so the resultant vanishes. Only the implication "common root implies zero resultant" is used; no converse or degree-preservation claim is needed.

### 2.3 Version hygiene

Every package component now uses v0.8 consistently:

- manuscript;
- audit;
- SymPy verifier;
- standard-library verifier;
- requirements file;
- README;
- checksums.

### 2.4 Independence of the standard-library verifier

The previous verifier contained two correct but hard-coded objects. In v0.8:

- the reduction of \(Q\) modulo 5 is derived from the integer coefficients of \(Q\);
- the coefficients of \(xD(s)-N(s)\) are derived from \(N\) and \(D\);
- the complete resultant polynomial is computed symbolically by fraction-free Bareiss elimination over \(\mathbb Z[x]\), rather than certified only by seven evaluations.

It returns, low degree first,

```text
[-93, 126, -213, -660, 1944, -1584, 432]
```

which is exactly \(3Q\).

### 2.5 Exact Galois-group and integrality corollary

The Galois-group observation remains valid, but the proof is now stated with the hypotheses of Dedekind's factorization theorem explicit.

The natural monic integral model is not the earlier scaling by 144. It is

\[
R(y)=y^6-22y^5+162y^4-330y^3-639y^2+2268y-10044,
\]

whose root is \(y=6\gamma_{\mathrm R}\). Its discriminant is

\[
\operatorname{disc}(R)=2^{17}3^{13}47^3 421^3.
\]

For each \(p\in\{61,107\}\), the exact condition used is

\[
p\nmid\operatorname{disc}(R).
\]

In addition, \(p\nmid6\cdot144\cdot324\). The leading coefficient remains a unit,

\[
144\equiv22\pmod{61},\qquad 144\equiv37\pmod{107},
\]

so \(Q\bmod p\) retains degree six. Since \(R(6x)=324Q(x)\), the invertible substitution \(y=6x\) and multiplication by the unit 324 preserve the complete factor-degree pattern. The displayed factorizations therefore give cycle types \((5,1)\) and \((2,1,1,1,1)\) for the same splitting field.

Irreducibility makes the group transitive. A 5-cycle gives a point stabilizer transitive on the other five points, hence 2-transitivity; conjugates of the transposition then give all transpositions. Thus

\[
\operatorname{Gal}(Q/\mathbb Q)=S_6.
\]

Since \(S_6\) is not solvable, \(\gamma_{\mathrm R}\) is not expressible by radicals.

The use of the prime 61 is deliberate. Irreducibility modulo 5 gives a 6-cycle, but a 6-cycle together with an unspecified transposition does not uniformly generate \(S_6\). An exhaustive six-point permutation check gives generated orders 24, 72, and 720 as the transposition varies. The 5-cycle avoids this ambiguity: transitivity of the full Galois group makes the stabilizer of its fixed point transitive on the other five points, hence the action is 2-transitive, after which one transposition yields all transpositions.

The algebraic-integrality statement has also been sharpened. For a positive integer \(d\), the monic minimal polynomial of \(d\gamma_{\mathrm R}\) is

\[
M_d(y)=d^6\frac{Q(y/d)}{144}.
\]

Its \(y^5\) and \(y^4\) coefficients are \(-11d/3\) and \(9d^2/2\). If \(d\gamma_{\mathrm R}\) is integral, these must be integers, forcing \(6\mid d\). Since \(R\) proves that \(d=6\) works, 6 is the least positive integral scaling factor.

## 3. Mathematical audit

### 3.1 Source reduction

Naeslund's Theorem 3 has numerator

\[
\theta(t^{k/(m+1)};\ell)
\]

and denominator

\[
1+t+\cdots+t^{\ell-1}.
\]

At \((k,m,\ell)=(1,1,3)\),

\[
\theta(t^{1/2};3)=1+\sqrt t+t^{3/2}.
\]

With \(s=\sqrt t\), the objective is exactly

\[
F(s)=\frac{1+s+s^3}{1+s^2+s^4}.
\]

Naeslund's arXiv v2 explanatory display prints the reciprocal. The inconsistency is exact, not merely numerical, because

\[
F(s)-1=\frac{s(1-s)(1+s^2)}{1+s^2+s^4}>0
\qquad(0<s<1),
\]

so the reciprocal is strictly below 1 and cannot equal \(1.23956674\ldots\).

### 3.2 Unique optimizer

Both verifiers also assert exactly that the displayed rational endpoints for \(s_*\) differ by \(10^{-18}\), matching the manuscript's claim that they are consecutive at 18 decimal places.

Writing

\[
N(s)=1+s+s^3,\qquad D(s)=1+s^2+s^4,
\]

one gets

\[
F'(s)=\frac{P(s)}{D(s)^2},
\]

where

\[
P(s)=1-2s+2s^2-4s^3-2s^4-s^6.
\]

Also

\[
-P'(s)=6s^5+8s^3+12s^2-4s+2>0
\]

for \(s>0\), since \(12s^2-4s+2\) has negative discriminant. Thus \(P\) is strictly decreasing. Since \(P(0)=1\) and \(P(1)=-6\), it has exactly one root in \((0,1)\), and this is the unique maximizer of \(F\).

Exact isolation:

\[
0.464087083432496056<s_*<0.464087083432496057.
\]

### 3.3 Elimination

The exact identity is

\[
\operatorname{Res}_s\left(P(s),x(1+s^2+s^4)-(1+s+s^3)\right)=3Q(x).
\]

It is confirmed by:

1. SymPy's exact resultant;
2. a lexicographic Groebner basis whose elimination generator is exactly \(Q\);
3. a standard-library symbolic Sylvester determinant over \(\mathbb Z[x]\);
4. SymPy's `minimal_polynomial` applied to the exact `RootOf` optimizer value.

At \(x=F(s_*)\), the two polynomials in \(s\) share the root \(s_*\), hence \(Q(F(s_*))=0\).

### 3.4 Irreducibility and exact degree

The content of \(Q\) is one. Modulo 5, after multiplication by the unit \(-1\),

\[
\overline Q=x^6-2x^5+2x^4+x^2-2x+1.
\]

The exact Rabin checks are

\[
\gcd(\overline Q,x^{5^2}-x)=1,
\qquad
\gcd(\overline Q,x^{5^3}-x)=1,
\]

and

\[
x^{5^6}-x\equiv0\pmod{\overline Q}.
\]

Therefore \(Q\) is irreducible over \(\mathbb Q\), and \(\gamma_{\mathrm R}\) has degree exactly six.

Under the standard monic convention, its minimal polynomial is \(Q/144\). The polynomial \(Q\) is its primitive irreducible integral associate.

### 3.5 Real roots and monotonicity

The shifted derivative is

\[
\begin{aligned}
Q'(6/5+y)={}&864y^5+2544y^4+\frac{11808}{5}y^3
+\frac{19788}{25}y^2\\
&+\frac{22714}{125}y+\frac{236814}{3125}.
\end{aligned}
\]

All coefficients are positive, so \(Q\) is strictly increasing on \([6/5,\infty)\). Exact signs give

\[
Q(6/5)=-49351/15625<0,
\qquad
Q(13/10)=88379/15625>0.
\]

A rational Sturm sequence proves that \(Q\) has exactly two real roots:

- one in \((-0.467,-0.466)\);
- \(\gamma_{\mathrm R}\) in \((1.2,1.3)\).

### 3.6 Certified decimal

Let

\[
L=\frac{12395667407265985397097751707397283370137}{10^{40}},
\]

\[
U=\frac{12395667407265985397097751707397283370138}{10^{40}}.
\]

Exact evaluation gives

\[
Q(L)<0<Q(U),
\]

and monotonicity yields

\[
L<\gamma_{\mathrm R}<U.
\]

The interval width is exactly \(10^{-40}\).

### 3.7 Structural checks

Additional exact consistencies:

- \(\operatorname{disc}(Q)=2^{27}3^3 47^3 421^3>0\);
- the resultant has exact degree six;
- the minimal monic integral scaling is
  \[
  R(y)=y^6-22y^5+162y^4-330y^3-639y^2+2268y-10044,
  \qquad y=6\gamma_{\mathrm R};
  \]
- \(\operatorname{disc}(R)=2^{17}3^{13}47^3 421^3\);
- the primes 61 and 107 satisfy \(p\nmid\operatorname{disc}(R)\), and the leading coefficients 144, 22, and 37 remain units in the relevant reductions;
- the SymPy diagnostic Galois-group computation returns order 720, agreeing with the modular proof;
- the standard-library verifier derives \(R\), its discriminant, and the scaling test from the defining coefficients, then compares the computed quantities against the exact values stated in the manuscript; its printed outputs come from the derived quantities.

## 4. Citation audit

| Source | Claim | Verdict |
|---|---|---|
| Raigorodskii, *Russian Mathematical Surveys* 55 (2000), 351-352 | Original asymptotic lower bound | Correct |
| Gorskaya, Mitricheva (Shitova), Protasov, Raigorodskii, *Sbornik: Mathematics* 200 (2009), 783-801 | Convex-minimization treatment and recorded numerical base | Correct |
| Naeslund, *Mathematika* 69 (2023), 692-718; arXiv:2205.12312v2 | Theorem 3, exact specialization, and explicit statement that the case retrieves Raigorodskii's bound | Correct; arXiv explanatory display is inverted |
| Erdős Problems #704 | Limit question and recorded lower bound | Correct at the audit date |
| Rabin, *SIAM Journal on Computing* 9 (1980), 273-280 | Finite-field irreducibility criterion | Correct |
| Cox, *Galois Theory*, 2nd ed. (2012) | Factorization-cycle correspondence and radicals | Appropriate standard reference |
| Meurer et al., *PeerJ Computer Science* 3 (2017), e103 | SymPy | Correct |

## 5. Priority search

The following were searched:

- the full coefficient string of the sextic;
- the monic integral models for \(6\gamma_{\mathrm R}\) and \(144\gamma_{\mathrm R}\);
- the long decimal expansion;
- combinations of "Raigorodskii", "minimal polynomial", "algebraic", "sextic", and "root isolation";
- the inspected primary texts;
- targeted web-index searches restricted to OEIS.

No prior appearance of the explicit sextic or exact isolation was found.

This remains evidence, not proof of priority. Equivalent number-field models, unindexed theses, notes, source code, and non-English literature may evade text search. An LMFDB absence would not establish bibliographic priority: LMFDB is a database of number fields, not a bibliographic index. Its silence would concern database coverage, not whether the sextic or root isolation had appeared in print.

The manuscript therefore retains the qualified sentence:

> To the best of our knowledge, this explicit minimal polynomial and exact root isolation have not previously appeared in the literature.

It immediately states that the search was not comprehensive and that priority awaits specialist review.

## 6. Reproducibility

From the package directory:

```bash
python -m pip install -r requirements_raigorodskii_v0_8.txt
python verify_raigorodskii_certificate_v0_8.py
python verify_raigorodskii_certificate_stdlib_v0_8.py
sha256sum -c SHA256SUMS
```

Expected output includes:

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

No floating-point value is used in a logical step.

A fresh extraction of the release ZIP was executed independently of the build directory. Both verification programs completed successfully, and `sha256sum -c SHA256SUMS` returned `OK` for every packaged file. The rendered PDF was also inspected page by page after recompilation.

## 7. Remaining limitations

1. No human expert has yet reviewed the complete proof.
2. Priority is unresolved.
3. The historical equality with Raigorodskii's original parameterization is inherited from Naeslund's explicit identification, rather than re-derived from the 2000 construction.
4. The journal version of Naeslund's paper has not been inspected for the reciprocal display.
5. The result certifies a known lower-bound base and does not improve the asymptotic chromatic bound or solve Erdős #704.

## 8. Final recommendation

Send v0.8 to Ingo Althöfer with the PDF and the complete reproducibility ZIP. Ask specifically for:

- mathematical review of the identification and elimination chain;
- assessment of the Galois-group corollary;
- knowledge of prior appearances of the sextic or exact root isolation;
- advice on attribution and the appropriate publication format.
