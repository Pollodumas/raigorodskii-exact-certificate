# Roadmap for the remaining Lean formalization

This document records verified interfaces and exact certificates for future work. It is not itself a formal proof and does not enlarge the claims made by `RaigorodskiiCertificate.lean`.

## 1. Arithmetic layer

### Irreducibility and degree six

Use the monic polynomial

\[
R(y)=y^6-22y^5+162y^4-330y^3-639y^2+2268y-10044.
\]

Modulo `5`, it becomes

\[
y^6+3y^5+2y^4+y^2+3y+1.
\]

The exact verifiers give a Rabin certificate for irreducibility. A Lean implementation can formalize that quotient-ring test directly, or prove that a reducible monic sextic has an irreducible factor of degree at most three and rule out roots over concrete fields of cardinalities `5`, `25`, and `125` by finite computation.

At the pinned Mathlib revision, `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` supplies the Gauss-lemma bridge from `ℤ[X]` to `ℚ[X]`.

### Minimality of the scaling factor

After identifying the degree-six minimal polynomial, the monic polynomial of `dγ_R` has coefficients

\[
[y^5]= -\frac{11d}{3},\qquad [y^4]=\frac{9d^2}{2}.
\]

If `dγ_R` is integral, these coefficients must be integers, forcing `3 ∣ d` and `2 ∣ d`. The relevant fraction-field interfaces are `minpoly.isIntegrallyClosed_eq_field_fractions` and `minpoly.isIntegrallyClosed_dvd`.

## 2. Exactly two real roots

The manuscript contains an elementary proof that avoids formalizing a complete Sturm engine. It divides the line into intervals and uses:

1. a positive-coefficient expansion of `Q(-467/1000-y)` for `y ≥ 0`;
2. a degree-eight positive Bernstein representation of `-Q` on `[-466/1000,6/5]`;
3. a degree-five positive Bernstein representation of `-Q'` on `[-467/1000,-466/1000]`;
4. the already formalized strict monotonicity of `Q` on `[6/5,∞)`.

Each polynomial identity reduces to `ring`; coefficient positivity reduces to `norm_num`; only a short general lemma about nonnegative Bernstein bases is needed.

## 3. Galois group

The group-theoretic endgame is substantially present in the pinned Mathlib revision:

- `Polynomial.Gal.galAction_isPretransitive`: irreducibility gives transitivity on the roots;
- `Polynomial.Gal.galActionHom` and `galActionHom_injective`: faithful permutation representation;
- `MulAction.is_two_pretransitive_iff`: ordered-pair formulation of 2-transitivity;
- `SubMulAction.ofStabilizer.isMultiplyPretransitive`: stabilizer formulation, if preferred;
- `MulAction.isPreprimitive_of_is_two_pretransitive`: 2-transitive implies primitive;
- `subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`: Jordan's theorem, primitive plus a transposition gives the full symmetric group.

One correction to an earlier roadmap is important: `MulAction.is_two_pretransitive_iff` is the ordered-pair criterion, not itself the point-stabilizer criterion. The latter is supplied by the `SubMulAction.ofStabilizer` API.

The missing packaged bridge is the Dedekind factorization-to-cycle-type theorem:

> For a monic integral polynomial and a prime not dividing its discriminant, the irreducible factor degrees modulo that prime occur as the cycle lengths of a Galois element acting on the roots.

`Mathlib/RingTheory/Frobenius.lean` already supplies arithmetic Frobenius elements, including existence and unramified uniqueness. Completing the bridge requires connecting unramified reduction of the roots to Frobenius orbits and factor degrees. This is a reusable Mathlib-level project, not a manuscript-specific finite calculation.

## 4. Recommended order

1. Formalize irreducibility of `R` modulo `5` and lift it to `ℚ`.
2. Identify the degree-six minimal polynomial.
3. Formalize minimality of scaling `6`.
4. Formalize the Bernstein root-count certificate.
5. Build or import the Dedekind factorization-cycle bridge.
6. Finish the `S₆` and non-radicality layer using the existing group-action API.
