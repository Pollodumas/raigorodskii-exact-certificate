#!/usr/bin/env python3
"""Exact SymPy verification for the Raigorodskii lower-bound certificate v0.8."""
from __future__ import annotations

import sympy as sp

EXPECTED_SYMPY = "1.14.0"


def poly_powmod(base: sp.Poly, exponent: int, modulus: sp.Poly) -> sp.Poly:
    """Binary exponentiation in a finite polynomial quotient ring."""
    result = sp.Poly(1, base.gens[0], modulus=base.get_modulus())
    power = base
    while exponent:
        if exponent & 1:
            result = (result * power).rem(modulus)
        power = (power * power).rem(modulus)
        exponent //= 2
    return result


def main() -> None:
    assert sp.__version__ == EXPECTED_SYMPY, (
        f"Expected SymPy {EXPECTED_SYMPY}, found {sp.__version__}"
    )

    s, x, y = sp.symbols("s x y")
    numerator = 1 + s + s**3
    denominator = 1 + s**2 + s**4
    P = 1 - 2*s + 2*s**2 - 4*s**3 - 2*s**4 - s**6
    Q = 144*x**6 - 528*x**5 + 648*x**4 - 220*x**3 - 71*x**2 + 42*x - 31
    R = y**6 - 22*y**5 + 162*y**4 - 330*y**3 - 639*y**2 + 2268*y - 10044

    derivative_numerator = sp.expand(
        sp.diff(numerator, s) * denominator
        - numerator * sp.diff(denominator, s)
    )
    assert derivative_numerator == P
    assert sp.discriminant(12*s**2 - 4*s + 2, s) == -80
    assert sp.expand(P.subs(s, 0)) == 1
    assert sp.expand(P.subs(s, 1)) == -6
    assert sp.expand((numerator - denominator) - s * (1 - s) * (1 + s**2)) == 0

    resultant = sp.resultant(P, x * denominator - numerator, s)
    assert sp.expand(resultant - 3 * Q) == 0
    gb = sp.groebner([P, x * denominator - numerator], s, x, order="lex")
    elimination_polys = [g.as_expr() for g in gb.polys if not g.as_expr().has(s)]
    assert elimination_polys == [Q]

    optimizer = sp.CRootOf(P, 1)
    assert 0 < optimizer.evalf(50) < 1
    gamma_exact = (1 + optimizer + optimizer**3) / (1 + optimizer**2 + optimizer**4)
    assert sp.minimal_polynomial(gamma_exact, x) == Q
    assert sp.expand(6**6 * Q.subs(x, y / 6) / 144 - R) == 0
    assert sp.minimal_polynomial(6 * gamma_exact, y) == R

    q = sp.Poly(Q, x, domain=sp.QQ)
    content, primitive = sp.primitive(Q, x)
    assert content == 1
    assert sp.expand(primitive - Q) == 0
    discriminant_q = sp.discriminant(Q, x)
    assert discriminant_q == 28074595548868135354368
    assert sp.factorint(discriminant_q) == {2: 27, 3: 3, 47: 3, 421: 3}
    discriminant_r = sp.discriminant(R, y)
    assert discriminant_r == 1618922648989369652871168
    assert sp.factorint(discriminant_r) == {2: 17, 3: 13, 47: 3, 421: 3}

    q5 = sp.Poly(-Q, x, modulus=5).monic()
    expected_q5 = sp.Poly(x**6 - 2*x**5 + 2*x**4 + x**2 - 2*x + 1, x, modulus=5)
    assert q5 == expected_q5
    X = sp.Poly(x, x, modulus=5)
    r2 = (poly_powmod(X, 5**2, q5) - X).rem(q5)
    r3 = (poly_powmod(X, 5**3, q5) - X).rem(q5)
    r6 = (poly_powmod(X, 5**6, q5) - X).rem(q5)
    assert sp.gcd(q5, r2).degree() == 0
    assert sp.gcd(q5, r3).degree() == 0
    assert r6.is_zero
    assert q.is_irreducible
    assert sp.Poly(R, y, domain=sp.QQ).is_irreducible

    shifted = sp.Poly(sp.expand(sp.diff(Q, x).subs(x, sp.Rational(6, 5) + y)), y)
    expected_shifted = sp.Poly(
        864*y**5 + 2544*y**4 + sp.Rational(11808, 5)*y**3
        + sp.Rational(19788, 25)*y**2 + sp.Rational(22714, 125)*y
        + sp.Rational(236814, 3125), y)
    assert shifted == expected_shifted
    assert all(c > 0 for c in shifted.all_coeffs())
    assert q.eval(sp.Rational(6, 5)) == sp.Rational(-49351, 15625)
    assert q.eval(sp.Rational(13, 10)) == sp.Rational(88379, 15625)
    assert sp.Rational(26, 21) > sp.Rational(6, 5)

    assert q.count_roots(-sp.oo, sp.oo) == 2
    assert q.count_roots(sp.Rational(-467, 1000), sp.Rational(-466, 1000)) == 1
    assert q.count_roots(sp.Rational(6, 5), sp.Rational(13, 10)) == 1

    p = sp.Poly(P, s, domain=sp.QQ)
    s1 = sp.Rational(464087083432496056, 10**18)
    s2 = sp.Rational(464087083432496057, 10**18)
    assert s2 - s1 == sp.Rational(1, 10**18)
    assert p.eval(s1) > 0
    assert p.eval(s2) < 0

    lower = sp.Rational(12395667407265985397097751707397283370137, 10**40)
    upper = sp.Rational(12395667407265985397097751707397283370138, 10**40)
    q_lower = q.eval(lower)
    q_upper = q.eval(upper)
    assert q_lower < 0 < q_upper
    assert upper - lower == sp.Rational(1, 10**40)

    quintic61 = x**5 - 15*x**4 + 22*x**3 + 5*x**2 - 22*x - 2
    factor61 = 22 * (x - 9) * quintic61
    assert sp.Poly(Q - factor61, x, modulus=61).is_zero
    assert sp.Poly(quintic61, x, modulus=61).is_irreducible

    quadratic107 = x**2 + x - 50
    factor107 = 37 * (x - 16) * (x - 11) * (x + 25) * (x + 33) * quadratic107
    assert sp.Poly(Q - factor107, x, modulus=107).is_zero
    assert sp.Poly(quadratic107, x, modulus=107).is_irreducible

    quintic_r61 = y**5 - 29*y**4 - y**3 - 18*y**2 - 25*y + 3
    assert sp.Poly(R - (y + 7) * quintic_r61, y, modulus=61).is_zero
    assert sp.Poly(quintic_r61, y, modulus=61).is_irreducible
    quadratic_r107 = y**2 + 6*y + 19
    factor_r107 = (y + 11) * (y + 41) * (y + 43) * (y - 16) * quadratic_r107
    assert sp.Poly(R - factor_r107, y, modulus=107).is_zero
    assert sp.Poly(quadratic_r107, y, modulus=107).is_irreducible
    for prime, leading_unit in ((61, 22), (107, 37)):
        assert discriminant_r % prime != 0
        assert 6 % prime != 0 and 324 % prime != 0
        assert 144 % prime == leading_unit != 0
        assert sp.Poly(Q, x, modulus=prime).degree() == 6
        assert sp.Poly(sp.expand(R.subs(y, 6 * x) - 324 * Q), x, modulus=prime).is_zero

    for d in range(1, 7):
        scaled = sp.Poly(sp.expand(d**6 * Q.subs(x, y / d) / 144), y, domain=sp.QQ)
        integral = all(c.q == 1 for c in scaled.all_coeffs())
        assert integral == (d == 6)
        assert scaled.coeff_monomial(y**5) == -sp.Rational(11 * d, 3)
        assert scaled.coeff_monomial(y**4) == sp.Rational(9 * d**2, 2)

    group, is_alt = sp.polys.numberfields.galois_group(R, y)
    assert group.order() == 720 and not is_alt

    print(f"SymPy version: {sp.__version__}")
    print("All exact certificate checks passed.")
    print("Resultant and Groebner elimination = Q:", True)
    print("Exact minimal polynomials = Q and R:", True)
    print("Q primitive and irreducible:", True)
    print("disc(Q):", discriminant_q)
    print("disc(R):", discriminant_r)
    print("Real roots of Q:", q.count_roots(-sp.oo, sp.oo))
    print("Galois group order:", group.order())
    print("Dedekind primes and leading coefficients verified:", True)
    print("Least positive integral scaling factor:", 6)
    print("Q(6/5) =", q.eval(sp.Rational(6, 5)))
    print("Q(13/10) =", q.eval(sp.Rational(13, 10)))
    print("P(s1) > 0 > P(s2):", p.eval(s1) > 0, p.eval(s2) < 0)
    print("Q(L) < 0 < Q(U):", q_lower < 0, q_upper > 0)
    print("Bracket width:", upper - lower)


if __name__ == "__main__":
    main()
