#!/usr/bin/env python3
"""Exact SymPy verification for the Raigorodskii lower-bound certificate v0.9."""
from __future__ import annotations
import warnings

import sympy as sp
from sympy.utilities.exceptions import SymPyDeprecationWarning

class CertificateCheckError(RuntimeError):
    """Raised when an exact certificate check fails."""

def require(condition: bool, message: str) -> None:
    """Run a load-bearing check even when Python is invoked with -O."""
    if not condition:
        raise CertificateCheckError(message)
EXPECTED_SYMPY = '1.14.0'

def bernstein_coefficients(
    polynomial: sp.Expr, variable: sp.Symbol, degree: int
) -> list[sp.Rational]:
    """Return exact Bernstein coefficients after degree elevation."""
    power = sp.Poly(sp.expand(polynomial), variable, domain=sp.QQ)
    require(power.degree() <= degree, "requested Bernstein degree is too small")
    coefficients: list[sp.Rational] = []
    for i in range(degree + 1):
        coefficient = sp.Rational(0)
        for j in range(i + 1):
            coefficient += (
                sp.Rational(sp.binomial(i, j), sp.binomial(degree, j))
                * power.nth(j)
            )
        coefficients.append(sp.factor(coefficient))
    return coefficients


def factor_degree_pattern(
    polynomial: sp.Expr, variable: sp.Symbol, prime: int
) -> list[int]:
    """Return irreducible factor degrees over the prime field."""
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", SymPyDeprecationWarning)
        _, factors = sp.factor_list(sp.Poly(polynomial, variable, modulus=prime))
    return sorted(
        factor.degree() for factor, exponent in factors for _ in range(exponent)
    )


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
    require(sp.__version__ == EXPECTED_SYMPY, f'Expected SymPy {EXPECTED_SYMPY}, found {sp.__version__}')
    s, x, y, t = sp.symbols('s x y t')
    numerator = 1 + s + s ** 3
    denominator = 1 + s ** 2 + s ** 4
    P = 1 - 2 * s + 2 * s ** 2 - 4 * s ** 3 - 2 * s ** 4 - s ** 6
    Q = 144 * x ** 6 - 528 * x ** 5 + 648 * x ** 4 - 220 * x ** 3 - 71 * x ** 2 + 42 * x - 31
    R = y ** 6 - 22 * y ** 5 + 162 * y ** 4 - 330 * y ** 3 - 639 * y ** 2 + 2268 * y - 10044
    derivative_numerator = sp.expand(sp.diff(numerator, s) * denominator - numerator * sp.diff(denominator, s))
    require(derivative_numerator == P, "the numerator of F' must equal P")
    positive_quadratic = 12 * s ** 2 - 4 * s + 2
    positive_decomposition = 6 * s ** 5 + 8 * s ** 3 + positive_quadratic
    require(
        sp.expand(-sp.diff(P, s) - positive_decomposition) == 0,
        "the positivity decomposition of -P' is incorrect",
    )
    require(
        sp.discriminant(positive_quadratic, s) == -80,
        "the quadratic in the positivity decomposition must have discriminant -80",
    )
    require(sp.expand(P.subs(s, 0)) == 1, 'certificate check failed: sp.expand(P.subs(s, 0)) == 1')
    require(sp.expand(P.subs(s, 1)) == -6, 'certificate check failed: sp.expand(P.subs(s, 1)) == -6')
    require(sp.expand(numerator - denominator - s * (1 - s) * (1 + s ** 2)) == 0, 'certificate check failed: sp.expand(numerator - denominator - s * (1 - s) * (1 + s ** 2)) == 0')
    resultant = sp.resultant(P, x * denominator - numerator, s)
    require(sp.expand(resultant - 3 * Q) == 0, 'certificate check failed: sp.expand(resultant - 3 * Q) == 0')
    gb = sp.groebner([P, x * denominator - numerator], s, x, order='lex')
    elimination_polys = [g.as_expr() for g in gb.polys if not g.as_expr().has(s)]
    require(elimination_polys == [Q], 'certificate check failed: elimination_polys == [Q]')
    optimizer = sp.CRootOf(P, 1)
    require(bool(optimizer > 0) and bool(optimizer < 1), 'the chosen exact RootOf must lie in (0,1)')
    gamma_exact = (1 + optimizer + optimizer ** 3) / (1 + optimizer ** 2 + optimizer ** 4)
    require(sp.minimal_polynomial(gamma_exact, x) == Q, 'certificate check failed: sp.minimal_polynomial(gamma_exact, x) == Q')
    require(sp.expand(6 ** 6 * Q.subs(x, y / 6) / 144 - R) == 0, 'certificate check failed: sp.expand(6 ** 6 * Q.subs(x, y / 6) / 144 - R) == 0')
    require(sp.minimal_polynomial(6 * gamma_exact, y) == R, 'certificate check failed: sp.minimal_polynomial(6 * gamma_exact, y) == R')
    q = sp.Poly(Q, x, domain=sp.QQ)
    content, primitive = sp.primitive(Q, x)
    require(content == 1, 'certificate check failed: content == 1')
    require(sp.expand(primitive - Q) == 0, 'certificate check failed: sp.expand(primitive - Q) == 0')
    discriminant_q = sp.discriminant(Q, x)
    require(discriminant_q == 28074595548868135354368, 'certificate check failed: discriminant_q == 28074595548868135354368')
    require(sp.factorint(discriminant_q) == {2: 27, 3: 3, 47: 3, 421: 3}, 'certificate check failed: sp.factorint(discriminant_q) == {2: 27, 3: 3, 47: 3, 421: 3}')
    discriminant_r = sp.discriminant(R, y)
    require(discriminant_r == 1618922648989369652871168, 'certificate check failed: discriminant_r == 1618922648989369652871168')
    require(sp.factorint(discriminant_r) == {2: 17, 3: 13, 47: 3, 421: 3}, 'certificate check failed: sp.factorint(discriminant_r) == {2: 17, 3: 13, 47: 3, 421: 3}')
    q5 = sp.Poly(-Q, x, modulus=5).monic()
    expected_q5 = sp.Poly(x ** 6 - 2 * x ** 5 + 2 * x ** 4 + x ** 2 - 2 * x + 1, x, modulus=5)
    require(q5 == expected_q5, 'certificate check failed: q5 == expected_q5')
    X = sp.Poly(x, x, modulus=5)
    r2 = (poly_powmod(X, 5 ** 2, q5) - X).rem(q5)
    r3 = (poly_powmod(X, 5 ** 3, q5) - X).rem(q5)
    r6 = (poly_powmod(X, 5 ** 6, q5) - X).rem(q5)
    require(sp.gcd(q5, r2).degree() == 0, 'certificate check failed: sp.gcd(q5, r2).degree() == 0')
    require(sp.gcd(q5, r3).degree() == 0, 'certificate check failed: sp.gcd(q5, r3).degree() == 0')
    require(r6.is_zero, 'certificate check failed: r6.is_zero')
    require(q.is_irreducible, 'certificate check failed: q.is_irreducible')
    require(sp.Poly(R, y, domain=sp.QQ).is_irreducible, 'certificate check failed: sp.Poly(R, y, domain=sp.QQ).is_irreducible')
    shifted = sp.Poly(sp.expand(sp.diff(Q, x).subs(x, sp.Rational(6, 5) + y)), y)
    expected_shifted = sp.Poly(864 * y ** 5 + 2544 * y ** 4 + sp.Rational(11808, 5) * y ** 3 + sp.Rational(19788, 25) * y ** 2 + sp.Rational(22714, 125) * y + sp.Rational(236814, 3125), y)
    require(shifted == expected_shifted, 'certificate check failed: shifted == expected_shifted')
    require(all((c > 0 for c in shifted.all_coeffs())), 'certificate check failed: all((c > 0 for c in shifted.all_coeffs()))')
    require(q.eval(sp.Rational(6, 5)) == sp.Rational(-49351, 15625), 'certificate check failed: q.eval(sp.Rational(6, 5)) == sp.Rational(-49351, 15625)')
    require(q.eval(sp.Rational(13, 10)) == sp.Rational(88379, 15625), 'certificate check failed: q.eval(sp.Rational(13, 10)) == sp.Rational(88379, 15625)')
    require(sp.Rational(26, 21) > sp.Rational(6, 5), 'certificate check failed: sp.Rational(26, 21) > sp.Rational(6, 5)')
    require(q.count_roots(-sp.oo, sp.oo) == 2, 'certificate check failed: q.count_roots(-sp.oo, sp.oo) == 2')
    require(q.count_roots(sp.Rational(-467, 1000), sp.Rational(-466, 1000)) == 1, 'certificate check failed: q.count_roots(sp.Rational(-467, 1000), sp.Rational(-466, 1000)) == 1')
    require(q.count_roots(sp.Rational(6, 5), sp.Rational(13, 10)) == 1, 'certificate check failed: q.count_roots(sp.Rational(6, 5), sp.Rational(13, 10)) == 1')

    # A second, Sturm-free certificate for the two-real-root count.
    left_tail = sp.Poly(
        sp.expand(Q.subs(x, -sp.Rational(467, 1000) - y)),
        y,
        domain=sp.QQ,
    )
    expected_left_tail_low = [
        sp.Rational(21899765866381721, 62500000000000000),
        sp.Rational(13886577206994389, 31250000000000),
        sp.Rational(21570510479867, 12500000000),
        sp.Rational(8985296567, 3125000),
        sp.Rational(29399403, 12500),
        sp.Rational(116436, 125),
        sp.Rational(144),
    ]
    require(
        [left_tail.nth(i) for i in range(7)] == expected_left_tail_low,
        'left-tail positivity expansion of Q is incorrect',
    )
    require(
        all(coefficient > 0 for coefficient in expected_left_tail_low),
        'left-tail coefficients must be positive',
    )

    middle_polynomial = -Q.subs(
        x, -sp.Rational(466, 1000) + sp.Rational(833, 500) * t
    )
    middle_bernstein = bernstein_coefficients(middle_polynomial, t, 8)
    expected_middle_bernstein = [
        sp.Rational(90089305534379, 976562500000000),
        sp.Rational(359044792692858729, 3906250000000000),
        sp.Rational(52870090497122397, 3906250000000000),
        sp.Rational(124620702915641, 78125000000000),
        sp.Rational(13443213954293, 390625000000),
        sp.Rational(282934224509, 6250000000),
        sp.Rational(3214343901, 125000000),
        sp.Rational(118373431, 6250000),
        sp.Rational(49351, 15625),
    ]
    require(
        middle_bernstein == expected_middle_bernstein,
        'degree-eight Bernstein certificate for -Q is incorrect',
    )
    require(
        all(coefficient > 0 for coefficient in middle_bernstein),
        'all degree-eight Bernstein coefficients of -Q must be positive',
    )

    negative_window_derivative = -sp.diff(Q, x).subs(
        x, -sp.Rational(467, 1000) + sp.Rational(1, 1000) * t
    )
    derivative_bernstein = bernstein_coefficients(
        negative_window_derivative, t, 5
    )
    expected_derivative_bernstein = [
        sp.Rational(13886577206994389, 31250000000000),
        sp.Rational(6932503348257261, 15625000000000),
        sp.Rational(3460865785481089, 7812500000000),
        sp.Rational(1727743314228061, 3906250000000),
        sp.Rational(862528548927789, 1953125000000),
        sp.Rational(430593559988861, 976562500000),
    ]
    require(
        derivative_bernstein == expected_derivative_bernstein,
        "Bernstein certificate for -Q' is incorrect",
    )
    require(
        all(coefficient > 0 for coefficient in derivative_bernstein),
        "all Bernstein coefficients of -Q' must be positive",
    )
    require(
        q.eval(-sp.Rational(467, 1000)) > 0
        > q.eval(-sp.Rational(466, 1000)),
        'negative-root endpoint signs are incorrect',
    )

    p = sp.Poly(P, s, domain=sp.QQ)
    s1 = sp.Rational(464087083432496056, 10 ** 18)
    s2 = sp.Rational(464087083432496057, 10 ** 18)
    require(s2 - s1 == sp.Rational(1, 10 ** 18), 'certificate check failed: s2 - s1 == sp.Rational(1, 10 ** 18)')
    require(p.eval(s1) > 0, 'certificate check failed: p.eval(s1) > 0')
    require(p.eval(s2) < 0, 'certificate check failed: p.eval(s2) < 0')
    lower = sp.Rational(12395667407265985397097751707397283370137, 10 ** 40)
    upper = sp.Rational(12395667407265985397097751707397283370138, 10 ** 40)
    q_lower = q.eval(lower)
    q_upper = q.eval(upper)
    require(q_lower < 0 < q_upper, 'certificate check failed: q_lower < 0 < q_upper')
    require(upper - lower == sp.Rational(1, 10 ** 40), 'certificate check failed: upper - lower == sp.Rational(1, 10 ** 40)')
    quintic61 = x ** 5 - 15 * x ** 4 + 22 * x ** 3 + 5 * x ** 2 - 22 * x - 2
    factor61 = 22 * (x - 9) * quintic61
    require(sp.Poly(Q - factor61, x, modulus=61).is_zero, 'certificate check failed: sp.Poly(Q - factor61, x, modulus=61).is_zero')
    require(sp.Poly(quintic61, x, modulus=61).is_irreducible, 'certificate check failed: sp.Poly(quintic61, x, modulus=61).is_irreducible')
    quadratic107 = x ** 2 + x - 50
    factor107 = 37 * (x - 16) * (x - 11) * (x + 25) * (x + 33) * quadratic107
    require(sp.Poly(Q - factor107, x, modulus=107).is_zero, 'certificate check failed: sp.Poly(Q - factor107, x, modulus=107).is_zero')
    require(sp.Poly(quadratic107, x, modulus=107).is_irreducible, 'certificate check failed: sp.Poly(quadratic107, x, modulus=107).is_irreducible')
    quintic_r61 = y ** 5 - 29 * y ** 4 - y ** 3 - 18 * y ** 2 - 25 * y + 3
    require(sp.Poly(R - (y + 7) * quintic_r61, y, modulus=61).is_zero, 'certificate check failed: sp.Poly(R - (y + 7) * quintic_r61, y, modulus=61).is_zero')
    require(sp.Poly(quintic_r61, y, modulus=61).is_irreducible, 'certificate check failed: sp.Poly(quintic_r61, y, modulus=61).is_irreducible')
    quadratic_r107 = y ** 2 + 6 * y + 19
    factor_r107 = (y + 11) * (y + 41) * (y + 43) * (y - 16) * quadratic_r107
    require(sp.Poly(R - factor_r107, y, modulus=107).is_zero, 'certificate check failed: sp.Poly(R - factor_r107, y, modulus=107).is_zero')
    require(sp.Poly(quadratic_r107, y, modulus=107).is_irreducible, 'certificate check failed: sp.Poly(quadratic_r107, y, modulus=107).is_irreducible')

    unramified_primes = [
        prime for prime in sp.primerange(2, 108) if discriminant_r % prime != 0
    ]
    first_five_cycle_prime = next(
        prime
        for prime in unramified_primes
        if factor_degree_pattern(R, y, prime) == [1, 5]
    )
    first_transposition_prime = next(
        prime
        for prime in unramified_primes
        if factor_degree_pattern(R, y, prime) == [1, 1, 1, 1, 2]
    )
    require(
        first_five_cycle_prime == 61,
        '61 must be the least unramified prime with factor pattern [1,5]',
    )
    require(
        first_transposition_prime == 107,
        '107 must be the least unramified prime with pattern [1,1,1,1,2]',
    )

    for prime, leading_unit in ((61, 22), (107, 37)):
        require(discriminant_r % prime != 0, 'certificate check failed: discriminant_r % prime != 0')
        require(6 % prime != 0 and 324 % prime != 0, 'certificate check failed: 6 % prime != 0 and 324 % prime != 0')
        require(144 % prime == leading_unit != 0, 'certificate check failed: 144 % prime == leading_unit != 0')
        require(sp.Poly(Q, x, modulus=prime).degree() == 6, 'certificate check failed: sp.Poly(Q, x, modulus=prime).degree() == 6')
        require(sp.Poly(sp.expand(R.subs(y, 6 * x) - 324 * Q), x, modulus=prime).is_zero, 'certificate check failed: sp.Poly(sp.expand(R.subs(y, 6 * x) - 324 * Q), x, modulus=prime).is_zero')
    for d in range(1, 7):
        scaled = sp.Poly(sp.expand(d ** 6 * Q.subs(x, y / d) / 144), y, domain=sp.QQ)
        integral = all((c.q == 1 for c in scaled.all_coeffs()))
        require(integral == (d == 6), 'certificate check failed: integral == (d == 6)')
        require(scaled.coeff_monomial(y ** 5) == -sp.Rational(11 * d, 3), 'certificate check failed: scaled.coeff_monomial(y ** 5) == -sp.Rational(11 * d, 3)')
        require(scaled.coeff_monomial(y ** 4) == sp.Rational(9 * d ** 2, 2), 'certificate check failed: scaled.coeff_monomial(y ** 4) == sp.Rational(9 * d ** 2, 2)')
    group, is_alt = sp.polys.numberfields.galois_group(R, y)
    require(group.order() == 720 and (not is_alt), 'certificate check failed: group.order() == 720 and (not is_alt)')
    print(f'SymPy version: {sp.__version__}')
    print('All exact certificate checks passed.')
    print('Resultant and Groebner elimination = Q:', True)
    print('Exact minimal polynomials = Q and R:', True)
    print('Q primitive and irreducible:', True)
    print('disc(Q):', discriminant_q)
    print('disc(R):', discriminant_r)
    print('Real roots of Q:', q.count_roots(-sp.oo, sp.oo))
    print('Elementary two-root positivity certificate:', True)
    print('Galois group order:', group.order())
    print('Dedekind primes and leading coefficients verified:', True)
    print(
        'Least primes for cycle patterns [1,5] and [1,1,1,1,2]:',
        first_five_cycle_prime,
        first_transposition_prime,
    )
    print('Least positive integral scaling factor:', 6)
    print('Q(6/5) =', q.eval(sp.Rational(6, 5)))
    print('Q(13/10) =', q.eval(sp.Rational(13, 10)))
    print('P(s1) > 0 > P(s2):', p.eval(s1) > 0, p.eval(s2) < 0)
    print('Q(L) < 0 < Q(U):', q_lower < 0, q_upper > 0)
    print('Bracket width:', upper - lower)
if __name__ == '__main__':
    main()
