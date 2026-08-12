#!/usr/bin/env python3
"""Independent exact audit for the Raigorodskii certificate v0.9.

Uses only Python's standard library. It performs symbolic Sylvester elimination
in Z[x], finite-field irreducibility checks, rational Sturm computations, exact
endpoint evaluations, and the modular factorization certificates for Gal(Q)=S_6.
"""
from __future__ import annotations
from fractions import Fraction
from math import comb, gcd

class CertificateCheckError(RuntimeError):
    """Raised when an exact certificate check fails."""

def require(condition, message):
    """Run a load-bearing check even when Python is invoked with -O."""
    if not condition:
        raise CertificateCheckError(message)

def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a

def add(a, b):
    n = max(len(a), len(b))
    out = [Fraction(0)] * n
    for i in range(n):
        out[i] = (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
    return trim(out)

def sub(a, b):
    n = max(len(a), len(b))
    out = [Fraction(0)] * n
    for i in range(n):
        out[i] = (a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)
    return trim(out)

def mul(a, b):
    a, b = (trim(a), trim(b))
    if a == [0] or b == [0]:
        return [Fraction(0)]
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return trim(out)

def divmod_q(a, b):
    a = trim(a)
    b = trim(b)
    if b == [0]:
        raise ZeroDivisionError
    if len(a) < len(b):
        return ([Fraction(0)], a)
    q = [Fraction(0)] * (len(a) - len(b) + 1)
    while a != [0] and len(a) >= len(b):
        d = len(a) - len(b)
        c = a[-1] / b[-1]
        q[d] = c
        for i, bi in enumerate(b):
            a[i + d] -= c * bi
        a = trim(a)
    return (trim(q), trim(a))

def divexact(a, b):
    q, r = divmod_q(a, b)
    require(r == [0], 'certificate check failed: r == [0]')
    return q

def deriv(a):
    return trim([Fraction(i) * a[i] for i in range(1, len(a))])

def eval_poly(a, x):
    acc = Fraction(0)
    for c in reversed(a):
        acc = acc * x + c
    return acc

def bareiss_poly_det(matrix):
    n = len(matrix)
    M = [[trim(e) for e in row] for row in matrix]
    sign = 1
    previous_pivot = [Fraction(1)]
    for k in range(n - 1):
        if M[k][k] == [0]:
            pivot_row = next((r for r in range(k + 1, n) if M[r][k] != [0]), None)
            if pivot_row is None:
                return [Fraction(0)]
            M[k], M[pivot_row] = (M[pivot_row], M[k])
            sign *= -1
        pivot = M[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = sub(mul(M[i][j], pivot), mul(M[i][k], M[k][j]))
                if k:
                    numerator = divexact(numerator, previous_pivot)
                require(all((c.denominator == 1 for c in numerator)), 'certificate check failed: all((c.denominator == 1 for c in numerator))')
                M[i][j] = numerator
            M[i][k] = [Fraction(0)]
        previous_pivot = pivot
    result = M[-1][-1]
    return trim([-c for c in result] if sign < 0 else result)

def sylvester_resultant_symbolic(f_desc, g_desc):
    m = len(f_desc) - 1
    n = len(g_desc) - 1
    size = m + n
    rows = []
    zero = [Fraction(0)]
    for shift in range(n):
        row = [zero[:] for _ in range(size)]
        row[shift:shift + m + 1] = [trim(v) for v in f_desc]
        rows.append(row)
    for shift in range(m):
        row = [zero[:] for _ in range(size)]
        row[shift:shift + n + 1] = [trim(v) for v in g_desc]
        rows.append(row)
    return bareiss_poly_det(rows)

def integer_resultant(f_low, g_low):
    result = sylvester_resultant_symbolic([[Fraction(c)] for c in reversed(trim(f_low))], [[Fraction(c)] for c in reversed(trim(g_low))])
    require(len(result) == 1 and result[0].denominator == 1, 'certificate check failed: len(result) == 1 and result[0].denominator == 1')
    return result[0]

def fp_trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a

def fp_sub(a, b, p):
    n = max(len(a), len(b))
    return fp_trim([((a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)) % p for i in range(n)])

def fp_mul(a, b, p):
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] = (out[i + j] + ai * bj) % p
    return fp_trim(out)

def fp_scale(a, c, p):
    return fp_trim([c * ai % p for ai in a])

def fp_divmod(a, b, p):
    a = fp_trim([x % p for x in a])
    b = fp_trim([x % p for x in b])
    require(b != [0], 'certificate check failed: b != [0]')
    if len(a) < len(b):
        return ([0], a)
    q = [0] * (len(a) - len(b) + 1)
    inv = pow(b[-1], -1, p)
    while a != [0] and len(a) >= len(b):
        d = len(a) - len(b)
        c = a[-1] * inv % p
        q[d] = c
        for i, bi in enumerate(b):
            a[i + d] = (a[i + d] - c * bi) % p
        a = fp_trim(a)
    return (fp_trim(q), fp_trim(a))

def fp_divexact(a, b, p):
    q, r = fp_divmod(a, b, p)
    require(r == [0], "finite-field division must be exact")
    return q


def fp_mod(a, m, p):
    return fp_divmod(a, m, p)[1]

def fp_gcd(a, b, p):
    while fp_trim(b) != [0]:
        _, r = fp_divmod(a, b, p)
        a, b = (b, r)
    a = fp_trim([x % p for x in a])
    inv = pow(a[-1], -1, p)
    return fp_trim([x * inv % p for x in a])

def fp_powmod(base, exponent, modulus, p):
    result = [1]
    base = fp_mod(base, modulus, p)
    while exponent:
        if exponent & 1:
            result = fp_mod(fp_mul(result, base, p), modulus, p)
        base = fp_mod(fp_mul(base, base, p), modulus, p)
        exponent >>= 1
    return result

def prime_divisors(n):
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out

def fp_monic(a, p):
    a = fp_trim([c % p for c in a])
    inv = pow(a[-1], -1, p)
    return fp_scale(a, inv, p)

def rabin_irreducible(f, p):
    f = fp_monic(f, p)
    n = len(f) - 1
    X = [0, 1]
    for r in prime_divisors(n):
        test = fp_sub(fp_powmod(X, p ** (n // r), f, p), X, p)
        if len(fp_gcd(f, test, p)) > 1:
            return False
    return fp_sub(fp_powmod(X, p ** n, f, p), X, p) == [0]

def factor_degree_pattern_squarefree(f, p):
    """Distinct-degree factor pattern for a squarefree polynomial over F_p."""
    f = fp_monic(f, p)
    remaining = f
    degree = len(f) - 1
    X = [0, 1]
    pattern = []
    for d in range(1, degree + 1):
        frobenius_fixed = fp_sub(fp_powmod(X, p ** d, f, p), X, p)
        common = fp_gcd(remaining, frobenius_fixed, p)
        common_degree = len(common) - 1
        if common_degree:
            require(common_degree % d == 0, "invalid distinct-degree factor block")
            pattern.extend([d] * (common_degree // d))
            remaining = fp_divexact(remaining, common, p)
        if len(remaining) == 1:
            break
    require(sum(pattern) == degree, "factor degrees must sum to polynomial degree")
    return sorted(pattern)


def sturm_sequence(f):
    seq = [trim(f), deriv(f)]
    while seq[-1] != [0]:
        _, r = divmod_q(seq[-2], seq[-1])
        if r == [0]:
            break
        seq.append([-c for c in r])
    return seq

def variations(values):
    signs = [1 if v > 0 else -1 for v in values if v != 0]
    return sum((a != b for a, b in zip(signs, signs[1:])))

def sturm_count(seq, a, b):
    return variations([eval_poly(f, a) for f in seq]) - variations([eval_poly(f, b) for f in seq])

def sturm_infinite_variations(seq, positive):
    signs = []
    for f in seq:
        lc = f[-1]
        degree = len(f) - 1
        signs.append(lc if positive or degree % 2 == 0 else -lc)
    return variations(signs)

def perm_compose(left, right):
    return tuple((left[right[i]] for i in range(len(left))))

def perm_inverse(p):
    out = [0] * len(p)
    for i, image in enumerate(p):
        out[image] = i
    return tuple(out)

def generated_group_order(generators):
    identity = tuple(range(len(generators[0])))
    gens = list(generators) + [perm_inverse(g) for g in generators]
    seen = {identity}
    stack = [identity]
    while stack:
        current = stack.pop()
        for generator in gens:
            nxt = perm_compose(current, generator)
            if nxt not in seen:
                seen.add(nxt)
                stack.append(nxt)
    return len(seen)

def transposition(n, i, j):
    p = list(range(n))
    p[i], p[j] = (p[j], p[i])
    return tuple(p)

def affine_substitute_low(poly, offset, scale):
    """Coefficients of p(offset + scale*t), low degree first."""
    out = [Fraction(0)] * len(poly)
    for j, coefficient in enumerate(poly):
        for k in range(j + 1):
            out[k] += coefficient * Fraction(comb(j, k)) * offset ** (j - k) * scale ** k
    return trim(out)


def bernstein_coefficients(poly, degree):
    """Exact Bernstein coefficients after degree elevation to `degree`."""
    poly = trim(poly)
    require(len(poly) - 1 <= degree, "requested Bernstein degree is too small")
    result = []
    for i in range(degree + 1):
        value = Fraction(0)
        for j in range(min(i, len(poly) - 1) + 1):
            value += Fraction(comb(i, j), comb(degree, j)) * poly[j]
        result.append(value)
    return result


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    divisor = 3
    while divisor * divisor <= n:
        if n % divisor == 0:
            return False
        divisor += 2
    return True


def main():
    P_low = [1, -2, 2, -4, -2, 0, -1]
    Q_desc = [144, -528, 648, -220, -71, 42, -31]
    Q_low = list(reversed(Q_desc))
    N_low = [1, 1, 0, 1]
    D_low = [1, 0, 1, 0, 1]
    require(sub(mul(deriv(N_low), D_low), mul(N_low, deriv(D_low))) == [Fraction(c) for c in P_low], 'certificate check failed: sub(mul(deriv(N_low), D_low), mul(N_low, deriv(D_low))) == [Fraction(c) for c in P_low]')
    negative_P_derivative = [-c for c in deriv([Fraction(c) for c in P_low])]
    positive_quadratic = [Fraction(2), Fraction(-4), Fraction(12)]
    positive_decomposition = add(positive_quadratic, add([0, 0, 0, 8], [0, 0, 0, 0, 0, 6]))
    require(
        negative_P_derivative == positive_decomposition,
        "the positivity decomposition of -P' is incorrect",
    )
    quadratic_discriminant = positive_quadratic[1] ** 2 - 4 * positive_quadratic[2] * positive_quadratic[0]
    require(
        quadratic_discriminant == -80,
        "the quadratic in the decomposition of -P' must have discriminant -80",
    )
    require(sub(N_low, D_low) == [Fraction(0), Fraction(1), Fraction(-1), Fraction(1), Fraction(-1)], 'certificate check failed: sub(N_low, D_low) == [Fraction(0), Fraction(1), Fraction(-1), Fraction(1), Fraction(-1)]')
    require(mul([0, 1], mul([1, -1], [1, 0, 1])) == sub(N_low, D_low), 'certificate check failed: mul([0, 1], mul([1, -1], [1, 0, 1])) == sub(N_low, D_low)')
    P_desc_symbolic = [[Fraction(c)] for c in reversed(P_low)]
    g_low_s = []
    for i in range(max(len(N_low), len(D_low))):
        ni = N_low[i] if i < len(N_low) else 0
        di = D_low[i] if i < len(D_low) else 0
        g_low_s.append([Fraction(-ni), Fraction(di)])
    resultant_low = sylvester_resultant_symbolic(P_desc_symbolic, list(reversed(g_low_s)))
    require(resultant_low == [Fraction(3 * c) for c in Q_low], 'certificate check failed: resultant_low == [Fraction(3 * c) for c in Q_low]')
    content = 0
    for c in Q_desc:
        content = gcd(content, abs(c))
    require(content == 1, 'certificate check failed: content == 1')
    q5 = fp_monic([-c % 5 for c in Q_low], 5)
    require(q5 == [1, 3, 1, 0, 2, 3, 1] and rabin_irreducible(q5, 5), 'certificate check failed: q5 == [1, 3, 1, 0, 2, 3, 1] and rabin_irreducible(q5, 5)')
    Q_low_q = [Fraction(c) for c in Q_low]
    seq = sturm_sequence(Q_low_q)
    v_minus = sturm_infinite_variations(seq, False)
    v_plus = sturm_infinite_variations(seq, True)
    require(v_minus - v_plus == 2, 'certificate check failed: v_minus - v_plus == 2')
    require(sturm_count(seq, Fraction(-467, 1000), Fraction(-466, 1000)) == 1, 'certificate check failed: sturm_count(seq, Fraction(-467, 1000), Fraction(-466, 1000)) == 1')
    require(sturm_count(seq, Fraction(6, 5), Fraction(13, 10)) == 1, 'certificate check failed: sturm_count(seq, Fraction(6, 5), Fraction(13, 10)) == 1')

    # Independent, Sturm-free certificate for the two real roots.
    left_power = affine_substitute_low(Q_low_q, Fraction(-467, 1000), Fraction(-1))
    expected_left_power = [
        Fraction(21899765866381721, 62500000000000000),
        Fraction(13886577206994389, 31250000000000),
        Fraction(21570510479867, 12500000000),
        Fraction(8985296567, 3125000),
        Fraction(29399403, 12500),
        Fraction(116436, 125),
        Fraction(144),
    ]
    require(left_power == expected_left_power, "left positive-coefficient expansion is incorrect")
    require(all(coefficient > 0 for coefficient in left_power), "Q must be positive left of -467/1000")

    middle_power = affine_substitute_low(Q_low_q, Fraction(-466, 1000), Fraction(833, 500))
    middle_bernstein = bernstein_coefficients([-c for c in middle_power], 8)
    expected_middle_bernstein = [
        Fraction(90089305534379, 976562500000000),
        Fraction(359044792692858729, 3906250000000000),
        Fraction(52870090497122397, 3906250000000000),
        Fraction(124620702915641, 78125000000000),
        Fraction(13443213954293, 390625000000),
        Fraction(282934224509, 6250000000),
        Fraction(3214343901, 125000000),
        Fraction(118373431, 6250000),
        Fraction(49351, 15625),
    ]
    require(middle_bernstein == expected_middle_bernstein, "middle Bernstein certificate is incorrect")
    require(all(coefficient > 0 for coefficient in middle_bernstein), "Q must be negative on [-466/1000,6/5]")

    q_derivative = deriv(Q_low_q)
    negative_derivative_power = [-c for c in affine_substitute_low(q_derivative, Fraction(-467, 1000), Fraction(1, 1000))]
    derivative_bernstein = bernstein_coefficients(negative_derivative_power, 5)
    expected_derivative_bernstein = [
        Fraction(13886577206994389, 31250000000000),
        Fraction(6932503348257261, 15625000000000),
        Fraction(3460865785481089, 7812500000000),
        Fraction(1727743314228061, 3906250000000),
        Fraction(862528548927789, 1953125000000),
        Fraction(430593559988861, 976562500000),
    ]
    require(derivative_bernstein == expected_derivative_bernstein, "derivative Bernstein certificate is incorrect")
    require(all(coefficient > 0 for coefficient in derivative_bernstein), "Q must decrease on the negative isolating interval")
    require(
        eval_poly(Q_low_q, Fraction(-467, 1000)) > 0 > eval_poly(Q_low_q, Fraction(-466, 1000)),
        "negative-root endpoint signs are incorrect",
    )
    a = Fraction(6, 5)
    shifted = []
    for k in range(len(q_derivative)):
        shifted.append(sum((q_derivative[j] * Fraction(comb(j, k)) * a ** (j - k) for j in range(k, len(q_derivative)))))
    require(shifted == [Fraction(236814, 3125), Fraction(22714, 125), Fraction(19788, 25), Fraction(11808, 5), Fraction(2544), Fraction(864)], 'certificate check failed: shifted == [Fraction(236814, 3125), Fraction(22714, 125), Fraction(19788, 25), Fraction(11808, 5), Fraction(2544), Fraction(864)]')
    require(all((c > 0 for c in shifted)), 'certificate check failed: all((c > 0 for c in shifted))')
    require(eval_poly(Q_low_q, Fraction(6, 5)) == Fraction(-49351, 15625), 'certificate check failed: eval_poly(Q_low_q, Fraction(6, 5)) == Fraction(-49351, 15625)')
    require(eval_poly(Q_low_q, Fraction(13, 10)) == Fraction(88379, 15625), 'certificate check failed: eval_poly(Q_low_q, Fraction(13, 10)) == Fraction(88379, 15625)')
    P_low_q = [Fraction(c) for c in P_low]
    s1 = Fraction(464087083432496056, 10 ** 18)
    s2 = Fraction(464087083432496057, 10 ** 18)
    require(s2 - s1 == Fraction(1, 10 ** 18) and eval_poly(P_low_q, s1) > 0 and (eval_poly(P_low_q, s2) < 0), 'certificate check failed: s2 - s1 == Fraction(1, 10 ** 18) and eval_poly(P_low_q, s1) > 0 and (eval_poly(P_low_q, s2) < 0)')
    lower = Fraction(12395667407265985397097751707397283370137, 10 ** 40)
    upper = Fraction(12395667407265985397097751707397283370138, 10 ** 40)
    q_lower = eval_poly(Q_low_q, lower)
    q_upper = eval_poly(Q_low_q, upper)
    require(q_lower < 0 < q_upper and upper - lower == Fraction(1, 10 ** 40), 'certificate check failed: q_lower < 0 < q_upper and upper - lower == Fraction(1, 10 ** 40)')
    R_low = [Fraction(Q_low[i] * 6 ** (6 - i), 144) for i in range(7)]
    require(R_low == [Fraction(c) for c in [-10044, 2268, -639, -330, 162, -22, 1]], 'certificate check failed: R_low == [Fraction(c) for c in [-10044, 2268, -639, -330, 162, -22, 1]]')
    discriminant_R = -integer_resultant(R_low, deriv(R_low))
    require(discriminant_R == Fraction(2 ** 17 * 3 ** 13 * 47 ** 3 * 421 ** 3), 'certificate check failed: discriminant_R == Fraction(2 ** 17 * 3 ** 13 * 47 ** 3 * 421 ** 3)')
    p = 61
    q61 = [c % p for c in Q_low]
    require(Q_desc[0] % p == 22 != 0 and 6 % p != 0 and (324 % p != 0) and (discriminant_R % p != 0) and (len(fp_trim(q61)) == 7), 'certificate check failed: Q_desc[0] % p == 22 != 0 and 6 % p != 0 and (324 % p != 0) and (discriminant_R % p != 0) and (len(fp_trim(q61)) == 7)')
    linear61 = [-9 % p, 1]
    quintic61 = [-2 % p, -22 % p, 5, 22, -15 % p, 1]
    require(fp_trim(fp_scale(fp_mul(linear61, quintic61, p), 22, p)) == fp_trim(q61) and rabin_irreducible(quintic61, p), 'certificate check failed: fp_trim(fp_scale(fp_mul(linear61, quintic61, p), 22, p)) == fp_trim(q61) and rabin_irreducible(quintic61, p)')
    r61 = [int(c) % p for c in R_low]
    linear_r61 = [7, 1]
    quintic_r61 = [3, -25 % p, -18 % p, -1 % p, -29 % p, 1]
    require(fp_trim(fp_mul(linear_r61, quintic_r61, p)) == fp_trim(r61) and rabin_irreducible(quintic_r61, p), 'certificate check failed: fp_trim(fp_mul(linear_r61, quintic_r61, p)) == fp_trim(r61) and rabin_irreducible(quintic_r61, p)')
    p = 107
    q107 = [c % p for c in Q_low]
    require(Q_desc[0] % p == 37 != 0 and 6 % p != 0 and (324 % p != 0) and (discriminant_R % p != 0) and (len(fp_trim(q107)) == 7), 'certificate check failed: Q_desc[0] % p == 37 != 0 and 6 % p != 0 and (324 % p != 0) and (discriminant_R % p != 0) and (len(fp_trim(q107)) == 7)')
    factors107 = [[-16 % p, 1], [-11 % p, 1], [25, 1], [33, 1], [-50 % p, 1, 1]]
    product107 = [1]
    for factor in factors107:
        product107 = fp_mul(product107, factor, p)
    require(fp_trim(fp_scale(product107, 37, p)) == fp_trim(q107) and rabin_irreducible(factors107[-1], p), 'certificate check failed: fp_trim(fp_scale(product107, 37, p)) == fp_trim(q107) and rabin_irreducible(factors107[-1], p)')
    r107 = [int(c) % p for c in R_low]
    factors_r107 = [[11, 1], [41, 1], [43, 1], [-16 % p, 1], [19, 6, 1]]
    product_r107 = [1]
    for factor in factors_r107:
        product_r107 = fp_mul(product_r107, factor, p)
    require(fp_trim(product_r107) == fp_trim(r107) and rabin_irreducible(factors_r107[-1], p), 'certificate check failed: fp_trim(product_r107) == fp_trim(r107) and rabin_irreducible(factors_r107[-1], p)')

    unramified_primes = [prime for prime in range(2, 108) if is_prime(prime) and discriminant_R % prime != 0]
    first_five_cycle_prime = next(
        prime for prime in unramified_primes
        if factor_degree_pattern_squarefree([int(c) % prime for c in R_low], prime) == [1, 5]
    )
    first_transposition_prime = next(
        prime for prime in unramified_primes
        if factor_degree_pattern_squarefree([int(c) % prime for c in R_low], prime) == [1, 1, 1, 1, 2]
    )
    require(first_five_cycle_prime == 61, "61 must be the least unramified prime with factor pattern [1,5]")
    require(first_transposition_prime == 107, "107 must be the least unramified prime with factor pattern [1,1,1,1,2]")
    cycle6 = (1, 2, 3, 4, 5, 0)
    six_cycle_orders = sorted({generated_group_order([cycle6, transposition(6, i, j)]) for i in range(6) for j in range(i + 1, 6)})
    require(six_cycle_orders == [24, 72, 720], 'certificate check failed: six_cycle_orders == [24, 72, 720]')
    for d in range(1, 7):
        scaled_low = [Fraction(Q_low[i] * d ** (6 - i), 144) for i in range(7)]
        integral = all((c.denominator == 1 for c in scaled_low))
        require(integral == (d == 6), 'certificate check failed: integral == (d == 6)')
        require(scaled_low[5] == Fraction(-11 * d, 3), 'certificate check failed: scaled_low[5] == Fraction(-11 * d, 3)')
        require(scaled_low[4] == Fraction(9 * d * d, 2), 'certificate check failed: scaled_low[4] == Fraction(9 * d * d, 2)')
    print('Independent standard-library audit passed.')
    print('Full symbolic resultant coefficients (low first):', [int(c) for c in resultant_low])
    print('disc(R):', int(discriminant_R))
    print('Rabin irreducibility over F_5 passed.')
    print('Sturm total real roots:', v_minus - v_plus)
    print('Elementary two-root positivity certificate:', True)
    print('Q(6/5) =', eval_poly(Q_low_q, Fraction(6, 5)))
    print('Q(13/10) =', eval_poly(Q_low_q, Fraction(13, 10)))
    print('P(s1) > 0 > P(s2):', eval_poly(P_low_q, s1) > 0, eval_poly(P_low_q, s2) < 0)
    print('Q(L) < 0 < Q(U):', q_lower < 0, q_upper > 0)
    print('Mod-61 cycle type: (5,1); mod-107 cycle type: (2,1,1,1,1).')
    print('Dedekind primes and leading coefficients verified:', True)
    print(
        'Least primes for cycle patterns [1,5] and [1,1,1,1,2]:',
        first_five_cycle_prime,
        first_transposition_prime,
    )
    print('Orders from <6-cycle, transposition> over all transpositions:', six_cycle_orders)
    print('Least positive integral scaling factor:', 6)
if __name__ == '__main__':
    main()
