from fractions import Fraction
import sympy as sp

# Exact independent verifier for the algebraic certificate.
s = sp.symbols('s')
x = sp.symbols('x')
y = sp.symbols('y')

N = 1 + s + s**3
D = 1 + s**2 + s**4
F = N / D
P = 1 - 2*s + 2*s**2 - 4*s**3 - 2*s**4 - s**6
Q = 144*x**6 - 528*x**5 + 648*x**4 - 220*x**3 - 71*x**2 + 42*x - 31
R = sp.Poly(sp.expand(6**6 * Q.subs(x, y/6) / 144), y, domain=sp.ZZ)

assert R.as_expr() == y**6 - 22*y**5 + 162*y**4 - 330*y**3 - 639*y**2 + 2268*y - 10044
assert sp.expand(R.as_expr().subs(y, 6*x)) == 324 * Q

# Derivative numerator.
num = sp.factor(sp.together(sp.diff(F, s))).as_numer_denom()[0]
assert sp.expand(num - P) == 0

# Resultant / elimination.
res = sp.resultant(P, sp.together(x*D - N), s)
res_poly = sp.Poly(sp.expand(res), x, domain=sp.ZZ)
assert res_poly.all_coeffs() == [432, -1584, 1944, -660, -213, 126, -93]
assert sp.expand(res - 3*Q) == 0

G = sp.groebner([P, x*D-N], s, x, order='lex')
elim = [g for g in G.polys if not g.as_expr().has(s)]
assert len(elim) == 1
assert sp.Poly(elim[0], x).monic() == sp.Poly(Q, x).monic()

# Irreducibility over Q.
assert sp.Poly(Q, x, domain=sp.QQ).is_irreducible

# Real roots.
roots = sp.Poly(Q, x).intervals(eps=sp.Rational(1,10)**50)
real_intervals = [(a,b) for (a,b), mult in roots if a.is_real and b.is_real for _ in range(mult)]
assert len(real_intervals) == 2

# Exact optimizer enclosure.
s1 = sp.Rational(464087083432496056, 10**18)
s2 = sp.Rational(464087083432496057, 10**18)
assert s2 - s1 == sp.Rational(1, 10**18)
assert sp.sign(sp.together(P.subs(s,s1))) == 1
assert sp.sign(sp.together(P.subs(s,s2))) == -1

# Exact gamma enclosure.
L = sp.Rational(12395667407265985397097751707397283370137, 10**40)
U = sp.Rational(12395667407265985397097751707397283370138, 10**40)
assert U - L == sp.Rational(1, 10**40)
assert sp.sign(sp.together(Q.subs(x,L))) == -1
assert sp.sign(sp.together(Q.subs(x,U))) == 1

# Discriminants.
discQ = sp.discriminant(Q, x)
discR = sp.discriminant(R.as_expr(), y)
assert discQ == 28074595548868135354368
assert discR == 1618922648989369652871168

# Scaling minimality: coefficients of 144*d^6 Q(y/d), normalized monic.
d = sp.symbols('d')
Md = sp.Poly(sp.expand((d**6 / 144) * Q.subs(x, y/d)), y)
assert sp.simplify(Md.coeff_monomial(y**5)) == -sp.Rational(11,3)*d
assert sp.simplify(Md.coeff_monomial(y**4)) == sp.Rational(9,2)*d**2
for dd in range(1,7):
    coeffs = [sp.simplify(c.subs(d,dd)) for c in Md.all_coeffs()]
    is_int = all(c.q == 1 for c in coeffs)
    assert is_int == (dd % 6 == 0)

# Modular factorization certificates for Galois cycle types.
q61 = sp.Poly(Q, x, modulus=61)
q107 = sp.Poly(Q, x, modulus=107)
f61 = sp.Poly(22*(x-9)*(x**5-15*x**4+22*x**3+5*x**2-22*x-2), x, modulus=61)
f107 = sp.Poly(37*(x-16)*(x-11)*(x+25)*(x+33)*(x**2+x-50), x, modulus=107)
assert q61 == f61
assert q107 == f107
fac61 = sp.factor_list(q61)[1]
fac107 = sp.factor_list(q107)[1]
assert sorted([f.degree() for f,e in fac61 for _ in range(e)]) == [1,5]
assert sorted([f.degree() for f,e in fac107 for _ in range(e)]) == [1,1,1,1,2]

# Diagnostic Galois group from SymPy.
ggrp = sp.polys.numberfields.galois_group(sp.Poly(Q, x, domain=sp.QQ), x)[0]
assert ggrp.order() == 720

print('Q irreducible: OK')
print('Real roots: 2')
print('disc(R):', discR)
print('Galois group order:', ggrp.order())
print('Least positive integral scaling factor: 6')
print('All exact certificate checks passed.')
