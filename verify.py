# /// script
# requires-python = ">=3.11"
# dependencies = ["sympy==1.14.0"]
# ///
"""Exact regression checks, not a formal proof or a novelty certificate.

Run with: uv run verify.py
All arithmetic is symbolic/exact. No floating-point point sampling is used.
The arguments valid for all integers and complex parameters are in the paper.
"""

import json
from collections import Counter
from itertools import product

import sympy as s


counts = Counter()


def check(category, condition, detail):
    if not condition:
        raise AssertionError(f"{category}: {detail}")
    counts[category] += 1


def zero(expression):
    return s.cancel(s.expand(expression)) == 0


X, Y, t, u, v, c, cb, beta, betab = s.symbols("X Y t u v c cb beta betab")
x, y = s.symbols("x y", real=True)


def polynomial(m, alpha):
    return X**m * (alpha + X * Y) + Y**m * (s.conjugate(alpha) + X * Y)


# An explicit order-six, degree-five counterexample: simultaneous substitution.
f = (x*x + y*y) * (x**3 - 3*x*y*y) - 3*x*x*y + y**3
expanded = x**5 - 2*x**3*y**2 - 3*x*y**4 - 3*x*x*y + y**3
check("quintic", zero(f - expanded), "Cartesian expansion")
complex_form = polynomial(3, s.I).subs({X: x+s.I*y, Y: x-s.I*y}) / 2
check("quintic", zero(f - complex_form), "real/complex coordinates")
rotation = {x: (x-s.sqrt(3)*y)/2, y: (s.sqrt(3)*x+y)/2}
check("quintic", zero(f.subs(rotation, simultaneous=True) + f), "60-degree sign")
R = s.Matrix([[1, -s.sqrt(3)], [s.sqrt(3), 1]]) / 2
check("quintic", R**6 == s.eye(2), "rotation sixth power")
for k in (1, 2, 3):
    check("quintic", R**k != s.eye(2), f"rotation order not {k}")
check("quintic", s.Poly(f, x, y).total_degree() == 5, "degree")


# Finite checks of the support argument, not an enumeration of all curves.
for d in range(2, 41):
    monomials = [(a, b) for a in range(d+1) for b in range(d+1-a)]
    bound = max(d, 2*d-4)
    for N in range(d+1, 2*d+3):
        plus = [(a, b) for a, b in monomials if (a-b) % N == 0]
        check("support", all(a == b for a, b in plus), (d, N, "positive sign"))
        if N % 2:
            continue
        m = N // 2
        minus = [(a, b) for a, b in monomials if (a-b-m) % N == 0]
        check("support", all(abs(a-b) == m for a, b in minus), (d, N, "weights"))
        if N > bound:
            check("support", all(a+b == m for a, b in minus), (d, N, "homogeneous"))
    if d >= 5:
        m, N = d-2, 2*d-4
        support = {(a, b) for a, b in monomials if (a-b-m) % N == 0}
        expected = {(m, 0), (m+1, 1), (0, m), (1, m+1)}
        check("equality_support", support == expected, d)


parameters = (s.I, (3+4*s.I)/5, (-5+12*s.I)/13)
for m, alpha in product(range(2, 13), parameters):
    P = polynomial(m, alpha)
    A, D = alpha*t**m + s.conjugate(alpha), t**m+1
    H = A + t*D*Y**2
    check("geometry", zero(P.subs(X, t*Y) - Y**m*H), (m, alpha, "blowup"))
    check("geometry", s.Poly(P, X, Y).total_degree() == m+2, (m, "degree"))
    check("geometry", s.degree(P, X) == m+1 == s.degree(P, Y), (m, "bidegree"))
    check("geometry", s.degree(s.gcd(A, t*D), t) == 0, (m, "primitive quadratic"))
    # A nonzero numerator and a denominator with a simple zero at t=0.
    check("geometry", A.subs(t, 0) != 0 and D.subs(t, 0) != 0, (m, "odd pole"))
    branch = s.Poly(t*A*D, t, extension=s.I)
    check("geometry", branch.degree() == 2*m+1, (m, "finite branch count"))
    check("geometry", s.gcd(branch, branch.diff()).degree() == 0, (m, "simple branches"))
    infinity = s.cancel(u**(m+1)*v**(m+1)*P.subs({X: 1/u, Y: 1/v}))
    expected_infinity = v**m + u**m + alpha*u*v**(m+1) + s.conjugate(alpha)*u**(m+1)*v
    check("geometry", zero(infinity-expected_infinity), (m, "infinity chart"))
    mixed = s.cancel(u**(m+1)*P.subs(X, 1/u))
    expected_mixed = alpha*u + Y + s.conjugate(alpha)*u**(m+1)*Y**m + u**m*Y**(m+1)
    check("geometry", zero(mixed-expected_mixed), (m, "mixed chart"))
    check("geometry", s.diff(mixed, Y).subs({u: 0, Y: 0}) == 1, (m, "mixed smoothness"))
    weights = [a-b for a, b in s.Poly(P, X, Y).monoms()]
    order = s.igcd(*[a-b for a in weights for b in weights])
    check("rotation_order", order == 2*m, (m, alpha))
    for degenerate in (1, -1):
        check("excluded_cases", zero(polynomial(m, degenerate) -
              (X*Y+degenerate)*(X**m+Y**m)), (m, degenerate))


# Recover, rather than assume, the four coefficient-ratio constraints.
for m in range(2, 10):
    Q = X**m*(beta+X*Y) + Y**m*(betab+X*Y)
    substitutions = (
        ({X: c*X, Y: cb*Y}, 1, beta/(c*cb)),
        ({X: c/X, Y: cb/Y}, (X*Y)**(m+1), c*cb/betab),
        ({X: c*Y, Y: cb*X}, 1, betab/(c*cb)),
        ({X: c/Y, Y: cb/X}, (X*Y)**(m+1), c*cb/beta),
    )
    for sub, clear, expected in substitutions:
        transformed = s.Poly(s.cancel(clear*Q.subs(sub, simultaneous=True)), X, Y)
        low = transformed.coeff_monomial(X**m)
        high = transformed.coeff_monomial(X**(m+1)*Y)
        check("transport_ratios", zero(low/high-expected), (m, sub))


# Verify every algebraic root permitted by the group formula via remainders.
for m, alpha in product(range(2, 9), parameters):
    P = polynomial(m, alpha)
    for inverted in (False, True):
        sub = {X: c/X, Y: 1/(c*Y)} if inverted else {X: c*X, Y: Y/c}
        clear = (X*Y)**(m+1) if inverted else 1
        transformed = s.Poly(s.cancel(clear*P.subs(sub, simultaneous=True)), X, Y)
        scalar = transformed.coeff_monomial(X**(m+1)*Y)
        residual = s.Poly(s.cancel(c**m*(transformed.as_expr()-scalar*P)), X, Y)
        relation = c**(2*m) - (s.conjugate(alpha)**2 if inverted else 1)
        for coefficient in residual.coeffs():
            remainder = s.rem(coefficient, relation, c)
            check("group_identities", zero(remainder), (m, alpha, inverted))


# A coefficient-real polynomial negated by reflection has the mirror factor.
for d in range(2, 13):
    odd_part = sum(x**a*y**b for a in range(d+1) for b in range(d+1-a) if b % 2)
    check("reflection_sign", zero(odd_part.subs(y, -y) + odd_part), d)
    check("reflection_sign", zero(odd_part.subs(y, 0)), d)

print(json.dumps({
    "status": "PASS",
    "sympy": s.__version__,
    "checks": dict(sorted(counts.items())),
    "total": sum(counts.values()),
    "scope": "Exact identities and bounded regression tests; the general proof is in the TeX.",
}, indent=2))
