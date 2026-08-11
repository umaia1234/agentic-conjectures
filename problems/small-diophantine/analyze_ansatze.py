#!/usr/bin/env python3
"""Exact symbolic checks for three low-degree ansatz classes.

The target equations are

    z^2 + y^2 z + x^3 + a*x + k = 0.

All calculations are over QQ.  This script does not claim to solve any of the
six open equations; it records two ansatz classes that can be ruled out.
"""

from __future__ import annotations

import sympy as sp


TARGETS = ((0, -2), (-1, -1), (0, -3), (0, 3), (-1, -2), (-1, 2))


def rational_roots(poly: sp.Expr, variable: sp.Symbol) -> dict:
    """Return the rational roots of a univariate polynomial, exactly."""
    return sp.polys.polytools.ground_roots(sp.Poly(poly, variable, domain=sp.QQ))


def check_unbalanced_ansatz() -> None:
    """Analyze degrees (2,1,3) in a parameter T.

    We use
      x=-d^2*T^2 + beta*d*T + c,
      y=p*d*T + q,
      z=d^3*T^3 + s*d^2*T^2 + u*d*T + v.

    The calculation below assumes d*p != 0.  The leading three coefficient
    equations determine s,u,v.  A birational change of the remaining
    variables makes the last three equations very small.
    """
    T = sp.symbols("T")
    d, p = sp.symbols("d p", nonzero=True)
    beta, c, q, s, u, v, a, k = sp.symbols("beta c q s u v a k")
    x = -d**2 * T**2 + beta * d * T + c
    y = p * d * T + q
    z = d**3 * T**3 + s * d**2 * T**2 + u * d * T + v
    coeff = sp.Poly(sp.expand(z**2 + y**2 * z + x**3 + a * x + k), T)

    solved = {}
    for degree, variable in ((5, s), (4, u), (3, v)):
        equation = sp.factor(coeff.coeff_monomial(T**degree).subs(solved))
        solved[variable] = sp.factor(sp.solve(equation, variable)[0])

    h, r = sp.symbols("h r")
    # After q=p*(r-beta/2) and c=h-(beta^2+p^4)/4, the remaining
    # equations reduce to the compact eliminated forms below.
    E2 = 4 * (-16 * a - 12 * h**2 + p**8 - 24 * p**4 * r**2)
    E1_mod_E2 = 32 * p**4 * r * (-3 * h + p**4 - 2 * r**2)
    low = [
        sp.factor(
            sp.together(
                coeff.coeff_monomial(T**degree)
                .subs(solved)
                .subs({q: p * (r - beta / 2), c: h - (beta**2 + p**4) / 4})
            )
        )
        for degree in (2, 1, 0)
    ]
    assert sp.factor(low[0] - d**2 * E2 / 64) == 0
    a_from_E2 = (p**8 - 12 * h**2 - 24 * p**4 * r**2) / 16
    assert (
        sp.factor(low[1].subs(a, a_from_E2) - d * E1_mod_E2 / 64) == 0
    )
    print("[degrees (2,1,3)]")
    print("s =", solved[s])
    print("u =", solved[u])
    print("v =", solved[v])
    print("E2 =", sp.factor(E2))
    print("E1 modulo E2 =", sp.factor(E1_mod_E2))

    # Branch r=0.  Eliminate X=p^4 from E2 and the constant equation.
    X, H = sp.symbols("X H")
    constant_numerator = (4 * H - X) * (2 * H**2 - 4 * H * X + X**2)
    constant_after_e2 = sp.factor(low[2].subs(a, a_from_E2))
    assert sp.factor(
        constant_after_e2.subs(r, 0)
        - ((4 * h - p**4) * (2 * h**2 - 4 * h * p**4 + p**8) + 32 * k) / 32
    ) == 0
    for target_a, target_k in TARGETS:
        if target_a == 0:
            # X^2=12H^2 has no nonzero rational solution, since sqrt(12) is
            # irrational.
            print(f"  target {(target_a, target_k)}: r=0 impossible over QQ (p!=0)")
            continue
        pellish = X**2 - 12 * H**2 + 16
        resultant = sp.factor(
            sp.resultant(pellish, constant_numerator + 32 * target_k, X)
        )
        roots = rational_roots(resultant, H)
        print(
            f"  target {(target_a, target_k)}: r=0 resultant degree "
            f"{sp.degree(resultant, H)}, rational H roots={roots}"
        )

    # Branch p^4-3h-2r^2=0.  For a=-1 put X=p^4 and R=r^2.
    X, R = sp.symbols("X R")
    conic = X**2 + 56 * X * R + 16 * R**2 - 48
    second_constant = (
        p**12 - 132 * p**8 * r**2 - 528 * p**4 * r**4
        + 64 * r**6 - 864 * k
    )
    assert sp.factor(
        constant_after_e2.subs(h, (p**4 - 2 * r**2) / 3)
        + second_constant / 864
    ) == 0
    for target_a, target_k in TARGETS:
        if target_a == 0:
            print(
                f"  target {(target_a, target_k)}: second branch impossible "
                "over R except p=r=0"
            )
            continue
        constant = X**3 - 132 * X**2 * R - 528 * X * R**2 + 64 * R**3
        resultant = sp.factor(sp.resultant(conic, constant - 864 * target_k, R))
        roots = rational_roots(resultant, X)
        print(
            f"  target {(target_a, target_k)}: second-branch resultant degree "
            f"{sp.degree(resultant, X)}, rational X roots={roots}"
        )


def check_rational_lines() -> None:
    """Exhaust rational nonvertical affine lines on each target surface.

    After an affine reparametrization every such line can be written

      x=-d^2*T, y=d^3*T+D0, z=T+V0.

    (The parameter origin is chosen at x=0.)  The Groebner basis has a final
    univariate polynomial in d.  No target polynomial has a rational root.
    """
    d, D0, V0 = sp.symbols("d D0 V0")
    print("[rational affine lines]")
    for a, k in TARGETS:
        equations = [
            2 * D0 * d**3 + d**6 * V0 + 1,
            -a * d**2 + D0**2 + 2 * D0 * d**3 * V0 + 2 * V0,
            D0**2 * V0 + V0**2 + k,
        ]
        basis = sp.groebner(equations, D0, V0, d, order="lex")
        univariate = next(
            g.as_expr()
            for g in reversed(basis.polys)
            if g.as_expr().free_symbols <= {d}
        )
        roots = rational_roots(univariate, d)
        print(
            f"  target {(a, k)}: degree {sp.degree(univariate, d)}, "
            f"rational d roots={roots}"
        )
        print("    ", sp.factor(univariate))


def check_equal_degree_quadratics() -> None:
    """Rule out the generic quadratic-in-T curve branch.

    For x,y,z all quadratic in T, coefficient elimination reduces the generic
    (non-even) branch to a rational variable U and direction q:

      a=(39U^2+216U-16)/(3 q^8 U^2),
      k=(918U^3+2088U^2-4320U-128)/(27 q^12 U^3).

    The even branch is a line and was checked above.
    """
    U = sp.symbols("U")
    numerator_a0 = 39 * U**2 + 216 * U - 16
    print("[x,y,z quadratic in one parameter]")
    print("  a=0 numerator discriminant =", sp.discriminant(numerator_a0, U))
    M = 16 - 216 * U - 39 * U**2
    N = 918 * U**3 + 2088 * U**2 - 4320 * U - 128
    for a, k in TARGETS:
        if a == 0:
            print(f"  target {(a, k)}: no rational U (quadratic discriminant nonsquare)")
            continue
        obstruction = sp.factor(N**2 - 27 * k**2 * M**3)
        roots = rational_roots(obstruction, U)
        print(
            f"  target {(a, k)}: degree {sp.degree(obstruction, U)}, "
            f"rational U roots={roots}"
        )


if __name__ == "__main__":
    check_unbalanced_ansatz()
    check_rational_lines()
    check_equal_degree_quadratics()
