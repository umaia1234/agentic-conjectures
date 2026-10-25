#!/usr/bin/env python3
"""Exact checks for curves on which z is a polynomial in y.

Target surfaces (the six remaining equations):

    S_{a,b}:  z^2 + y^2*z + x^3 + a*x + b = 0,
    (a,b) in {(0,-2), (-1,-1), (0,-3), (0,3), (-1,-2), (-1,2)}.

With w = 2z + y^2 the equation reads w^2 = y^4 - 4(x^3 + a*x + b).  For
A in QQ[y] put Q = 2A + y^2 and

    C_A = S_{a,b} cap {z = A(y)}:   4(x^3 + a*x + b) = y^4 - Q(y)^2.

README.md (section "Curves on which z is a polynomial in y") explains how
Siegel's theorem and the Riemann-Hurwitz formula reduce the question "does some
C_A with deg A <= 5 carry infinitely many integer points?" to the algebraic
statements checked here.  All arithmetic is exact (sympy over
QQ and Python integers).  Nothing here finds a solution of any equation and
nothing here claims that any of the six equations is solved.
"""

from __future__ import annotations

import sys
from fractions import Fraction

import sympy as sp

SIX = ((0, -2), (-1, -1), (0, -3), (0, 3), (-1, -2), (-1, 2))
A0_BS = (-2, -3, 3)  # the three b with a = 0

x, y, z, r, k, b, t = sp.symbols("x y z r k b t")
R_, T_ = sp.symbols("R T")


def ok(cond: bool, msg: str) -> None:
    if not cond:
        print("FAIL:", msg)
        sys.exit(1)
    print("ok  ", msg)


def rational_roots(poly: sp.Poly) -> list:
    return sorted(sp.polys.polytools.ground_roots(sp.Poly(poly, domain=sp.QQ)).keys())


def is_rational_square(q: sp.Rational) -> bool:
    q = sp.Rational(q)
    return q >= 0 and sp.sqrt(q).is_rational


def is_rational_power(q: sp.Rational, n: int) -> bool:
    q = sp.Rational(q)
    if q < 0 and n % 2 == 0:
        return False
    root = sp.root(abs(q), n)
    return bool(root.is_rational)


# ---------------------------------------------------------------------------
# 0. the substitution w = 2z + y^2
# ---------------------------------------------------------------------------
def check_identity() -> None:
    a = sp.symbols("a")
    lhs = (2 * z + y**2) ** 2 - (y**4 - 4 * (x**3 + a * x + b))
    rhs = 4 * (z**2 + y**2 * z + x**3 + a * x + b)
    ok(sp.expand(lhs - rhs) == 0, "(2z+y^2)^2 - (y^4 - 4N(x)) = 4*(equation)")


# ---------------------------------------------------------------------------
# 1. a = 0, deg A = 2, lc(A) != -1: genus-0 curves <-> points of C_b
# ---------------------------------------------------------------------------
REL = sp.Poly(k**2 - (r**4 - 4 * b), k)  # C_b : k^2 = r^4 - 4b
D_r = 3 * r**8 - 24 * b * r**4 - 16 * b**2
E_r = r**8 + 24 * b * r**4 - 48 * b**2
G0, G1, G2 = k, 2 * r**3 / k, r**2 * (r**4 - 12 * b) / k**3  # Taylor data
Q_rk = G0 + G1 * (y - r) + G2 * (y - r) ** 2
LAM = 4 * b * D_r / k**6  # leading coefficient of y^4 - 4b - Q^2
S_rk = -r * E_r / D_r  # the simple root s


def zero_mod_rel(expr: sp.Expr) -> bool:
    num = sp.numer(sp.together(expr))
    return sp.rem(sp.Poly(sp.expand(num), k), REL).is_zero


def check_degree_two_a0() -> None:
    g0, g1, g2 = sp.symbols("g0 g1 g2")
    Q = g0 + g1 * (y - r) + g2 * (y - r) ** 2
    P = sp.Poly(sp.expand((y**4 - 4 * b - Q**2).subs(y, r + t)), t)
    c = [P.coeff_monomial(t**i) for i in range(5)]
    ok(sp.expand(c[0] - (r**4 - 4 * b - g0**2)) == 0, "c0 = r^4 - 4b - g0^2")
    ok(sp.expand(c[1] - (4 * r**3 - 2 * g0 * g1)) == 0, "c1 = 4r^3 - 2 g0 g1")
    ok(sp.expand(c[2] - (6 * r**2 - g1**2 - 2 * g0 * g2)) == 0, "c2 = 6r^2 - g1^2 - 2 g0 g2")
    ok(sp.expand(c[3] - (4 * r - 2 * g1 * g2)) == 0, "c3 = 4r - 2 g1 g2")
    ok(sp.expand(c[4] - (1 - g2**2)) == 0, "c4 = 1 - g2^2")
    # c0=c1=c2=0 with g0=k: g0=0 would force r=0 (c1) and then c0=-4b != 0.
    sol = {g0: k, g1: 2 * r**3 / k}
    sol[g2] = sp.together((6 * r**2 - sol[g1] ** 2) / (2 * k))
    ok(zero_mod_rel(sol[g2] - G2), "triple root at r forces g2 = r^2(r^4-12b)/k^3 on C_b")
    for i in range(3):
        ok(zero_mod_rel(c[i].subs(sol)), "c%d vanishes for Q_{r,k}" % i)
    ok(zero_mod_rel(1 - G2**2 - LAM), "1 - g2^2 = 4b*D(r)/k^6, D = 3r^8-24br^4-16b^2")
    ok(zero_mod_rel(c[3].subs(sol) - 16 * b * r * (r**4 + 4 * b) / k**4),
       "c3 = 16 b r (r^4+4b)/k^4 (quadruple root iff r = 0 or r^4 = -4b)")
    ident = y**4 - 4 * b - Q_rk**2 - LAM * (y - r) ** 3 * (y - S_rk)
    ok(zero_mod_rel(ident), "y^4-4b-Q_{r,k}^2 = (4bD/k^6)(y-r)^3(y-s), s = -r E(r)/D(r)")
    for bv in A0_BS:
        ok(not is_rational_square(-4 * bv) and not is_rational_power(-4 * bv, 4),
           "b=%d: no quadruple-root case (-4b not a square, not a 4th power)" % bv)
        ok(rational_roots(sp.Poly(D_r.subs(b, bv), r)) == [],
           "b=%d: D(r) has no rational root, so lc(Q) != +-1 and s is defined" % bv)


# ---------------------------------------------------------------------------
# 2. rational points of C_b : k^2 = r^4 - 4b  (E_b : Y^2 = X^3 + 16 b X)
# ---------------------------------------------------------------------------
def count_points(A: int, p: int) -> int:
    """#E(F_p) for Y^2 = X^3 + A X, p odd."""
    sq = [0] * p
    for v in range(p):
        sq[v * v % p] += 1
    return 1 + sum(sq[(X**3 + A * X) % p] for X in range(p))


def quartic_locally_insoluble(d: int, c: int, p: int, kk: int) -> bool:
    """True if N^2 = d M^4 + c e^4 has no solution mod p^kk with (M, e) primitive."""
    m = p**kk
    squares = {(n * n) % m for n in range(m)}
    for M in range(m):
        for e in range(m):
            if M % p == 0 and e % p == 0:
                continue
            if (d * M**4 + c * e**4) % m in squares:
                return False
    return True


def check_cb_points() -> None:
    X = 2 * (k + r**2)
    Y = 4 * r * (k + r**2)
    ok(zero_mod_rel(Y**2 - X**3 - 16 * b * X),
       "(r,k) -> (2(k+r^2), 4r(k+r^2)) maps C_b to E_b: Y^2 = X^3 + 16bX")
    Xs, Ys = sp.symbols("Xs Ys")
    rr, kk_ = Ys / (2 * Xs), Xs / 2 - Ys**2 / (4 * Xs**2)
    inv = sp.together(kk_**2 - rr**4 + 4 * b)
    ok(sp.expand(sp.numer(inv) + (Ys**2 - Xs**3 - 16 * b * Xs) * sp.denom(inv) / (4 * Xs)) == 0,
       "inverse (X,Y) -> (Y/(2X), X/2 - Y^2/(4X^2)) for X != 0, so affine C_b(Q) "
       "embeds in E_b(Q) minus {O,(0,0)}")
    # b = -3: E: Y^2 = X^3 - 48X has E(Q) = {O, (0,0)}.
    A = -48
    n5 = count_points(A, 5)
    ok(n5 == 2, "b=-3: #E(F_5) = 2 (good reduction at 5), so E(Q)_tors = {O,(0,0)}")
    # 2-isogeny descent: E: y^2 = x^3 - 48x, E': y^2 = x^3 + 192x.
    # alpha(E) contains {1, -3}; alpha'(E') contains {1, 3}; rank 0 iff equality.
    for d, p, kk in ((-1, 3, 2), (2, 3, 2), (-2, 2, 4)):
        ok(quartic_locally_insoluble(d, -48 // d, p, kk),
           "b=-3 descent on E: N^2 = %d M^4 %+d e^4 insoluble mod %d^%d" % (d, -48 // d, p, kk))
    ok(quartic_locally_insoluble(2, 96, 3, 2),
       "b=-3 descent on E': N^2 = 2 M^4 + 96 e^4 insoluble mod 3^2")
    print("     (E': d < 0 has no real solution since 192/d < 0)  => rank E_{-3}(Q) = 0,")
    print("     so C_{-3} : k^2 = r^4 + 12 has no affine rational point.")
    # b = -2, 3: an explicit point of infinite order (torsion is Z/2 by #E(F_5), #E(F_7)).
    for bv, (rv, kv) in ((-2, (-1, 3)), (3, (2, 2))):
        A = 16 * bv
        ok(kv**2 == rv**4 - 4 * bv, "b=%d: (r,k) = (%d,%d) lies on C_b" % (bv, rv, kv))
        tors = sp.gcd(count_points(A, 5), count_points(A, 7))
        ok(tors == 2, "b=%d: gcd(#E(F_5), #E(F_7)) = 2, so E(Q)_tors = {O,(0,0)}" % bv)
        P = (Fraction(2 * (kv + rv**2)), Fraction(4 * rv * (kv + rv**2)))
        ok(P[1] ** 2 == P[0] ** 3 + A * P[0] and P[0] != 0,
           "b=%d: image point %s is not torsion, so C_b(Q) is infinite"
           % (bv, (int(P[0]), int(P[1]))))


# ---------------------------------------------------------------------------
# 3. explicit families for b = -2, 3 and the integrality obstruction
# ---------------------------------------------------------------------------
def family(bv: int, rv, kv):
    sub = {b: bv, r: sp.Rational(rv), k: sp.Rational(kv)}
    Q = sp.expand(Q_rk.subs(sub))
    A = sp.expand((Q - y**2) / 2)
    lam, s = sp.Rational(LAM.subs(sub)), sp.Rational(S_rk.subs(sub))
    U = sp.symbols("U")
    Y = s + 4 * U**3 / lam  # (lam/4)(y - s) = U^3
    X = U * (Y - sp.Rational(rv))
    Z = A.subs(y, Y)
    return A, lam, s, U, sp.expand(X), sp.expand(Y), sp.expand(Z)


def check_families() -> None:
    for bv, rv, kv in ((-2, -1, 3), (3, 2, 2)):
        A, lam, s, U, X, Y, Z = family(bv, rv, kv)
        print("     b=%d, (r,k)=(%d,%d): A(y) = %s" % (bv, rv, kv, sp.factor(A)))
        print("        x(U) = %s,  y(U) = %s" % (X, Y))
        ok(sp.expand(Z**2 + Y**2 * Z + X**3 + bv) == 0,
           "b=%d: (x(U), y(U), A(y(U))) satisfies the equation identically in U" % bv)
        # independent spot check with Fractions only
        Ac = [Fraction(int(c.p), int(c.q)) for c in sp.Poly(A, y).all_coeffs()]
        for u in (Fraction(1), Fraction(-2, 3), Fraction(5, 7), Fraction(13, 2)):
            yy = Fraction(int(s.p), int(s.q)) + 4 * u**3 / Fraction(int(lam.p), int(lam.q))
            xx = u * (yy - rv)
            zz = Ac[0] * yy**2 + Ac[1] * yy + Ac[2]
            if zz**2 + yy**2 * zz + xx**3 + bv != 0:
                ok(False, "Fraction spot check b=%d u=%s" % (bv, u))
        ok(True, "b=%d: Fraction-arithmetic spot check at four parameter values" % bv)


def check_obstructions() -> None:
    Dh = sp.expand(T_**8 * D_r.subs(r, R_ / T_))
    Eh = sp.expand(T_**8 * E_r.subs(r, R_ / T_))
    V = b * (T_ * Dh * y + R_ * Eh)
    lhs = T_**9 * k**6 * (LAM / 4) * (y - S_rk)
    ok(sp.simplify(sp.together(lhs.subs(r, R_ / T_) - V)) == 0,
       "T^9 k^6 (lam/4)(y-s) = V := b(T*Dh(R,T)*y + R*Eh(R,T)) for r = R/T")
    print("     hence x^3 = (lam/4)(y-r)^3(y-s) with x != 0 forces V = (x T^3 k^2/(y-r))^3,")
    print("     a nonzero integer cube, whenever y is an integer.")
    Dh_f = sp.lambdify((R_, T_, b), Dh)
    Eh_f = sp.lambdify((R_, T_, b), Eh)
    # b = -2: residues mod 13
    p, bv = 13, -2
    cubes = {(c**3) % p for c in range(p)}
    squares = {(c * c) % p for c in range(p)}
    cases = 0
    for Rm in range(p):
        for Tm in range(p):
            if (Rm, Tm) == (0, 0) or (Rm**4 - 4 * bv * Tm**4) % p not in squares:
                continue
            for ym in range(p):
                Vm = bv * (Tm * Dh_f(Rm, Tm, bv) * ym + Rm * Eh_f(Rm, Tm, bv)) % p
                if Vm in cubes:
                    ok(False, "mod 13 obstruction fails at R,T,y = %d,%d,%d" % (Rm, Tm, ym))
                cases += 1
    ok(True, "b=-2: V mod 13 is a nonzero non-cube in all %d admissible residue cases" % cases)
    # b = 3: residues mod 9, V must have 3-adic valuation exactly 1
    m, bv = 9, 3
    squares9 = {(c * c) % m for c in range(m)}
    cases = 0
    for Rm in range(m):
        for Tm in range(m):
            if (Rm % 3, Tm % 3) == (0, 0) or (Rm**4 - 4 * bv * Tm**4) % m not in squares9:
                continue
            for ym in range(m):
                Vm = bv * (Tm * Dh_f(Rm, Tm, bv) * ym + Rm * Eh_f(Rm, Tm, bv)) % m
                if Vm not in (3, 6):
                    ok(False, "mod 9 obstruction fails at R,T,y = %d,%d,%d" % (Rm, Tm, ym))
                cases += 1
    ok(True, "b=3: V = 3 or 6 mod 9 (v_3(V) = 1, not a cube) in all %d admissible cases" % cases)


# ---------------------------------------------------------------------------
# 4. a = -1: the two critical values of x^3 - x are Galois conjugate
# ---------------------------------------------------------------------------
def check_a_minus1() -> None:
    s3 = sp.sqrt(3)
    for sgn in (1, -1):
        c0 = sgn * 2 / (3 * s3)
        x1, x2 = -sgn / s3, sgn * 2 / s3
        ok(sp.expand(x**3 - x - c0 - (x - x1) ** 2 * (x - x2)) == 0,
           "x^3 - x - (%s) = (x - (%s))^2 (x - (%s))" % (c0, x1, x2))
    print("     the critical values +-2/(3*sqrt3) of x^3 - x are swapped by sqrt3 -> -sqrt3,")
    print("     so for g in QQ[y] the odd-multiplicity root counts of g -+ 2/(3*sqrt3) agree")
    print("     (README, Lemma B)")


# ---------------------------------------------------------------------------
# 5. a = 0, deg A = 4 and 5:  y^4 - 4b - Q^2 = -q^2 (y-s)^m H^3
# ---------------------------------------------------------------------------
def proportional(expr, target) -> bool:
    ratio = sp.cancel(sp.expand(expr) / target)
    return bool(ratio.is_number) and ratio != 0


def exact_quo(P: sp.Poly, G: sp.Poly) -> sp.Poly:
    quo, rem = sp.div(P, G)
    assert rem.is_zero
    return quo


def monic_factors(g, gens) -> set:
    _, facs = sp.Poly(g, *gens).factor_list()
    return {sp.Poly(f.as_expr(), *gens, domain=sp.QQ).monic() for f, _ in facs}


def same_factors(g, expected, gens) -> bool:
    want = {sp.Poly(f, *gens, domain=sp.QQ).monic() for f in expected}
    return monic_factors(g, gens) == want


def no_common_root(polys, var) -> bool:
    """Nonzero univariate polynomials with constant gcd have no common root."""
    ps = [sp.Poly(p, var) for p in polys]
    if any(p.is_zero for p in ps):
        return False
    g = ps[0]
    for p in ps[1:]:
        g = sp.gcd(g, p)
    return g.is_ground


def nonzero_constant(expr) -> bool:
    expr = sp.expand(expr)
    return bool(expr.is_number) and expr != 0


def deg_system(d: int, h: int, m: int, s_val: int):
    """Residual equations of y^4 - 4b - Q^2 = -q^2 (y-s)^m H^3 with deg Q = d.

    Q = q*y^d + ..., H monic of degree h.  The coefficients of y^(2d-1..d)
    are linear in Q_(d-1..0) with coefficient 2q and are solved; the returned
    list holds the numerators of the coefficients of y^(d-1), ..., y^0, written
    in q2 = q^2 (every monomial has even degree in q, checked).
    """
    q, q2 = sp.symbols("q q2")
    hs = sp.symbols("h0:%d" % h)
    H = y**h + sum(hs[i] * y**i for i in range(h))
    M = sp.expand(y**4 - 4 * b + q**2 * H**3 * (y - s_val) ** m)
    Qc = sp.symbols("Q0:%d" % d)
    Q = q * y**d + sum(Qc[i] * y**i for i in range(d))
    diff = sp.Poly(sp.expand(Q**2 - M), y)
    assert diff.coeff_monomial(y ** (2 * d)) == 0
    sol = {}
    for deg in range(2 * d - 1, d - 1, -1):
        var = Qc[deg - d]
        lin = sp.Poly(sp.expand(diff.coeff_monomial(y**deg).subs(sol)), var)
        assert lin.degree() == 1 and sp.expand(lin.coeff_monomial(var) - 2 * q) == 0
        sol[var] = sp.together(-lin.coeff_monomial(1) / lin.coeff_monomial(var))
    eqs = []
    for deg in range(d - 1, -1, -1):
        e = sp.expand(sp.numer(sp.together(sp.expand(diff.coeff_monomial(y**deg).subs(sol)))))
        assert all(mon[0] % 2 == 0 for mon in sp.Poly(e, q).monoms())
        eqs.append(sp.expand(e.subs(q, sp.sqrt(q2))))
    return eqs, hs, q2


def split_q2(e, q2):
    p = sp.Poly(e, q2)
    assert p.degree() <= 1
    return p.coeff_monomial(q2), p.coeff_monomial(1)


def check_degree_four() -> None:
    print("     shape: y^4-4b-Q^2 = -q^2 (y-s)^2 H^3, H monic quadratic; s = 1 or s = 0")
    print("     (s != 0 is scaled to 1 by y -> s*y, b -> b/s^4; b stays a free unknown)")
    eqs, (h0, h1), q2 = deg_system(4, 2, 2, 1)
    e3, e2, e1, e0 = eqs  # coefficients of y^3, y^2, y^1, y^0
    ok(all(not e.has(b) for e in (e3, e2, e1)), "s=1: the y^3, y^2, y^1 equations do not involve b")
    AC = [split_q2(e, q2) for e in (e3, e2, e1)]
    R2 = sp.Poly(sp.expand(AC[0][0] * AC[1][1] - AC[1][0] * AC[0][1]), h0, h1)
    R3 = sp.Poly(sp.expand(AC[0][0] * AC[2][1] - AC[2][0] * AC[0][1]), h0, h1)
    g = sp.gcd(R2, R3)
    ok(same_factors(g, [4 * h0 - h1**2], (h0, h1)),
       "s=1: after eliminating q^2, gcd of the two eliminants = const*(4h0-h1^2)^j")
    U = sp.Poly(sp.resultant(exact_quo(R2, g).as_expr(), exact_quo(R3, g).as_expr(), h0), h1)
    ok(not U.is_zero and rational_roots(U) == [-2],
       "s=1, off 4h0 = h1^2: h1 is a root of a nonzero eliminant whose only rational root is -2")
    ok(nonzero_constant(e3.subs(h1, -2)), "s=1, h1=-2: the y^3 equation is a nonzero constant")
    on = [sp.expand(e.subs(h0, h1**2 / 4)) for e in (e3, e2, e1)]
    ok(all(not e.has(q2) for e in on) and no_common_root(on, h1),
       "s=1, on 4h0 = h1^2: the y^3, y^2, y^1 equations lose q and have no common root")
    eqs, (h0, h1), q2 = deg_system(4, 2, 2, 0)
    e3, e2, e1, e0 = eqs
    ok(proportional(e3, h1 * (q2 * (4 * h0 - h1**2) ** 2 + 64)),
       "s=0: y^3 equation = c*h1*(q^2(4h0-h1^2)^2 + 64), and the bracket is > 0, so h1 = 0")
    ok(proportional(e2.subs(h1, 0), h0 * (q2 * h0**2 + 12)),
       "s=0, h1=0: y^2 equation = c*h0*(q^2 h0^2 + 12), so h0 = 0")
    ok(sp.expand(e1.subs({h0: 0, h1: 0})) == 0, "s=0, H = y^2: the y^1 equation holds")
    ok(proportional(e0.subs({h0: 0, h1: 0}), 16 * b * q2 + 1),
       "s=0, H = y^2: the y^0 equation is c*(16 b q^2 + 1), i.e. b = -1/(16 q^2)")
    for bv in A0_BS:
        ok(not is_rational_square(sp.Rational(-1, 16 * bv)),
           "s=0: b=%d is not of the form -1/(16 q^2), q in QQ" % bv)


def check_degree_five() -> None:
    print("     shape: y^4-4b-Q^2 = -q^2 (y-s) H^3, H monic cubic; s = 1 or s = 0")
    for s_val in (1, 0):
        eqs, (h0, h1, h2), q2 = deg_system(5, 3, 1, s_val)
        top = eqs[0]  # coefficient of y^4
        ok(all(not e.has(b) for e in eqs[:4]),
           "s=%d: the y^4..y^1 equations do not involve b" % s_val)
        P = []
        for e in eqs[1:4]:
            aq, cq = split_q2(e, q2)
            assert cq == 0
            P.append(sp.Poly(aq, h0, h1, h2))
        ok(True, "s=%d: the y^3, y^2, y^1 equations are q^2*P_i(h0,h1,h2); q != 0, so P_i = 0"
           % s_val)
        R12 = sp.Poly(sp.resultant(P[0].as_expr(), P[1].as_expr(), h0), h1, h2)
        R13 = sp.Poly(sp.resultant(P[0].as_expr(), P[2].as_expr(), h0), h1, h2)
        g = sp.gcd(R12, R13)
        U = sp.Poly(sp.resultant(exact_quo(R12, g).as_expr(), exact_quo(R13, g).as_expr(), h1), h2)
        if s_val == 1:
            curve = 4 * h1 - h2**2 + 2 * h2 + 3
            ok(same_factors(g, [curve], (h1, h2)),
               "s=1: gcd of the h0-resultants = const*(4h1 - h2^2 + 2h2 + 3)^j")
            ok(not U.is_zero and rational_roots(U) == [-3],
               "s=1, off that curve: h2 is a root of a nonzero eliminant, rational root only -3")
            P3 = [p.as_expr().subs(h2, -3) for p in P]
            r12 = sp.Poly(sp.resultant(P3[0], P3[1], h0), h1)
            r13 = sp.Poly(sp.resultant(P3[0], P3[2], h0), h1)
            ok(not r12.is_zero and not r13.is_zero and rational_roots(sp.gcd(r12, r13)) == [3],
               "s=1, h2=-3: h1 = 3 is forced")
            ok(rational_roots(sp.gcd(sp.gcd(sp.Poly(P3[0].subs(h1, 3), h0),
                                            sp.Poly(P3[1].subs(h1, 3), h0)),
                                     sp.Poly(P3[2].subs(h1, 3), h0))) == [-1],
               "s=1, (h1,h2)=(3,-3): h0 = -1 is forced, i.e. H = (y-1)^3")
            ok(nonzero_constant(top.subs({h0: -1, h1: 3, h2: -3})),
               "s=1, H = (y-1)^3: the y^4 equation is a nonzero constant")
            sub = {h1: (h2**2 - 2 * h2 - 3) / 4}
            fac = 4 * h0 + (h2 + 1) ** 2
            fac_sub = {h0: -(h2 + 1) ** 2 / 4}
        else:
            curve = 4 * h1 - h2**2
            other = 48 * h1**2 - 72 * h1 * h2**2 + 23 * h2**4
            ok(same_factors(g, [curve, other], (h1, h2)),
               "s=0: gcd of the h0-resultants = c*(4h1 - h2^2)^i*(48h1^2 - 72h1h2^2 + 23h2^4)^j")
            ok(not is_rational_square(72**2 - 4 * 48 * 23),
               "s=0: 48u^2 - 72u + 23 has no rational root, so the second factor needs h1=h2=0")
            ok(not U.is_zero and rational_roots(U) == [0],
               "s=0, off those curves: h2 is a root of a nonzero eliminant, rational root only 0")
            P0 = [p.as_expr().subs(h2, 0) for p in P]
            ok(proportional(P0[0], h0 * h1**2) and proportional(P0[1].subs(h0, 0), h1**4)
               and proportional(P0[2].subs(h1, 0), h0**3),
               "s=0, h2=0: P_1 = c h0 h1^2, P_2(0,h1) = c h1^4, P_3(h0,0) = c h0^3, so h = 0")
            ok(nonzero_constant(top.subs({h0: 0, h1: 0, h2: 0})),
               "s=0, H = y^3: the y^4 equation is a nonzero constant")
            sub = {h1: h2**2 / 4}
            fac = h0
            fac_sub = {h0: 0}
        Pb = [sp.Poly(sp.expand(p.as_expr().subs(sub)), h0, h2) for p in P]
        common = sp.gcd(sp.gcd(Pb[0], Pb[1]), Pb[2])
        ok(same_factors(common, [fac], (h0, h2)),
           "s=%d, on the curve 4h1 = %s: the P_i share exactly the factor %s"
           % (s_val, sp.expand(4 * sub[h1]), fac))
        red = [exact_quo(p, common) for p in Pb]
        rr12 = sp.Poly(sp.resultant(red[0].as_expr(), red[1].as_expr(), h0), h2)
        rr13 = sp.Poly(sp.resultant(red[0].as_expr(), red[2].as_expr(), h0), h2)
        ok(not rr12.is_zero and not rr13.is_zero and sp.gcd(rr12, rr13).is_ground,
           "   ... off that factor the P_i have no common zero")
        ok(nonzero_constant(top.subs(sub).subs(fac_sub)),
           "   ... on it the y^4 equation is a nonzero constant")


# ---------------------------------------------------------------------------
# 6. polynomial components x = X(y): deg A <= 1 (lines) and deg A = 3
# ---------------------------------------------------------------------------
def check_polynomial_components() -> None:
    xi, eta, tau, x1, x0 = sp.symbols("xi eta tau x1 x0")
    for a, bv in SIX:
        ok(rational_roots(sp.Poly(x**3 + a * x + bv, x)) == [],
           "(%d,%d): N(x) has no rational root, so x is not constant on any C_A" % (a, bv))
        # deg A <= 1, X = xi*y + eta, xi != 0: the y^3, y^2 coefficients force alpha, beta
        F1 = 3 * eta**2 + 6 * xi**4 * eta + 2 * xi**8 + a
        F0 = eta**3 + a * eta + bv + (xi**6 + 3 * xi**2 * eta) ** 2
        alpha, beta = -xi**3, -xi**6 - 3 * xi**2 * eta
        Q = y**2 + 2 * (alpha * y + beta)
        X = xi * y + eta
        res = sp.Poly(sp.expand(y**4 - Q**2 - 4 * (X**3 + a * X + bv)), y)
        ok(res.coeff_monomial(y**3) == 0 and res.coeff_monomial(y**2) == 0
           and sp.expand(res.coeff_monomial(y) + 4 * xi * F1) == 0
           and sp.expand(res.coeff_monomial(1) + 4 * F0) == 0,
           "(%d,%d): x = xi*y+eta, z = alpha*y+beta on S iff F1 = F0 = 0 (xi != 0)" % (a, bv))
        U = sp.Poly(sp.resultant(F1, F0, eta), xi)
        ok(U.degree() > 0 and rational_roots(U) == [],
           "(%d,%d): the xi-eliminant (degree %d) has no rational root" % (a, bv, U.degree()))
        # deg A = 3, X = -tau^2 y^2 + x1 y + x0, Q = 2 tau^3 y^3 + ..., tau != 0
        Qs = sp.symbols("Q2 Q1 Q0")
        X = -tau**2 * y**2 + x1 * y + x0
        Q = 2 * tau**3 * y**3 + Qs[0] * y**2 + Qs[1] * y + Qs[2]
        diff = sp.Poly(sp.expand(Q**2 - (y**4 - 4 * bv - 4 * X**3 - 4 * a * X)), y)
        assert diff.coeff_monomial(y**6) == 0
        sol = {}
        for deg, var in zip((5, 4, 3), Qs):
            lin = sp.Poly(sp.expand(diff.coeff_monomial(y**deg).subs(sol)), var)
            assert sp.expand(lin.coeff_monomial(var) - 4 * tau**3) == 0
            sol[var] = sp.together(-lin.coeff_monomial(1) / lin.coeff_monomial(var))
        E = [sp.numer(sp.together(diff.coeff_monomial(y**deg).subs(sol))) for deg in (2, 1, 0)]
        R12 = sp.Poly(sp.resultant(E[0], E[1], x0), tau, x1)
        R13 = sp.Poly(sp.resultant(E[0], E[2], x0), tau, x1)
        g = sp.gcd(R12, R13)
        ok(same_factors(g, [tau], (tau, x1)),
           "(%d,%d): deg A = 3: gcd of the x0-eliminants is const*tau^j" % (a, bv))
        U = sp.Poly(sp.resultant(exact_quo(R12, g).as_expr(), exact_quo(R13, g).as_expr(), x1), tau)
        ok(not U.is_zero and rational_roots(U) == [0],
           "(%d,%d): deg A = 3: tau-eliminant (degree %d) has only the excluded rational root 0"
           % (a, bv, U.degree()))


def check_constant_z() -> None:
    for bv in A0_BS:
        ok(not is_rational_square(-bv) and not is_rational_power(-bv, 3),
           "a=0, b=%d: z constant: -b is neither a square nor a cube (genus 1 or no point)" % bv)


def main() -> None:
    print("== 0. substitution")
    check_identity()
    print("== 1. a = 0, deg A = 2: triple-root classification")
    check_degree_two_a0()
    print("== 2. rational points of C_b : k^2 = r^4 - 4b")
    check_cb_points()
    print("== 3. explicit families (b = -2, 3) and their integrality obstruction")
    check_families()
    check_obstructions()
    print("== 4. a = -1")
    check_a_minus1()
    print("== 5. a = 0, deg A = 4, 5")
    check_degree_four()
    check_degree_five()
    print("== 6. polynomial components x = X(y) and constant z")
    check_polynomial_components()
    check_constant_z()
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
