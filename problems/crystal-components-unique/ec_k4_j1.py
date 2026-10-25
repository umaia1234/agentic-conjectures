"""The k = 4 family and the j = 1 family never share n (Sage computation, not Lean).

A k = 4 crystal is {2t^2 - 1, 2(t + 1)^2 - 1} with t >= 2, so n + 1 = 4X(X - 1) with X = t(t + 1).
A j = 1 crystal with k = K is {2K - 1, 2(K - 1)^2 - 1}, so n + 1 = 2K(K - 1)(2K - 3).
Equal n means (2X - 1)^2 = 4K^3 - 10K^2 + 6K + 1, so (x, y) = (4K, 4(2X - 1)) is an integral point
of E: y^2 = x^3 - 10x^2 + 24x + 16.

The script proves rank E(Q) = 2 (PARI ellrank), shows that two points found by ellrank generate
E(Q) (an index bound from a lower bound for the canonical height, then PARI ellsaturation at every
prime up to a much larger bound), lists all integral points (Sage, from that Mordell-Weil basis)
and converts them back to (t, K).  The only solution with t >= 2 and K >= 3 is t = 2, K = 4:
n = 119 = 7 * 17, the single crystal with k = 4 and j = 1.

Run with `sage -python ec_k4_j1.py`, or with a Python that has the pip packages
passagemath-schemes, passagemath-pari and passagemath-symbolics.
"""
try:                                    # SageMath
    from sage.all import *
except ImportError:                     # the modular passagemath distributions
    from sage.all__sagemath_schemes import *
    from sage.all__sagemath_pari import *
    from sage.all__sagemath_symbolics import *

E = EllipticCurve(QQ, [0, -10, 0, 24, 16])
print(E, "| conductor", E.conductor(), "| torsion order", E.torsion_order())
assert E.torsion_order() == 1
pe = pari(E)
rk = pe.ellrank()
print("PARI ellrank [r, R, s, L]:", rk)
assert rk[0] == rk[1] == 2          # lower and upper bound for the rank agree

# If the points P generate a subgroup of index n, then Reg(P) = n^2 Reg(E(Q)) and, by Hermite's
# inequality, Reg(E(Q)) >= (lambda / gamma_2)^2, where lambda bounds the canonical height of every
# non-torsion point from below and gamma_2^2 = 4/3.  Heights and regulators below use Sage's
# normalization throughout.
P = [E(list(Q)) for Q in rk[3]]
R = E.regulator_of_points(P)
lam = E.height_function().min(0.0001, 5)
index_bound = sqrt(R * RR(4 / 3)) / lam
print("lower bound for canonical heights of non-torsion points:", lam)
print("regulator of the ellrank points:", R, "=> index bound:", index_bound)
B = 100
assert index_bound < B
sat = pe.ellsaturation(rk[3], B)
gens = [E(list(Q)) for Q in sat]
Rs = E.regulator_of_points(gens)
print("PARI ellsaturation at all primes <=", B, ":", sat, "| regulator:", Rs)
assert abs(Rs - R) < 1e-10 * R      # already saturated: the points generate E(Q)

pts = E.integral_points(mw_base=gens, both_signs=False)
print("integral points (one of each pair +-P):", pts)
sols = set()
for Q in pts:
    x, y = ZZ(Q[0]), ZZ(Q[1])
    for yy in {y, -y}:
        if x % 4 == 0 and yy % 4 == 0 and (yy // 4 + 1) % 2 == 0:
            sols.add((x // 4, (yy // 4 + 1) // 2))
print("(K, X):", sorted(sols))
found = []
for K, X in sorted(sols):
    s = 4 * X + 1
    if s >= 1 and s.is_square():
        t = (s.isqrt() - 1) // 2
        print("  t =", t, "K =", K, "n(k=4, t) =", (2 * t * t - 1) * (2 * (t + 1) ** 2 - 1),
              "n(j=1, K) =", (2 * K - 1) * (2 * (K - 1) ** 2 - 1))
        if t >= 2 and K >= 3:
            found.append((t, K))
assert found == [(2, 4)]
print("only solution with t >= 2, K >= 3: t = 2, K = 4 (n = 119, the crystal 7 * 17 itself)")

# Sanity check, not part of the argument: a direct search over 0 <= K <= 10^6 finds the same K.
direct = [K for K in range(10**6 + 1) if ZZ(4 * K**3 - 10 * K**2 + 6 * K + 1).is_square()]
print("direct search, K <= 10^6:", direct)
assert direct == sorted({K for K, X in sols})
