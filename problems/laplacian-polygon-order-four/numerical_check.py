#!/usr/bin/env python3
"""Independent floating-point check of the order-4 polygon question (pure Python).

Unscaled arc weights b_ij in [0, 1] (i != j) give L = D - B; z is an eigenvalue of a
standardized Laplacian of order 4 exactly when 4 z is an eigenvalue of such an L.  So
Lambda_4 = S_4 reads |Im w| <= 1, |Im w| <= Re w and |Im w| <= 4 - Re w for every
eigenvalue w of every L.

This script shares no code with face_certificate.py.  Characteristic polynomials come from
the Faddeev-LeVerrier recursion and eigenvalues from Durand-Kerner iteration.  It checks

 1. on random weights, the identity Phi = prod_{a<b} ((r_a - r_b)^2 + 4) over the three
    eigenvalues other than 0, with Phi computed from s1, s2, s3 as in Basic.lean, and the
    identity Psi = e1 e2 - e3 for the squares r_a^2;
 2. by multi-start local ascent, that max Im w stays <= 1 (it reaches 1 on the 4-cycle),
    and that |Im w| - Re w and |Im w| - (4 - Re w) stay <= 0.

Usage: python3 numerical_check.py [--starts N] [--samples N] [--seed S]
"""
import argparse
import cmath
import random
import sys

ARCS = [(i, j) for i in range(4) for j in range(4) if i != j]
TOL = 1e-7


def lap(b):
    L = [[0.0] * 4 for _ in range(4)]
    for (i, j), w in zip(ARCS, b):
        L[i][j] -= w
        L[i][i] += w
    return L


def charpoly(A):
    """Coefficients c[0..4] of det(x - A) = sum c_k x^k (Faddeev-LeVerrier)."""
    n = 4
    c = [0.0] * (n + 1)
    c[n] = 1.0
    M = [[0.0] * n for _ in range(n)]
    for k in range(1, n + 1):
        AM = [[sum(A[i][m] * M[m][j] for m in range(n)) for j in range(n)] for i in range(n)]
        M = [[AM[i][j] + (c[n - k + 1] if i == j else 0.0) for j in range(n)] for i in range(n)]
        AM = [[sum(A[i][m] * M[m][j] for m in range(n)) for j in range(n)] for i in range(n)]
        c[n - k] = -sum(AM[i][i] for i in range(n)) / k
    return c


def roots(c):
    """Roots of the monic quartic sum c_k x^k by Durand-Kerner iteration."""
    def p(x):
        return (((x + c[3]) * x + c[2]) * x + c[1]) * x + c[0]
    R = 1 + max(abs(v) for v in c[:4])
    z = [R * (0.4 + 0.9j) ** k for k in range(4)]
    for _ in range(500):
        delta = 0.0
        for k in range(4):
            den = 1
            for j in range(4):
                if j != k:
                    den *= z[k] - z[j]
            if den == 0:
                den = 1e-300
            step = p(z[k]) / den
            z[k] -= step
            delta = max(delta, abs(step))
        if delta < 1e-15 * R:
            break
    return z


def eigs(b):
    return roots(charpoly(lap(b)))


def identity_errors(b):
    c = charpoly(lap(b))
    s1, s2, s3 = -c[3], c[2], -c[1]
    phi = (s1 ** 2 * s2 ** 2 - 4 * s2 ** 3 - 4 * s1 ** 3 * s3 + 18 * s1 * s2 * s3
           - 27 * s3 ** 2 + 4 * (s1 ** 2 - 3 * s2 + 4) ** 2)
    psi = (s1 ** 2 - 2 * s2) * (s2 ** 2 - 2 * s1 * s3) - s3 ** 2
    r = sorted(roots(c), key=abs)[1:]  # drop the eigenvalue 0
    prod = 1
    for a in range(3):
        for d in range(a + 1, 3):
            prod *= (r[a] - r[d]) ** 2 + 4
    y = [x * x for x in r]
    e1, e2, e3 = sum(y), y[0] * y[1] + y[0] * y[2] + y[1] * y[2], y[0] * y[1] * y[2]
    psi_r = e1 * e2 - e3
    return (abs(phi - prod) / max(1.0, abs(phi)), abs(psi - psi_r) / max(1.0, abs(psi)))


OBJECTIVES = {
    "Im w": lambda w: w.imag,
    "|Im w| - Re w": lambda w: abs(w.imag) - w.real,
    "|Im w| - (4 - Re w)": lambda w: abs(w.imag) - (4 - w.real),
}


def score(b, f):
    return max(f(w) for w in eigs(b))


def start_point(rng, kind):
    if kind == 0:
        return [rng.random() for _ in ARCS]
    if kind == 1:
        return [float(rng.random() < 0.5) for _ in ARCS]
    # near the directed 4-cycle 0 -> 1 -> 2 -> 3 -> 0, relabelled at random
    perm = list(range(4))
    rng.shuffle(perm)
    cyc = {(perm[k], perm[(k + 1) % 4]) for k in range(4)}
    return [1.0 if a in cyc else 0.3 * rng.random() for a in ARCS]


def ascend(b, f, rng, iters):
    best = score(b, f)
    step = 0.3
    for _ in range(iters):
        cand = list(b)
        for k in rng.sample(range(12), rng.randint(1, 3)):
            cand[k] = min(1.0, max(0.0, cand[k] + rng.gauss(0, step)))
        v = score(cand, f)
        if v > best:
            b, best = cand, v
        else:
            step = max(1e-4, step * 0.97)
    return best, b


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--starts", type=int, default=30, help="ascent starts per objective")
    ap.add_argument("--iters", type=int, default=400, help="ascent steps per start")
    ap.add_argument("--samples", type=int, default=2000, help="random identity samples")
    ap.add_argument("--seed", type=int, default=2026)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    ok = True
    worst_phi = worst_psi = 0.0
    for _ in range(args.samples):
        b = [rng.random() if rng.random() < 0.7 else float(rng.random() < 0.5) for _ in ARCS]
        e_phi, e_psi = identity_errors(b)
        worst_phi, worst_psi = max(worst_phi, e_phi), max(worst_psi, e_psi)
    print(f"identities on {args.samples} samples: max relative error {worst_phi:.1e} (Phi), "
          f"{worst_psi:.1e} (Psi)")
    ok &= worst_phi < 1e-8 and worst_psi < 1e-8
    for name, f in OBJECTIVES.items():
        best, arg = float("-inf"), None
        for s in range(args.starts):
            v, b = ascend(start_point(rng, s % 3), f, rng, args.iters)
            if v > best:
                best, arg = v, b
        bound = 1.0 if name == "Im w" else 0.0
        good = best <= bound + TOL
        ok &= good
        print(f"max of {name} over {args.starts} ascents: {best:.9f} "
              f"(bound {bound:g}){'' if good else '  VIOLATION at ' + repr(arg)}")
    print("RESULT: no eigenvalue outside S_4 found" if ok else "RESULT: CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
