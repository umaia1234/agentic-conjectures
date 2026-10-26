#!/usr/bin/env python3
"""Exact certificate for the two face inequalities of the order-4 polygon question.

Arc weights b_ij in [0, 1] (i != j) give the Laplacian L = D - B, and
det(x - L) = x (x^3 - s1 x^2 + s2 x - s3), where s_k is the sum of the k x k principal
minors of L.  The Lean module `AgenticConjectures.LaplacianPolygonOrderFour` defines

    Phi = s1^2 s2^2 - 4 s2^3 - 4 s1^3 s3 + 18 s1 s2 s3 - 27 s3^2 + 4 (s1^2 - 3 s2 + 4)^2,
    Psi = (s1^2 - 2 s2) (s2^2 - 2 s1 s3) - s3^2,

and proves Question 1 (Lambda_4 = S_4) from `FaceBound` (Phi >= 0) and `SectorFaceBound`
(Psi >= 0), both for all weights with at most four fractional entries, at most two per row.
This script checks both inequalities with integer and fraction arithmetic only:

 1. Such weights lie on the face of a maximal pattern: four free arcs ('F', at most two per
    row, the k-th one carrying t_k in [0, 1]) and eight arcs fixed at 0 or 1.  There are
    117504 patterns.
 2. Relabelling the vertices fixes s1, s2, s3, and the complement b -> 1 - b maps them by an
    affine map that fixes Phi.  Both facts are checked below as polynomial identities.  So
    Phi needs one face per orbit of S4 x {id, complement}, and Psi one per orbit of S4.
 3. On each orbit representative the face polynomial P(t0, ..., t3) is shown to be >= 0 on
    [0, 1]^4: either all its Bernstein coefficients on the box are >= 0, or the box is cut
    into the 24 Kuhn simplices through one corner, simplices are split along edges (each
    split replaces a simplex by two that cover it), and on every final simplex all
    coefficients of P in barycentric coordinates are >= 0.
 4. Each face polynomial is compared, at random rational points, with a separate evaluation
    of the Lean formulas for s1, s2, s3 (`σ₁`, `c2`, `c3`, `det3` in Basic.lean).

The search is deterministic, so the table of methods it prints can be compared with the
committed face_orbits.tsv.  Usage:

    python3 face_certificate.py [--jobs N] [--table face_orbits.tsv] [--write-table FILE]
"""
import argparse
import itertools
import os
import random
import sys
import time
from fractions import Fraction
from math import gcd
from multiprocessing import Pool

ARCS = [(i, j) for i in range(4) for j in range(4) if i != j]
IDX = {a: k for k, a in enumerate(ARCS)}
PERMS = list(itertools.permutations(range(4)))
NV = 4


# ---------- sparse polynomials over Z: {exponent tuple: nonzero int} ----------

def padd(a, b, s=1):
    out = dict(a)
    for e, c in b.items():
        v = out.get(e, 0) + s * c
        if v:
            out[e] = v
        else:
            out.pop(e, None)
    return out


def pmul(a, b):
    out = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            e = tuple(x + y for x, y in zip(ea, eb))
            out[e] = out.get(e, 0) + ca * cb
    return {e: c for e, c in out.items() if c}


def pscale(a, s):
    return {e: s * c for e, c in a.items()} if s else {}


def pconst(c, n):
    return {(0,) * n: c} if c else {}


def pvar(k, n):
    return {tuple(1 if i == k else 0 for i in range(n)): 1}


def ppow(a, k, n):
    r = pconst(1, n)
    for _ in range(k):
        r = pmul(r, a)
    return r


# ---------- Laplacian, s1, s2, s3, Phi and Psi ----------

def lap_matrix(w, n):
    """L = D - B for arc weights w (dict arc -> polynomial in n variables)."""
    L = [[{} for _ in range(4)] for _ in range(4)]
    for (i, j), x in w.items():
        L[i][j] = padd(L[i][j], x, -1)
        L[i][i] = padd(L[i][i], x)
    return L


def det_poly(M):
    if len(M) == 1:
        return M[0][0]
    tot = {}
    for c in range(len(M)):
        minor = [row[:c] + row[c + 1:] for row in M[1:]]
        tot = padd(tot, pmul(M[0][c], det_poly(minor)), -1 if c % 2 else 1)
    return tot


def sigmas(L):
    out = []
    for k in (1, 2, 3):
        tot = {}
        for S in itertools.combinations(range(4), k):
            tot = padd(tot, det_poly([[L[i][j] for j in S] for i in S]))
        out.append(tot)
    return out


def phi_of(s1, s2, s3, n):
    s1s, s2s = pmul(s1, s1), pmul(s2, s2)
    disc = pmul(s1s, s2s)
    disc = padd(disc, pmul(s2s, s2), -4)
    disc = padd(disc, pmul(pmul(s1s, s1), s3), -4)
    disc = padd(disc, pscale(pmul(pmul(s1, s2), s3), 18))
    disc = padd(disc, pscale(pmul(s3, s3), -27))
    h = padd(padd(s1s, pscale(s2, -3)), pconst(4, n))
    return padd(disc, pscale(pmul(h, h), 4))


def psi_of(s1, s2, s3):
    e1 = padd(pmul(s1, s1), pscale(s2, -2))
    e2 = padd(pmul(s2, s2), pscale(pmul(s1, s3), -2))
    return padd(pmul(e1, e2), pmul(s3, s3), -1)


def face_weights(pattern):
    w, k = {}, 0
    for ch, a in zip(pattern, ARCS):
        if ch == "F":
            w[a] = pvar(k, NV)
            k += 1
        elif ch == "1":
            w[a] = pconst(1, NV)
    return w


def face_polys(pattern):
    s1, s2, s3 = sigmas(lap_matrix(face_weights(pattern), NV))
    return phi_of(s1, s2, s3, NV), psi_of(s1, s2, s3)


# ---------- step 2: symmetry identities ----------

def check_symmetry():
    n = 12
    gen = {a: pvar(k, n) for k, a in enumerate(ARCS)}
    S = sigmas(lap_matrix(gen, n))
    for perm in [(1, 0, 2, 3), (1, 2, 3, 0)]:  # generators of S4
        moved = {(perm[i], perm[j]): gen[(i, j)] for (i, j) in ARCS}
        if sigmas(lap_matrix(moved, n)) != S:
            return False
    s1, s2, s3 = S
    comp = {a: padd(pconst(1, n), gen[a], -1) for a in ARCS}
    want = [padd(pconst(12, n), s1, -1),
            padd(padd(pconst(48, n), pscale(s1, -8)), s2),
            padd(padd(padd(pconst(64, n), pscale(s1, -16)), pscale(s2, 4)), s3, -1)]
    if sigmas(lap_matrix(comp, n)) != want:
        return False
    a, b, c = (pvar(k, 3) for k in range(3))
    a2 = padd(pconst(12, 3), a, -1)
    b2 = padd(padd(pconst(48, 3), pscale(a, -8)), b)
    c2 = padd(padd(padd(pconst(64, 3), pscale(a, -16)), pscale(b, 4)), c, -1)
    return phi_of(a2, b2, c2, 3) == phi_of(a, b, c, 3)


# ---------- step 1: patterns and orbits ----------

def maximal_patterns():
    out = []
    for free in itertools.combinations(range(12), 4):
        if any(sum(1 for k in free if k // 3 == r) > 2 for r in range(4)):
            continue
        rest = [k for k in range(12) if k not in free]
        for bits in itertools.product("01", repeat=8):
            p = ["F"] * 12
            for k, ch in zip(rest, bits):
                p[k] = ch
            out.append("".join(p))
    return out


TARGET = {perm: [IDX[(perm[i], perm[j])] for (i, j) in ARCS] for perm in PERMS}
FLIP = {"0": "1", "1": "0", "F": "F"}


def act(p, perm, comp):
    out = [""] * 12
    for k, t in enumerate(TARGET[perm]):
        out[t] = FLIP[p[k]] if comp else p[k]
    return "".join(out)


def orbits(patterns, comps):
    rep_of = {}
    for p in patterns:
        if p in rep_of:
            continue
        imgs = {act(p, perm, c) for perm in PERMS for c in comps}
        r = min(imgs)
        for q in imgs:
            rep_of[q] = r
    sizes = {}
    for r in rep_of.values():
        sizes[r] = sizes.get(r, 0) + 1
    return rep_of, sizes


# ---------- step 3: Bernstein certificates ----------

def bern_1d(a):
    d = len(a) - 1
    out = []
    for k in range(d + 1):
        tot, cf = 0, 1  # cf = C(d - j, k - j), updated from j = k downwards
        for j in range(k, -1, -1):
            tot += a[j] * cf
            if j:
                cf = cf * (d - j + 1) // (k - j + 1)
        out.append(tot)
    return out


def box_ok(P):
    """All Bernstein coefficients of P on [0, 1]^4 (times positive integers) are >= 0."""
    sh = [max([e[i] for e in P] + [0]) + 1 for i in range(NV)]
    strides = [sh[1] * sh[2] * sh[3], sh[2] * sh[3], sh[3], 1]
    A = [0] * (sh[0] * strides[0])
    for e, c in P.items():
        A[sum(x * s for x, s in zip(e, strides))] = c
    for ax in range(NV):
        st, n = strides[ax], sh[ax]
        others = [range(sh[i]) if i != ax else range(1) for i in range(NV)]
        for idx in itertools.product(*others):
            base = sum(i * s for i, s in zip(idx, strides))
            new = bern_1d([A[base + k * st] for k in range(n)])
            for k in range(n):
                A[base + k * st] = new[k]
    return min(A) >= 0


def eval_at(P, pt):
    tot = Fraction(0)
    for e, c in P.items():
        term = Fraction(c)
        for k in range(NV):
            if e[k]:
                term *= pt[k] ** e[k]
        tot += term
    return tot


def simplex_ok(P, V):
    """All coefficients of the degree-d form P(sum_j th_j V_j) (sum th_j)^(d - deg) >= 0."""
    m = len(V)
    den = 1
    for v in V:
        for x in v:
            den = den * x.denominator // gcd(den, x.denominator)
    unit = [tuple(1 if jj == j else 0 for jj in range(m)) for j in range(m)]
    lin = [{unit[j]: int(V[j][k] * den) for j in range(m) if V[j][k] != 0} for k in range(NV)]
    ssum = {unit[j]: den for j in range(m)}
    d = max(sum(e) for e in P)
    cache = {}

    def pw(key, base, k):
        if (key, k) not in cache:
            cache[(key, k)] = ppow(base, k, m)
        return cache[(key, k)]

    out = {}
    for e, c in P.items():
        term = pconst(c, m)
        for k in range(NV):
            if e[k]:
                term = pmul(term, pw(k, lin[k], e[k]))
        if d - sum(e):
            term = pmul(term, pw("s", ssum, d - sum(e)))
        out = padd(out, term)
    return min(out.values(), default=0) >= 0


def grad_hess(P, V):
    g = [Fraction(0)] * NV
    H = [[Fraction(0)] * NV for _ in range(NV)]
    for e, c in P.items():
        for k in range(NV):
            if e[k] == 0:
                continue
            t = Fraction(c * e[k])
            for m in range(NV):
                p = e[m] - (m == k)
                if p:
                    t *= V[m] ** p
            g[k] += t
            for l in range(NV):
                el = e[l] - (l == k)
                if el == 0:
                    continue
                t2 = Fraction(c * e[k] * el)
                for m in range(NV):
                    p = e[m] - (m == k) - (m == l)
                    if p:
                        t2 *= V[m] ** p
                H[k][l] += t2
    return g, H


def split_point(P, V):
    """Edge (i, j) and ratio for splitting a simplex: at a vertex where P vanishes, split the
    edge between two directions in which P grows only quadratically and whose quadratic
    forms have a negative cross term; otherwise bisect the longest edge."""
    for j0, W in enumerate(V):
        if eval_at(P, W) != 0:
            continue
        g, H = grad_hess(P, W)
        dirs = {k: [a - b for a, b in zip(V[k], W)] for k in range(len(V)) if k != j0}
        flat = [k for k, dk in dirs.items() if sum(x * y for x, y in zip(g, dk)) == 0]
        best = None
        for k, l in itertools.combinations(flat, 2):
            q = [[sum(dirs[u][a] * H[a][b] * dirs[v][b] for a in range(NV) for b in range(NV))
                  for v in (k, l)] for u in (k, l)]
            if q[0][1] < 0 < q[0][0] and q[1][1] > 0 and (best is None or q[0][1] < best[0]):
                best = (q[0][1], k, l, q[0][0] / (q[0][0] - q[0][1]))
        if best:
            return best[1], best[2], best[3]
    pairs = itertools.combinations(range(len(V)), 2)
    i, j = max(pairs, key=lambda ij: sum((a - b) ** 2 for a, b in zip(V[ij[0]], V[ij[1]])))
    return i, j, Fraction(1, 2)


def refine(P, V, budget):
    """Number of final simplices covering V on which P is certified >= 0, or None."""
    if simplex_ok(P, V):
        return 1
    if budget == 0:
        return None
    i, j, lam = split_point(P, V)
    M = tuple(a + lam * (b - a) for a, b in zip(V[i], V[j]))
    total = 0
    for side in (i, j):
        W = list(V)
        W[side] = M
        n = refine(P, W, budget - 1)
        if n is None:
            return None
        total += n
    return total


def kuhn(corner):
    """The 24 Kuhn simplices of [0, 1]^4 through the given corner."""
    sims = []
    for perm in itertools.permutations(range(NV)):
        cur = [Fraction(c) for c in corner]
        V = [tuple(cur)]
        for k in perm:
            cur[k] = 1 - cur[k]
            V.append(tuple(cur))
        sims.append(V)
    return sims


def certify(P, budget=6):
    """(method, number of pieces) if P >= 0 on [0, 1]^4 is certified, else ('FAIL', 0)."""
    if not P or box_ok(P):
        return "box", 1
    corners = list(itertools.product((0, 1), repeat=NV))
    corners.sort(key=lambda c: eval_at(P, c) != 0)  # corners where P vanishes first
    for c in corners:
        total = 0
        for V in kuhn(c):
            n = refine(P, V, budget)
            if n is None:
                break
            total += n
        else:
            return "kuhn" + "".join(map(str, c)), total
    return "FAIL", 0


# ---------- step 4: the Lean formulas, evaluated directly ----------

def det3(a, b, c, d, e, f, g, h, i):
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def lean_values(pattern, t):
    """Phi and Psi at the point t of the face, from the formulas of Basic.lean."""
    b, k = {}, 0
    for ch, a in zip(pattern, ARCS):
        if ch == "F":
            b[a] = t[k]
            k += 1
        else:
            b[a] = Fraction(int(ch))
    A = [[(sum(b[(i, j)] for j in range(4) if j != i) if i == j else -b[(i, j)])
          for j in range(4)] for i in range(4)]
    s1 = A[0][0] + A[1][1] + A[2][2] + A[3][3]
    s2 = (A[0][0] * A[1][1] - A[0][1] * A[1][0] + (A[0][0] * A[2][2] - A[0][2] * A[2][0])
          + (A[0][0] * A[3][3] - A[0][3] * A[3][0]) + (A[1][1] * A[2][2] - A[1][2] * A[2][1])
          + (A[1][1] * A[3][3] - A[1][3] * A[3][1]) + (A[2][2] * A[3][3] - A[2][3] * A[3][2]))
    s3 = (det3(A[1][1], A[1][2], A[1][3], A[2][1], A[2][2], A[2][3], A[3][1], A[3][2], A[3][3])
          + det3(A[0][0], A[0][2], A[0][3], A[2][0], A[2][2], A[2][3], A[3][0], A[3][2], A[3][3])
          + det3(A[0][0], A[0][1], A[0][3], A[1][0], A[1][1], A[1][3], A[3][0], A[3][1], A[3][3])
          + det3(A[0][0], A[0][1], A[0][2], A[1][0], A[1][1], A[1][2], A[2][0], A[2][1], A[2][2]))
    phi = (s1 ** 2 * s2 ** 2 - 4 * s2 ** 3 - 4 * s1 ** 3 * s3 + 18 * s1 * s2 * s3
           - 27 * s3 ** 2 + 4 * (s1 ** 2 - 3 * s2 + 4) ** 2)
    psi = (s1 ** 2 - 2 * s2) * (s2 ** 2 - 2 * s1 * s3) - s3 ** 2
    return phi, psi


def work(task):
    rep, which = task
    t0 = time.time()
    phi, psi = face_polys(rep)
    rng = random.Random(rep)
    for _ in range(2):
        t = [Fraction(rng.randint(0, 12), 12) for _ in range(NV)]
        want = lean_values(rep, t)
        if (eval_at(phi, t), eval_at(psi, t)) != want:
            return rep, which, "MISMATCH", 0, time.time() - t0
    method, pieces = certify(phi if which == "phi" else psi)
    return rep, which, method, pieces, time.time() - t0


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--jobs", type=int, default=4, help="worker processes (0: all CPUs)")
    ap.add_argument("--table", default=os.path.join(here, "face_orbits.tsv"),
                    help="compare the per-orbit methods with this table (if it exists)")
    ap.add_argument("--write-table", help="write the per-orbit table to this file")
    args = ap.parse_args()
    t0 = time.time()
    ok = check_symmetry()
    print(f"symmetry identities (S4 generators, complement): {'ok' if ok else 'FAILED'}")
    pats = maximal_patterns()
    _, phi_orbits = orbits(pats, (False, True))
    _, psi_orbits = orbits(pats, (False,))
    print(f"maximal patterns: {len(pats)}; orbits: {len(phi_orbits)} for Phi "
          f"(S4 x complement), {len(psi_orbits)} for Psi (S4)")
    tasks = [(r, "phi") for r in sorted(phi_orbits)] + [(r, "psi") for r in sorted(psi_orbits)]
    tasks.sort(key=lambda x: x[0].count("1"), reverse=True)  # rough load balance
    jobs = args.jobs or os.cpu_count() or 1
    if jobs > 1:
        with Pool(jobs) as pool:
            results = pool.map(work, tasks, chunksize=16)
    else:
        results = [work(t) for t in tasks]
    rows, summary = [], {}
    for rep, which, method, pieces, sec in results:
        size = (phi_orbits if which == "phi" else psi_orbits)[rep]
        rows.append(f"{which}\t{rep}\t{size}\t{method}\t{pieces}")
        key = (which, "box" if method == "box" else method[:4])
        summary[key] = summary.get(key, 0) + 1
        if method in ("FAIL", "MISMATCH"):
            ok = False
            print(f"  {which} {rep}: {method}")
    rows.sort()
    for which, orbs in (("phi", phi_orbits), ("psi", psi_orbits)):
        nbox = summary.get((which, "box"), 0)
        nk = summary.get((which, "kuhn"), 0)
        print(f"{which}: {len(orbs)} orbits ({sum(orbs.values())} patterns): "
              f"{nbox} by box Bernstein, {nk} by Kuhn simplices")
        if nbox + nk != len(orbs) or sum(orbs.values()) != len(pats):
            ok = False  # some orbit was not certified, or the orbits miss a pattern
    if args.write_table:
        with open(args.write_table, "w") as fh:
            fh.write("which\trepresentative\tpatterns\tmethod\tpieces\n")
            fh.write("\n".join(rows) + "\n")
    if os.path.exists(args.table):
        with open(args.table) as fh:
            old = [ln.rstrip("\n") for ln in fh][1:]
        same = old == rows
        ok = ok and same
        print(f"table {os.path.basename(args.table)}: {'matches' if same else 'DIFFERS'}")
    print(f"total {time.time() - t0:.1f} s with {jobs} process(es)")
    print("RESULT: FaceBound and SectorFaceBound certified" if ok else "RESULT: FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
