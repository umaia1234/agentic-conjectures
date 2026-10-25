#!/usr/bin/env python3
"""Validate srg_sym_encode.py on parameter sets with known answers.

Part A (no SAT solver needed, CI-feasible with --semantic-only): for known
graphs, the intended assignment of every CNF variable (edge orbits from the
graph, AND gates, counter prefix sums) satisfies every clause.  This is the
soundness direction used by UNSAT claims: a real srg invariant under the group
always yields a model.

Part B (needs `cadical` on PATH): exhaustive cycle-type sweeps.  For Paley(9),
Petersen, Paley(13), Clebsch and the two srg(16,6,2,2) graphs (the complete
lists of srgs with these parameters; a classical fact, not re-checked here),
and for every cycle type of S_n, the encoding with one canonical permutation
of that type must be SAT iff a listed graph has an automorphism of that cycle
type (automorphism groups computed here by backtracking).  Rooted frames:
srg(9,4,1,2) SAT; srg(19,6,1,2) and srg(33,8,1,2) UNSAT (no such graphs:
irrational eigenvalues, resp. non-integral multiplicities); srg(243,22,1,2)
(Berlekamp-van Lint-Seidel) SAT under an order-110 group fixing the root.
Every SAT model is decoded and checked as a graph.

Usage: python3 validate_encoder.py [--semantic-only]
"""
import itertools
import os
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from srg_sym_encode import (check_graph, dimacs_bytes, encode,  # noqa: E402
                            extend_root_perm, perm_from_cycles, rooted_frame)


# ---------------------------------------------------------------- graphs ---

def paley9():
    return [[int(x != y and ((x // 3 == y // 3) != (x % 3 == y % 3)))
             for y in range(9)] for x in range(9)]


def petersen():
    S = list(itertools.combinations(range(5), 2))
    return [[int(not set(a) & set(b)) for b in S] for a in S]


def paley13():
    qr = {(i * i) % 13 for i in range(1, 13)}
    return [[int((x - y) % 13 in qr) for y in range(13)] for x in range(13)]


def clebsch():
    conn = {1, 2, 4, 8, 15}
    return [[int((x ^ y) in conn) for y in range(16)] for x in range(16)]


def rook44():
    return [[int(x != y and (x // 4 == y // 4 or x % 4 == y % 4))
             for y in range(16)] for x in range(16)]


def shrikhande():
    conn = {(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)}
    V = [(a, b) for a in range(4) for b in range(4)]
    return [[int(((p[0] - q[0]) % 4, (p[1] - q[1]) % 4) in conn) for q in V]
            for p in V]


def _polymod3(a, g):
    a = a[:]
    while len(a) >= len(g):
        c = a[-1] % 3
        if c:
            sh = len(a) - len(g)
            for i, gc in enumerate(g):
                a[sh + i] = (a[sh + i] - c * gc) % 3
        a.pop()
    return tuple(x % 3 for x in a) + (0,) * (len(g) - 1 - len(a))


def bvls():
    """srg(243,22,1,2): Cayley graph on F_3[x]/(g), g the ternary Golay
    generator x^5+x^4-x^3+x^2-1, connection set {+-x^i mod g}.
    Returns (adjacency, vertex list, h) with h[i] = x^i mod g."""
    g = [2, 0, 1, 2, 1, 1]
    h = [_polymod3([0] * i + [1], g) for i in range(11)]
    neg = lambda p: tuple((-c) % 3 for c in p)
    S = set(h) | {neg(p) for p in h}
    V = list(itertools.product(range(3), repeat=5))
    idx = {p: i for i, p in enumerate(V)}
    A = [[0] * 243 for _ in range(243)]
    for p in V:
        for s in S:
            A[idx[p]][idx[tuple((a + b) % 3 for a, b in zip(p, s))]] = 1
    return A, V, h, g


def params(A):
    n = len(A)
    k = sum(A[0])
    lam = mu = None
    for x in range(n):
        assert sum(A[x]) == k
        for y in range(x + 1, n):
            c = sum(A[x][z] & A[y][z] for z in range(n))
            if A[x][y]:
                assert lam in (None, c)
                lam = c
            else:
                assert mu in (None, c)
                mu = c
    return n, k, lam, mu


def automorphisms(A):
    n = len(A)
    res, img, used = [], [-1] * n, [False] * n

    def rec(i):
        if i == n:
            res.append(tuple(img))
            return
        for c in range(n):
            if not used[c] and all(A[i][j] == A[c][img[j]] for j in range(i)):
                img[i], used[c] = c, True
                rec(i + 1)
                used[c] = False
    rec(0)
    return res


def cycle_type(p):
    seen, t = set(), []
    for x in range(len(p)):
        if x not in seen:
            n, y = 0, x
            while y not in seen:
                seen.add(y)
                y = p[y]
                n += 1
            t.append(n)
    return tuple(sorted(t, reverse=True))


def partitions(n, maxp=None):
    maxp = maxp or n
    if n == 0:
        yield ()
        return
    for p in range(min(n, maxp), 0, -1):
        for rest in partitions(n - p, p):
            yield (p,) + rest


def canon_perm(n, part):
    cycles, s = [], 0
    for ln in part:
        cycles.append(list(range(s, s + ln)))
        s += ln
    return perm_from_cycles(n, cycles)


# ------------------------------------------------------ semantic checks ---

def intended_ok(v, k, lam, mu, gens, forced, A):
    """Evaluate every clause under the intended assignment derived from A.

    Edge-orbit variables are read off A.  Every auxiliary variable is
    functionally defined by clauses emitted before or together with its
    first use (AND triples, then counter rows in order), so one forward pass
    that fixes a variable whenever a clause has exactly one unassigned
    literal and all others false computes the intended assignment; a second
    pass checks that every clause is satisfied.
    """
    nvars, clauses, info = encode(v, k, lam, mu, gens, forced)
    val = [None] * (nvars + 1)
    for (x, y), r in info["orbit"].items():
        var = info["ovar"][r]
        if val[var] is None:
            val[var] = bool(A[x][y])
        elif val[var] != bool(A[x][y]):
            return "graph not invariant"
    for c in clauses:
        free = [l for l in c if val[abs(l)] is None]
        if len(free) == 1 and not any(val[abs(l)] == (l > 0) for l in c
                                      if val[abs(l)] is not None):
            val[abs(free[0])] = free[0] > 0
    if any(x is None for x in val[1:]):
        return "some auxiliary variable is undetermined"
    for c in clauses:
        if not any(val[abs(l)] == (l > 0) for l in c):
            return "clause %s violated" % (c,)
    return None


def relabel_rooted(A, root, k):
    """Map a graph with lambda=1, mu=2 to the canonical rooted frame.

    Returns (B, phi) where phi[old] = new and B is the relabelled adjacency.
    Gamma_1 is listed pair by pair in increasing order of the smaller vertex.
    """
    n = len(A)
    nb = [y for y in range(n) if A[root][y]]
    pairs, done = [], set()
    for a in nb:
        if a in done:
            continue
        b = [c for c in nb if A[a][c]][0]
        pairs.append((a, b))
        done.update((a, b))
    phi = {root: 0}
    for i, (a, b) in enumerate(pairs):
        phi[a], phi[b] = 2 * i + 1, 2 * i + 2
    v, partner, labels, _ = rooted_frame(k)
    inv = {phi[a]: a for a in nb}
    for i, (p, q) in enumerate(labels):
        a, b = inv[p], inv[q]
        w = [z for z in range(n) if z != root and A[a][z] and A[b][z]]
        assert len(w) == 1
        phi[w[0]] = k + 1 + i
    B = [[0] * n for _ in range(n)]
    for x in range(n):
        for y in range(n):
            B[phi[x]][phi[y]] = A[x][y]
    return B, phi


def solve(nvars, clauses):
    with tempfile.NamedTemporaryFile("wb", suffix=".cnf", delete=False) as f:
        f.write(dimacs_bytes(nvars, clauses))
        name = f.name
    try:
        r = subprocess.run(["cadical", "-q", name], capture_output=True, text=True)
    finally:
        os.unlink(name)
    true = set()
    for line in r.stdout.splitlines():
        if line.startswith("v "):
            true.update(int(t) for t in line.split()[1:] if int(t) > 0)
    return r.returncode, true


def model_graph(v, info, true):
    A = [[0] * v for _ in range(v)]
    for (x, y), r in info["orbit"].items():
        if info["ovar"][r] in true:
            A[x][y] = A[y][x] = 1
    return A


def bvls_rooted_group():
    """BvLS relabelled to the rooted frame at 0, plus 3 automorphisms fixing 0.

    Gamma_1(0) is ordered h_0, -h_0, h_1, -h_1, ... (h_i and -h_i are
    adjacent since h_i - (-h_i) = -h_i).  The automorphisms p -> x*p,
    p -> p^3 (Frobenius of F_3[x]/(g) = F_243) and p -> -p fix 0 and generate
    a group of order 110.  Returns (B, [cycles of sigma on 1..22]).
    """
    A, V, h, g = bvls()
    idx = {p: i for i, p in enumerate(V)}
    neg = lambda p: tuple((-c) % 3 for c in p)
    root = idx[(0,) * 5]
    gamma1 = []
    for i in range(11):
        gamma1 += [idx[h[i]], idx[neg(h[i])]]
    phi = {root: 0}
    for j, x in enumerate(gamma1):
        phi[x] = j + 1
    _, _, labels, _ = rooted_frame(22)
    for i, (p, q) in enumerate(labels):
        a, b = gamma1[p - 1], gamma1[q - 1]
        w = [z for z in range(243) if z != root and A[a][z] and A[b][z]]
        assert len(w) == 1
        phi[w[0]] = 23 + i
    B = [[0] * 243 for _ in range(243)]
    for x in range(243):
        for y in range(243):
            B[phi[x]][phi[y]] = A[x][y]

    def mulx(p):
        return _polymod3([0] + list(p), g)

    def frob(p):
        r = [0] * 13
        for i, c in enumerate(p):
            r[3 * i] = c
        return _polymod3(r, g)
    out = []
    for f in (mulx, frob, neg):
        full = [None] * 243
        for x in range(243):
            full[phi[x]] = phi[idx[f(V[x])]]
        sig = {a: full[a] for a in range(1, 23)}
        cycles, seen = [], set()
        for a in range(1, 23):
            if a not in seen and sig[a] != a:
                cyc, b = [], a
                while b not in seen:
                    seen.add(b)
                    cyc.append(b)
                    b = sig[b]
                cycles.append(cyc)
        assert extend_root_perm(22, cycles) == full, "frame extension mismatch"
        out.append(cycles)
    return B, out


def main():
    semantic_only = "--semantic-only" in sys.argv
    t0 = time.time()
    bad = 0
    # ---- Part A: intended assignments satisfy every clause
    v9, _, _, forced9 = rooted_frame(4)
    P9, _ = relabel_rooted(paley9(), 0, 4)
    for cyc in ([], [[1, 2]], [[1, 2], [3, 4]], [[1, 3], [2, 4]], [[1, 3, 2, 4]]):
        g = extend_root_perm(4, cyc)
        aut = all(P9[x][y] == P9[g[x]][g[y]] for x in range(9) for y in range(9))
        if aut:
            msg = intended_ok(9, 4, 1, 2, [g], forced9, P9)
            print("A paley9 rooted sigma=%s: %s" % (cyc, msg or "ok"))
            bad += msg is not None
    B, gens = bvls_rooted_group()
    _, _, _, forced243 = rooted_frame(22)
    perms = [extend_root_perm(22, c) for c in gens]
    for g in perms:
        assert all(B[x][y] == B[g[x]][g[y]] for x in range(243) for y in range(243))
    msg = intended_ok(243, 22, 1, 2, perms, forced243, B)
    print("A bvls srg(243,22,1,2) rooted, group of order 110: %s" % (msg or "ok"))
    bad += msg is not None
    for name, A in (("petersen", petersen()), ("clebsch", clebsch()),
                    ("shrikhande", shrikhande())):
        n, k, lam, mu = params(A)
        for p in automorphisms(A)[:40]:
            msg = intended_ok(n, k, lam, mu, [list(p)], {}, A)
            bad += msg is not None
            if msg:
                print("A %s automorphism %s: %s" % (name, p, msg))
        print("A %s srg%s: 40 automorphism groups ok" % (name, (n, k, lam, mu)))
    print("Part A done (%.1fs)" % (time.time() - t0), flush=True)
    if semantic_only:
        print("VALIDATION %s" % ("OK" if not bad else "FAILED"))
        return 1 if bad else 0
    # ---- Part B: SAT/UNSAT sweeps
    fams = [("paley9", [paley9()]), ("petersen", [petersen()]),
            ("paley13", [paley13()]), ("clebsch", [clebsch()]),
            ("srg(16,6,2,2)", [rook44(), shrikhande()])]
    for name, graphs in fams:
        types, prm = set(), None
        for A in graphs:
            p = params(A)
            assert prm in (None, p)
            prm = p
            types |= {cycle_type(a) for a in automorphisms(A)}
        n, k, lam, mu = prm
        cnt = [0, 0]
        for part in partitions(n):
            g = canon_perm(n, part)
            nvars, clauses, info = encode(n, k, lam, mu, [g])
            rc, true = solve(nvars, clauses)
            want = 10 if part in types else 20
            cnt[rc == 10] += 1
            if rc == 10 and check_graph(n, k, lam, mu, model_graph(n, info, true), [g]):
                bad += 1
                print("B %s %s: model is not a valid graph" % (name, part))
            if rc != want:
                bad += 1
                print("B MISMATCH %s cycle type %s: got %s want %s" % (name, part, rc, want))
        print("B %s srg%s: %d cycle types, %d SAT, %d UNSAT, all as expected"
              % (name, prm, cnt[0] + cnt[1], cnt[1], cnt[0]) if not bad else
              "B %s: see mismatches" % name, flush=True)
    for k, want in ((4, 10), (6, 20), (8, 20)):
        v, _, _, forced = rooted_frame(k)
        nvars, clauses, info = encode(v, k, 1, 2, [], forced)
        rc, true = solve(nvars, clauses)
        ok = rc == want and (rc == 20 or not check_graph(
            v, k, 1, 2, model_graph(v, info, true), []))
        bad += not ok
        print("B rooted srg(%d,%d,1,2), trivial group: %s (%s)" % (
            v, k, {10: "SAT", 20: "UNSAT"}.get(rc, rc), "expected" if ok else "WRONG"))
    nvars, clauses, info = encode(243, 22, 1, 2, perms, forced243)
    rc, true = solve(nvars, clauses)
    ok = rc == 10 and not check_graph(243, 22, 1, 2, model_graph(243, info, true), perms)
    bad += not ok
    print("B rooted srg(243,22,1,2), order-110 group: %s, model %s" % (
        {10: "SAT", 20: "UNSAT"}.get(rc, rc), "is a valid invariant srg" if ok else "INVALID"))
    print("VALIDATION %s (%.1fs)" % ("OK" if not bad else "FAILED", time.time() - t0))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
