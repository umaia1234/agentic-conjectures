#!/usr/bin/env python3
"""Certificate for the OEIS A286185 / A286183 (and A286182) result.

For the three standard 2n-vertex "width-two cyclic strip" graphs

    prism      CL_n = C_n [] K_2            OEIS A286182
    Moebius    ML_n (2n-cycle + n diameters) OEIS A286185
    antiprism  AP_n                          OEIS A286183

let a(n) be the number of connected induced (non-null) subgraphs.  PROOF.md
proves the closed forms that OEIS still labels "conjectured":

    prism      a(n) = A002203(n) + 3n*A000129(n) - 3n + 1     [= Vince 2021, Lemma 7.2]
    Moebius    a(n) = A002203(n) + 3n*A000129(n) - n - 1
    antiprism  a(n) = A005248(n) - 2n + 2n*A001906(n)

together with the order-6 linear recurrences and generating functions conjectured
on the same entries (which follow from the closed forms).

This script re-checks, with exact integer arithmetic and no network access:

  0. a *generic* frontier / boundary-partition DP for counting connected induced
     subgraphs of an arbitrary graph, cross-validated against naive brute force
     on random graphs (it knows nothing about ladders or Pell/Fibonacci numbers);
  1. exhaustive enumeration of all 2^(2n) vertex subsets of each graph, compared
     to the OEIS data terms;
  2. the generic DP against method 1, and against the OEIS terms, then run far
     past the range method 1 can reach;
  3. the closed forms against methods 1 and 2;
  4. every counting lemma of PROOF.md -- the transfer-matrix identities and the
     two structural pieces f(m) and g(n) -- against direct enumeration;
  5. the conjectured recurrences and generating functions, derived from the
     closed forms.

Exit status 0 iff every check passes.  Pure standard library; runs in well under
a minute.  Run from this directory:

    python3 certificate.py                # all checks (CI budget, ~25 s)
    python3 certificate.py --full         # heavier exhaustive range (~5 min)
    python3 certificate.py --print-edges  # edge lists, to diff against
                                          # lean_graph_check.lean
"""

import itertools
import random
import sys
import time

# ---------------------------------------------------------------------------
# OEIS DATA terms, offset 1, transcribed from the entries (checked 2026-08-12).
# ---------------------------------------------------------------------------
OEIS = {
    "prism": [
        3, 13, 51, 167, 503, 1441, 4007, 10923, 29355, 78037, 205659, 538127,
        1399583, 3621289, 9327695, 23931603, 61186131, 155949085, 396369795,
        1004904695, 2541896519, 6416348209, 16165610999, 40657256571,
        102090514683, 255968753125, 640899345579, 1602640560479,
    ],
    "moebius": [
        3, 15, 55, 173, 511, 1451, 4019, 10937, 29371, 78055, 205679, 538149,
        1399607, 3621315, 9327723, 23931633, 61186163, 155949119, 396369831,
        1004904733, 2541896559, 6416348251, 16165611043, 40657256617,
        102090514731, 255968753175, 640899345631, 1602640560533,
    ],
    "antiprism": [
        3, 15, 60, 207, 663, 2038, 6107, 17983, 52272, 150407, 429223, 1216490,
        3427635, 9609327, 26821668, 74576703, 206650167, 570877918, 1572754187,
        4322192287, 11851474968, 32430381815, 88576465735, 241511251922,
        657457204323, 1787147867343, 4851349002252,
    ],
}

FAIL = []


def check(name, ok, detail=""):
    print(("PASS  " if ok else "FAIL  ") + name + (("  -- " + detail) if detail else ""))
    if not ok:
        FAIL.append(name)


# ---------------------------------------------------------------------------
# The three graphs.  Vertex (i, r) of a 2n-vertex strip gets index 2*i + r;
# row r = 0 is the "inner" cycle, r = 1 the "outer" one.
#
#   rungs      (i, 0) ~ (i, 1)                        all three families
#   rails      (i, r) ~ (i+1, r)                      prism, Moebius, antiprism
#   twist      (n-1, r) ~ (0, 1-r) instead of rails   Moebius only
#   diagonal   (i, 1) ~ (i+1, 0)                      antiprism only
#
# Every inter-column edge is guarded by i != j, which keeps the graph simple in
# the degenerate cases n = 1, 2 that OEIS includes: all three give K_2 at n = 1,
# and at n = 2 the prism gives C_4 while the Moebius ladder and the antiprism
# both give K_4.  That reproduces the OEIS terms 3, 13 and 3, 15 exactly.
# ---------------------------------------------------------------------------
def graph_edges(n, kind):
    e = set()

    def add(u, v):
        if u != v:
            e.add((min(u, v), max(u, v)))

    for i in range(n):
        add(2 * i, 2 * i + 1)                       # rung
        j = (i + 1) % n
        if j == i:                                  # degenerate n = 1: no rails
            continue
        if kind == "prism":
            add(2 * i, 2 * j)
            add(2 * i + 1, 2 * j + 1)
        elif kind == "moebius":
            if i == n - 1:                          # twisted seam
                add(2 * i, 2 * j + 1)
                add(2 * i + 1, 2 * j)
            else:
                add(2 * i, 2 * j)
                add(2 * i + 1, 2 * j + 1)
        elif kind == "antiprism":
            add(2 * i, 2 * j)
            add(2 * i + 1, 2 * j + 1)
            add(2 * i + 1, 2 * j)                   # diagonal
        else:
            raise ValueError(kind)
    return sorted(e)


def oeis_reference_edges(n, kind):
    """The graphs exactly as OEIS's own Mathematica programs build them
    (transcribed from the `%t` lines of the entries, preserved in upstream/).

      A286182  Table[{i <-> Mod[i,n]+1, n+i <-> Mod[i,n]+n+1, i <-> i+n}, {i,n}]
      A286183  Table[{i <-> Mod[i,n]+1, n+i <-> Mod[i,n]+n+1,
                      i <-> n+Mod[i,n]+1, i <-> n+Mod[i-1,n]+1}, {i,n}]
      A286185  CirculantGraph[2n, {1, n}]

    Vertices are Mathematica's 1..2n, shifted to 0..2n-1.  This is an
    *independent* construction from `graph_edges`, used only to confirm that the
    graphs counted here are the ones OEIS tabulates.  Note that A286183's
    diagonal is `inner_i ~ outer_{i+1}` while `graph_edges` uses the mirror
    image `outer_i ~ inner_{i+1}`; the two antiprisms are isomorphic (swap the
    two rows), so the counts agree, which is what this check verifies.
    """
    e = set()

    def add(u, v):
        u, v = u - 1, v - 1                    # 1-based -> 0-based
        if u != v:
            e.add((min(u, v), max(u, v)))

    if kind == "moebius":
        for i in range(1, 2 * n + 1):          # CirculantGraph[2n, {1, n}]
            for d in (1, n):
                add(i, (i - 1 + d) % (2 * n) + 1)
        return sorted(e)
    for i in range(1, n + 1):
        add(i, i % n + 1)                      # inner cycle
        add(n + i, i % n + n + 1)              # outer cycle
        if kind == "prism":
            add(i, i + n)                      # rung
        elif kind == "antiprism":
            add(i, n + i % n + 1)              # diagonal  inner_i ~ outer_{i+1}
            add(i, n + (i - 1) % n + 1)        # rung      inner_i ~ outer_i
        else:
            raise ValueError(kind)
    return sorted(e)


def adjacency_masks(nv, edges):
    adj = [0] * nv
    for u, v in edges:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    return adj


def _connected(s, adj):
    comp = s & -s
    frontier = comp
    while frontier:
        nxt = 0
        f = frontier
        while f:
            b = f & -f
            nxt |= adj[b.bit_length() - 1]
            f ^= b
        frontier = nxt & s & ~comp
        comp |= frontier
    return comp == s


# ---------------------------------------------------------------------------
# Method 1: exhaustive enumeration of all vertex subsets.
# ---------------------------------------------------------------------------
def count_exhaustive(nv, edges):
    adj = adjacency_masks(nv, edges)
    return sum(1 for s in range(1, 1 << nv) if _connected(s, adj))


# ---------------------------------------------------------------------------
# Method 2: generic frontier dynamic program.  Vertices are processed in index
# order; the state records how the still-open ("frontier") vertices split into
# components of the partial induced subgraph, plus how many components have
# already been closed off.  A run contributes iff it closes exactly one.
# Nothing here is specific to ladders.
# ---------------------------------------------------------------------------
def count_frontier_dp(nv, edges):
    nb = [[] for _ in range(nv)]
    for u, v in edges:
        nb[u].append(v)
        nb[v].append(u)
    last = [max(nb[u]) if nb[u] else -1 for u in range(nv)]

    def canon(labels):
        seen, out, nxt = {}, [], 0
        for x in labels:
            if x < 0:
                out.append(-1)
                continue
            if x not in seen:
                seen[x] = nxt
                nxt += 1
            out.append(seen[x])
        return tuple(out)

    frontier, states = [], {((), 0): 1}
    for v in range(nv):
        pos = {u: i for i, u in enumerate(frontier)}
        survivors = [u for u in frontier if last[u] > v]
        new_frontier = survivors + ([v] if last[v] > v else [])
        nxt_states = {}
        for (labels, closed), cnt in states.items():
            for selected in (False, True):
                lab = list(labels)
                if selected:
                    group = {lab[pos[u]] for u in nb[v] if u in pos and lab[pos[u]] >= 0}
                    vlab = min(group) if group else (max(lab, default=-1) + 1)
                    if group:
                        lab = [vlab if x in group else x for x in lab]
                else:
                    vlab = -1
                alive_labels = [lab[pos[u]] for u in survivors]
                if last[v] > v:
                    alive_labels.append(vlab)
                alive = {x for x in alive_labels if x >= 0}
                before = {x for x in lab if x >= 0} | ({vlab} if selected else set())
                nclosed = closed + len(before - alive)
                if nclosed > 1:            # two components can never merge later
                    continue
                key = (canon(alive_labels), nclosed)
                nxt_states[key] = nxt_states.get(key, 0) + cnt
        states, frontier = nxt_states, new_frontier
    return sum(c for (labels, closed), c in states.items() if closed == 1 and not labels)


# ---------------------------------------------------------------------------
# Integer sequences and the closed forms.
# ---------------------------------------------------------------------------
def tables(n):
    P, Q, F, L = [0, 1], [2, 2], [0, 1], [2, 1]        # A000129, A002203, Fib, Lucas
    while len(P) <= n + 3:
        P.append(2 * P[-1] + P[-2])
        Q.append(2 * Q[-1] + Q[-2])
    while len(F) <= 2 * n + 3:
        F.append(F[-1] + F[-2])
        L.append(L[-1] + L[-2])
    t = [q // 2 for q in Q]                            # A001333 = A002203 / 2
    return P, Q, F, L, t


def closed_form(kind, n, P, Q, F, L):
    if kind == "prism":
        return Q[n] + 3 * n * P[n] - 3 * n + 1
    if kind == "moebius":
        return Q[n] + 3 * n * P[n] - n - 1
    return L[2 * n] - 2 * n + 2 * n * F[2 * n]         # antiprism, A005248/A001906


# ---------------------------------------------------------------------------
# PROOF.md internals.
#   Column states A = {0}, B = {1}, C = {0,1}; two occupied columns are LINKED
#   iff some edge of the graph joins them.  Transfer matrices, order (A, B, C):
#     prism / Moebius rails :  M  = [[1,0,1],[0,1,1],[1,1,1]]   (only {A,B} unlinked)
#     Moebius twisted seam  :  M . Psigma                       (Psigma swaps A, B)
#     antiprism             :  Ma = [[1,1,1],[0,1,1],[1,1,1]]   (only (B,A) unlinked)
# ---------------------------------------------------------------------------
M = [[1, 0, 1], [0, 1, 1], [1, 1, 1]]
MA = [[1, 1, 1], [0, 1, 1], [1, 1, 1]]
PSIGMA = [[0, 1, 0], [1, 0, 0], [0, 0, 1]]


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


def matpow(A, e):
    R = [[1 if i == j else 0 for j in range(3)] for i in range(3)]
    for _ in range(e):
        R = matmul(R, A)
    return R


def trace(A):
    return sum(A[i][i] for i in range(3))


def count_all_columns_occupied(n, kind, cyclic=True):
    """Enumerate the 3^n ways to occupy every column and test connectivity.
    With cyclic=False the last column's outgoing edges are dropped, giving the
    linear-strip quantity f(n) of PROOF.md."""
    edges = graph_edges(n, kind)
    if not cyclic:                    # delete the edges of the seam column pair
        edges = [(u, v) for (u, v) in edges
                 if not (u // 2 == 0 and v // 2 == n - 1) or u // 2 == v // 2]
    adj = adjacency_masks(2 * n, edges)
    total = 0
    for cols in itertools.product((0b01, 0b10, 0b11), repeat=n):
        s = 0
        for i, c in enumerate(cols):
            s |= c << (2 * i)
        if _connected(s, adj):
            total += 1
    return total


# ---------------------------------------------------------------------------
def main():
    if "--print-edges" in sys.argv:
        for n in range(1, 7):
            print(f"n={n}")
            for kind in ("prism", "moebius", "antiprism"):
                print(f"  {kind:9s} {graph_edges(n, kind)}")
        return 0

    t0 = time.time()
    # --full raises the exhaustive bound; the default keeps CI comfortably
    # inside scripts/verify_all.py's 180 s per-command timeout.
    N_EXH, N_DP = (13 if '--full' in sys.argv else 10), 200
    P, Q, F, L, t = tables(N_DP)

    # --- 0. the generic DP, validated against naive brute force
    random.seed(20260812)
    bad = 0
    for _ in range(200):
        nv = random.randint(1, 8)
        p = random.choice([0.2, 0.4, 0.7])
        edges = [(u, v) for u in range(nv) for v in range(u + 1, nv) if random.random() < p]
        if count_frontier_dp(nv, edges) != count_exhaustive(nv, edges):
            bad += 1
    check("generic frontier DP == brute force on 200 random graphs", bad == 0,
          f"{bad} mismatches")

    for kind in ("moebius", "antiprism", "prism"):
        print(f"\n--- {kind}")
        # --- 0b. our graph counts the same thing as OEIS's own generator program
        N_REF = 9
        check(f"[{kind}] counts agree with OEIS's own %t construction, n = 1..{N_REF}",
              all(count_exhaustive(2 * n, graph_edges(n, kind))
                  == count_exhaustive(2 * n, oeis_reference_edges(n, kind))
                  for n in range(1, N_REF + 1)))

        # --- 1. exhaustive enumeration vs the OEIS terms
        exh = {n: count_exhaustive(2 * n, graph_edges(n, kind)) for n in range(1, N_EXH + 1)}
        check(f"[{kind}] exhaustive enumeration == OEIS terms, n = 1..{N_EXH}",
              all(exh[n] == OEIS[kind][n - 1] for n in exh),
              ", ".join(str(exh[n]) for n in range(1, 7)) + ", ...")

        # --- 2. independent DP vs method 1 and vs the OEIS terms
        dp = {n: count_frontier_dp(2 * n, graph_edges(n, kind)) for n in range(1, N_DP + 1)}
        check(f"[{kind}] frontier DP == exhaustive enumeration, n = 1..{N_EXH}",
              all(dp[n] == exh[n] for n in exh))
        check(f"[{kind}] frontier DP == OEIS data terms, n = 1..{len(OEIS[kind])}",
              all(dp[n] == OEIS[kind][n - 1] for n in range(1, len(OEIS[kind]) + 1)))

        # --- 3. the closed form against both independent counts
        check(f"[{kind}] closed form == frontier DP, n = 1..{N_DP}",
              all(closed_form(kind, n, P, Q, F, L) == dp[n] for n in range(1, N_DP + 1)),
              f"a({N_DP}) has {len(str(dp[N_DP]))} digits")

        # --- 4. PROOF.md structural decomposition a(n) = n*(sum f) + g(n)
        G_MAX = 11
        g_enum = {n: count_all_columns_occupied(n, kind) for n in range(3, G_MAX + 1)}
        if kind == "antiprism":
            g_cf = lambda n: L[2 * n] + n * F[2 * n - 2]
            arc_cf = lambda n: n * (F[2 * n + 1] - 2)
            f_cf = lambda m: F[2 * m + 2]
        elif kind == "moebius":
            g_cf = lambda n: (Q[n] - 1) + n * (t[n - 1] + 1)
            arc_cf = lambda n: n * (P[n + 1] - 2)
            f_cf = lambda m: 2 * P[m] + t[m]
        else:
            g_cf = lambda n: (Q[n] + 1) + n * (t[n - 1] - 1)
            arc_cf = lambda n: n * (P[n + 1] - 2)
            f_cf = lambda m: 2 * P[m] + t[m]
        check(f"[{kind}] Step 3: g(n) closed form == direct enumeration, n = 3..{G_MAX}",
              all(g_enum[n] == g_cf(n) for n in g_enum),
              ", ".join(str(g_enum[n]) for n in range(3, min(8, G_MAX + 1))))
        check(f"[{kind}] Step 2: a(n) - g(n) == n * sum_{{m<n}} f(m), n = 3..{G_MAX}",
              all(dp[n] - g_enum[n] == arc_cf(n) == n * sum(f_cf(m) for m in range(1, n))
                  for n in g_enum))
        check(f"[{kind}] Step 4: n*(sum f) + g(n) == closed form, n = 1..{N_DP}",
              all(arc_cf(n) + g_cf(n) == closed_form(kind, n, P, Q, F, L)
                  for n in range(1, N_DP + 1)))

        # --- 5. the transfer-matrix identities of PROOF.md Steps 1 and 3
        K = 30
        if kind == "antiprism":
            check("[antiprism] Step 1: 1^T Ma^(m-1) 1 == A001906(m+1), m = 1..%d" % K,
                  all(sum(map(sum, matpow(MA, m - 1))) == F[2 * m + 2] for m in range(1, K)))
            check("[antiprism] Step 3: tr(Ma^n) == A005248(n), n = 1..%d" % K,
                  all(trace(matpow(MA, n)) == L[2 * n] for n in range(1, K)))
            check("[antiprism] Step 3: (Ma^(n-1))_{A,B} == Fibonacci(2n-2), n = 1..%d" % K,
                  all(matpow(MA, n - 1)[0][1] == F[2 * n - 2] for n in range(1, K)))
        else:
            check(f"[{kind}] Step 1: 1^T M^(m-1) 1 == 2*A000129(m) + A001333(m), m = 1..{K}",
                  all(sum(map(sum, matpow(M, m - 1))) == 2 * P[m] + t[m] for m in range(1, K)))
            if kind == "prism":
                check("[prism] Step 3: tr(M^n) == A002203(n) + 1, n = 1..%d" % K,
                      all(trace(matpow(M, n)) == Q[n] + 1 for n in range(1, K)))
                check("[prism] Step 3: (M^(n-1))_{A,B} == (A001333(n-1) - 1)/2, n = 1..%d" % K,
                      all(matpow(M, n - 1)[0][1] == (t[n - 1] - 1) // 2 for n in range(1, K)))
            else:
                check("[moebius] Step 3: tr(M^n . Psigma) == A002203(n) - 1, n = 1..%d" % K,
                      all(trace(matmul(matpow(M, n), PSIGMA)) == Q[n] - 1 for n in range(1, K)))
                check("[moebius] Step 3: (M^(n-1))_{A,A} == (A001333(n-1) + 1)/2, n = 1..%d" % K,
                      all(matpow(M, n - 1)[0][0] == (t[n - 1] + 1) // 2 for n in range(1, K)))

        # --- 6. the conjectured recurrence follows from the closed form
        sig = ([6, -11, 4, 5, -2, -1] if kind != "antiprism"
               else [8, -24, 34, -24, 8, -1])
        a = [None] + [closed_form(kind, n, P, Q, F, L) for n in range(1, N_DP + 1)]
        check(f"[{kind}] recurrence with signature {tuple(sig)}, n = 7..{N_DP}",
              all(a[n] == sum(sig[k] * a[n - 1 - k] for k in range(6))
                  for n in range(7, N_DP + 1)))

        # --- 7. the conjectured generating function follows from the closed form
        quad = [1, -2, -1] if kind != "antiprism" else [1, -3, 1]
        den = [1]
        for factor in ([1, -1], [1, -1], quad, quad):
            out = [0] * (len(den) + len(factor) - 1)
            for i, x in enumerate(den):
                for j, y in enumerate(factor):
                    out[i + j] += x * y
            den = out
        deg = 60
        num = [sum(den[j] * a[k - j] for j in range(len(den)) if 1 <= k - j <= N_DP)
               for k in range(deg + 1)]
        expected = {
            "prism": [0, 3, -5, 6, -8, -5, -3],
            "moebius": [0, 3, -3, -2, -4, 3, -1],
            "antiprism": [0, 3, -9, 12, -15, 9, -2],
        }[kind]
        check(f"[{kind}] g.f. numerator over (1-x)^2 * quadratic^2 == OEIS numerator",
              num[:7] == expected and all(c == 0 for c in num[7:]),
              f"numerator {num[:7]}")

    print(f"\n{'ALL CHECKS PASSED' if not FAIL else 'FAILURES: ' + '; '.join(FAIL)}"
          f"   ({time.time() - t0:.1f}s)")
    return 1 if FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
