#!/usr/bin/env python3
"""Numeric sanity check for WOWII Conjecture 96 and its per-root form.

The Lean proof in AgenticConjectures/WowiiGraphConjecture96.lean is the
certificate; this script only re-checks the inequalities on small graphs with
an independent, brute-force implementation (standard library only).

For a connected graph G, alpha is the independence number, E(v) the number of
vertices at even distance from v (v included) and l(v) the independence number
of the subgraph induced by the neighbourhood of v. With L = max l, it checks

  conjecture 96:  alpha <= 1 + min_v E(v) * (L - 1)            (n >= 2)
  per-root form:  alpha <= max(1, l(v)) + sum_{u != v, d(v,u) even} max(1, l(u) - 1)
                  for every root v

Default mode (CI): every labelled graph on n <= 6 vertices; the number of
connected ones is compared with OEIS A001187. Also checks that every star
K_{1,m}, m = 1..12, attains equality and that the one-vertex graph violates the
literal row (the reason upstream adds `Nontrivial`).

  python3 verify_wowii96.py
  geng -cq 9 | python3 verify_wowii96.py --graph6     # nauty input, local only
"""
import argparse
import itertools
import sys

# OEIS A001187: connected labelled graphs on n nodes, n = 0..6.
A001187 = [1, 1, 1, 4, 38, 728, 26704]


def invariants(n, adj):
    """Return (alpha, l, E) for the graph with adjacency bitmasks `adj`."""
    indep = [True] * (1 << n)
    for s in range(1, 1 << n):
        v = (s & -s).bit_length() - 1
        indep[s] = indep[s & (s - 1)] and not (adj[v] & s)
    alpha = max(bin(s).count("1") for s in range(1 << n) if indep[s])
    lam = []
    for v in range(n):
        best, sub = 0, adj[v]
        while True:  # all subsets of N(v)
            if indep[sub]:
                best = max(best, bin(sub).count("1"))
            if sub == 0:
                break
            sub = (sub - 1) & adj[v]
        lam.append(best)
    even = []
    for v in range(n):
        dist = [-1] * n
        dist[v] = 0
        queue = [v]
        for x in queue:
            for y in range(n):
                if adj[x] >> y & 1 and dist[y] < 0:
                    dist[y] = dist[x] + 1
                    queue.append(y)
        even.append([u for u in range(n) if dist[u] >= 0 and dist[u] % 2 == 0])
    return alpha, lam, even


def connected(n, adj):
    seen, stack = 1, [0]
    while stack:
        x = stack.pop()
        new = adj[x] & ~seen
        seen |= new
        stack.extend(y for y in range(n) if new >> y & 1)
    return seen == (1 << n) - 1


class Stats:
    def __init__(self):
        self.graphs = self.roots = 0
        self.tight = self.tight_root = 0
        self.min_slack = None
        self.failures = []

    def check(self, n, adj, label):
        alpha, lam, even = invariants(n, adj)
        big_l = max(lam)
        min_e = min(len(e) for e in even)
        rhs = 1 + min_e * (big_l - 1)
        self.graphs += 1
        slack = rhs - alpha
        self.min_slack = slack if self.min_slack is None else min(self.min_slack, slack)
        self.tight += slack == 0
        if slack < 0:
            self.failures.append(f"conjecture 96 fails on {label}")
        for v in range(n):
            bound = max(1, lam[v]) + sum(max(1, lam[u] - 1) for u in even[v] if u != v)
            self.roots += 1
            self.tight_root += alpha == bound
            if alpha > bound:
                self.failures.append(f"per-root form fails on {label}, root {v}")
        return alpha, min_e, big_l


def labelled(stats, nmax):
    ok = True
    for n in range(2, nmax + 1):
        pairs = list(itertools.combinations(range(n), 2))
        count = 0
        for mask in range(1 << len(pairs)):
            adj = [0] * n
            for k, (i, j) in enumerate(pairs):
                if mask >> k & 1:
                    adj[i] |= 1 << j
                    adj[j] |= 1 << i
            if connected(n, adj):
                count += 1
                stats.check(n, adj, f"n={n} edge mask {mask}")
        match = count == A001187[n]
        ok &= match
        print(f"n={n}: {count} connected labelled graphs "
              f"(A001187: {A001187[n]}, {'match' if match else 'MISMATCH'})")
    return ok


def parse_graph6(line):
    data = [ord(c) - 63 for c in line]
    if data[0] > 62:
        raise ValueError("graph6 with n > 62 is not supported")
    n, bits = data[0], []
    for x in data[1:]:
        bits.extend((x >> k) & 1 for k in range(5, -1, -1))
    adj, k = [0] * n, 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            k += 1
    return n, adj


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--graph6", action="store_true",
                    help="read connected graphs in graph6 format from stdin")
    ap.add_argument("--nmax", type=int, default=6,
                    help="largest order of the labelled enumeration (default 6)")
    args = ap.parse_args()
    stats, ok = Stats(), True

    if args.graph6:
        for line in sys.stdin:
            line = line.strip()
            if not line or line.startswith(">"):
                continue
            n, adj = parse_graph6(line)
            if n < 2 or not connected(n, adj):
                print(f"skipping {line}: not a connected graph on >= 2 vertices")
                ok = False
                continue
            stats.check(n, adj, line)
    else:
        ok &= labelled(stats, args.nmax)
        for m in range(1, 13):  # star K_{1,m}: vertex 0 is the centre
            adj = [((1 << (m + 1)) - 2)] + [1] * m
            alpha, min_e, big_l = stats.check(m + 1, adj, f"K_1,{m}")
            if (alpha, min_e, big_l) != (m, 1, m):
                stats.failures.append(f"unexpected invariants on K_1,{m}")
        print("stars K_1,m (m = 1..12): alpha = m = 1 + 1 * (m - 1), equality")
        # K_1: alpha = 1, E = 1, max l = 0, so the literal row reads 1 <= 0.
        alpha, lam, even = invariants(1, [0])
        literal_rhs = 1 + len(even[0]) * (max(lam) - 1)
        if (alpha, lam, len(even[0]), literal_rhs) != (1, [0], 1, 0):
            stats.failures.append("K_1 does not behave as documented")
        print(f"K_1: alpha = {alpha}, min E = {len(even[0])}, max l = {max(lam)}; "
              f"literal row {alpha} <= {literal_rhs} is false")

    print(f"graphs checked: {stats.graphs}; conjecture 96 tight on {stats.tight}; "
          f"minimum slack {stats.min_slack}")
    print(f"(graph, root) pairs checked: {stats.roots}; per-root form tight on "
          f"{stats.tight_root}")
    for failure in stats.failures[:10]:
        print("FAIL:", failure)
    ok &= not stats.failures and stats.graphs > 0
    print("OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
