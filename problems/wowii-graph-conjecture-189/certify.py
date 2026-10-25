#!/usr/bin/env python3
"""Hamiltonian-path certificates for WOWII Conjecture 189 when sigma(G) <= 4.

A certificate file lists, for every order n in its range, each connected graph G on n vertices
(up to isomorphism, one graph6 string per class) with

    max_v distEven(v) <= 1 + sigma(G)

in its class, together with a Hamiltonian path of G.  sigma3_certificates.txt covers
sigma(G) <= 3 and n = 2..16; sigma4_certificates.txt (option --sigma4) covers sigma(G) = 4 and
n = 2..15.  distEven(v) counts the vertices at even distance from v, v included; sigma(G) is the
second entry of the nondecreasing degree sequence.  Lines are

    # n=<n> count=<c>                       one header per order, before its graphs
    <graph6> <v_0>,<v_1>,...,<v_{n-1}>      vertices numbered as in the graph6 string

Default mode re-verifies a certificate file from the graph6 strings alone: every graph is
connected, satisfies the hypothesis, lies in the class, and the vertex list is a Hamiltonian
path; the graph6 strings are distinct; each order has its announced number of graphs, and the
counts agree with EXPECTED (EXPECTED4 for --sigma4) below.  It does not (and cannot) show that
the list is complete; completeness rests on the pruned geng searches in reproduce.sh.

`--make` reads graph6 lines on stdin, keeps the hypothesis graphs in the class, finds a
Hamiltonian path for each and prints certificate lines (without headers).  It exits with
status 1 if some kept graph has no Hamiltonian path, which would be a counterexample.

usage: certify.py [--sigma4] FILE  |  certify.py [--sigma4] --make

Standard library only.
"""
import sys
from collections import deque

# number of hypothesis graphs with sigma(G) <= 3, up to isomorphism, for n = 2..16
EXPECTED = {2: 1, 3: 2, 4: 5, 5: 14, 6: 42, 7: 168, 8: 293, 9: 100, 10: 29,
            11: 0, 12: 0, 13: 0, 14: 0, 15: 0, 16: 0}
# number of hypothesis graphs with sigma(G) = 4, up to isomorphism, for n = 2..15
EXPECTED4 = {2: 0, 3: 0, 4: 0, 5: 1, 6: 8, 7: 67, 8: 1018, 9: 17012, 10: 33433,
             11: 7186, 12: 2044, 13: 285, 14: 0, 15: 0}


def in_class(sigma, four):
    return sigma == 4 if four else sigma <= 3


def parse_graph6(s):
    """Adjacency sets of a graph6 string with at most 62 vertices."""
    data = [ord(c) - 63 for c in s]
    if not data or any(not 0 <= x <= 63 for x in data) or data[0] == 63:
        raise ValueError(f"unsupported graph6 string {s!r}")
    n, body = data[0], data[1:]
    need = n * (n - 1) // 2
    if len(body) != (need + 5) // 6:
        raise ValueError(f"wrong length for graph6 string {s!r}")
    bits = [(x >> k) & 1 for x in body for k in range(5, -1, -1)]
    if any(bits[need:]):
        raise ValueError(f"nonzero padding in graph6 string {s!r}")
    adj = [set() for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i].add(j)
                adj[j].add(i)
            k += 1
    return adj


def bfs(adj, s):
    dist = [-1] * len(adj)
    dist[s] = 0
    queue = deque([s])
    while queue:
        u = queue.popleft()
        for w in adj[u]:
            if dist[w] < 0:
                dist[w] = dist[u] + 1
                queue.append(w)
    return dist


def invariants(adj):
    """(connected with n > 1, sigma, max distEven); the last two are None if not."""
    n = len(adj)
    if n < 2:
        return False, None, None
    dists = [bfs(adj, v) for v in range(n)]
    if min(dists[0]) < 0:
        return False, None, None
    sigma = sorted(len(a) for a in adj)[1]
    max_even = max(sum(1 for d in row if d % 2 == 0) for row in dists)
    return True, sigma, max_even


def is_ham_path(adj, path):
    n = len(adj)
    return (sorted(path) == list(range(n))
            and all(path[i + 1] in adj[path[i]] for i in range(n - 1)))


def find_ham_path(adj):
    """Depth-first search from every start vertex; None if there is no Hamiltonian path."""
    n = len(adj)
    path, used = [], [False] * n

    def extend(v):
        path.append(v)
        used[v] = True
        if len(path) == n:
            return True
        for w in sorted(adj[v], key=lambda u: len(adj[u])):
            if not used[w] and extend(w):
                return True
        path.pop()
        used[v] = False
        return False

    for s in sorted(range(n), key=lambda u: len(adj[u])):
        if extend(s):
            return path
    return None


def make(four):
    bad = 0
    for line in sys.stdin:
        g6 = line.strip()
        if not g6 or g6.startswith(">"):
            continue
        adj = parse_graph6(g6)
        conn, sigma, max_even = invariants(adj)
        if not conn or not in_class(sigma, four) or max_even > 1 + sigma:
            continue
        path = find_ham_path(adj)
        if path is None:
            print(f"NO-HAMILTONIAN-PATH {g6}", file=sys.stderr)
            bad += 1
            continue
        print(g6, ",".join(map(str, path)))
    return 1 if bad else 0


def verify(filename, four):
    expected = EXPECTED4 if four else EXPECTED
    label = "sigma = 4" if four else "sigma <= 3"
    counts, announced, seen = {}, {}, set()
    current = None
    with open(filename) as f:
        for lineno, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            if line.startswith("#"):
                fields = dict(t.split("=") for t in line[1:].split() if "=" in t)
                if "n" in fields:
                    current = int(fields["n"])
                    if current in announced:
                        raise SystemExit(f"line {lineno}: second header for n={current}")
                    announced[current] = int(fields["count"])
                    counts[current] = 0
                continue
            g6, path_text = line.split()
            adj = parse_graph6(g6)
            path = [int(t) for t in path_text.split(",")]
            conn, sigma, max_even = invariants(adj)
            if current is None or len(adj) != current:
                raise SystemExit(f"line {lineno}: graph order does not match its header")
            if not conn or not in_class(sigma, four) or max_even > 1 + sigma:
                raise SystemExit(f"line {lineno}: {g6} is not a hypothesis graph with {label}")
            if not is_ham_path(adj, path):
                raise SystemExit(f"line {lineno}: invalid Hamiltonian path for {g6}")
            if g6 in seen:
                raise SystemExit(f"line {lineno}: duplicate graph {g6}")
            seen.add(g6)
            counts[current] += 1
    if sorted(announced) != sorted(expected):
        raise SystemExit(f"headers cover n={sorted(announced)}, expected {sorted(expected)}")
    for n in sorted(expected):
        if counts[n] != announced[n] or counts[n] != expected[n]:
            raise SystemExit(f"n={n}: {counts[n]} graphs, header {announced[n]}, "
                             f"expected {expected[n]}")
    total = sum(counts.values())
    print(f"OK: {total} hypothesis graphs with {label} on {min(expected)}..{max(expected)} "
          f"vertices, each with a verified Hamiltonian path; per order: "
          + " ".join(f"{n}:{counts[n]}" for n in sorted(counts)))
    return 0


if __name__ == "__main__":
    args = sys.argv[1:]
    four = args[:1] == ["--sigma4"]
    if four:
        args = args[1:]
    if args == ["--make"]:
        sys.exit(make(four))
    if len(args) == 1:
        sys.exit(verify(args[0], four))
    sys.exit(__doc__)
