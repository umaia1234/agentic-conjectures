#!/usr/bin/env python3
"""Independent numerical check of counterexamples to WOWII Conjecture 300.

WOWII Conjecture 300 (Graffiti.pc, Mar. 1, 2007): if G is a simple connected graph with
n(G) > 2, then

    gamma_t(G) <= (1/2) * [n(G) + frequency of lambda_min(complement of G)],

where gamma_t is the total domination number, lambda(v) is the independence number of the
subgraph induced by the neighbours of v, lambda_min is its minimum over the vertices, and the
frequency is the number of vertices at which lambda attains lambda_min. Everything here is
computed from these definitions by exhaustive search, with no theory about the graphs:

* gamma_t: the least k such that some k-subset D has a neighbour of every vertex. Supersets of
  total dominating sets are total dominating, so gamma_t = k exactly when some k-subset works
  and no (k-1)-subset does; both facts are checked by enumerating subsets.
* lambda(v) in the complement Gc: the largest independent set of Gc inside N_Gc(v), found by
  enumerating all independent sets of Gc[N_Gc(v)] (method A); and again as the largest clique
  of G avoiding the closed neighbourhood N_G[v] (method B). The two must agree.

Default mode: build G_t, the 2-corona of K4 with t pendant vertices at one vertex, for
t = 0..4 (n = 12, 15, 18, 21, 24), check that the graph6 string of G_1 is exactly the
15-vertex graph of the Lean proof, and check 2*gamma_t - (n + f) = t. For comparison it also
evaluates the reading without the complement, under which G_t gives equality. Then check the
ten counterexamples on 12 vertices (the first is graph12 of the Lean proof) and the six on 13
vertices that violate the bound by 1, as listed by closure_wowii300.sh.

--graph6: read graph6 lines on stdin (for example from geng -c) and check every connected graph
with n > 2; print one summary line per order and exit with status 1 if some graph violates the
bound. A violation needs 2*gamma_t >= n + 2, since the frequency is at least 1, so lambda is
computed only for the graphs with 2*gamma_t >= n.
"""

import itertools
import sys
from collections import Counter, defaultdict, deque

G15_GRAPH6 = "N~aA@?OA?G?O?O?G?A?"
G15_EDGES = [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 6), (2, 3), (2, 7),
             (3, 8), (4, 9), (5, 10), (6, 11), (7, 12), (8, 13), (9, 14)]

G12_EDGES = [(4, 5), (1, 6), (2, 7), (6, 8), (7, 9), (8, 9), (3, 10), (4, 10), (5, 10), (0, 11),
             (3, 11), (8, 11), (9, 11)]
# All counterexamples on 12 vertices (gamma_t = 7, frequency 1), and the counterexamples on 13
# vertices with gamma_t = 8 and frequency 1, which violate the bound by 1.
SMALLEST_12 = ["K??I@?A?WwQE", "K?G?K?@OGkBE", "K?Ca??CEOFOL", "K?D@?o@_?H_V", "K?O_?ODC_co[",
               "KA?_GAAAOQa[", "K?EA?o@GGH_V", "KAG?OGD__BaR", "KAGC?GD?Wc`R", "KAG?GM?CGP_^"]
UNIT_13 = ["L?_?I?_?O@aoEE", "L?EA@??@?p?U?\\", "LC@@??C?gQ@HC[", "L?EA@?W?GG_R?V",
           "L?`@?_PA?G_R?Z", "L?`@?_PA?G_R?^"]


def family(t):
    """G_t: K4 on hubs 0..3, pendant hubs 4..3+t at hub 0, then a path hub - middle - leaf at
    every hub h, with middle h + k and leaf h + 2k, where k = 4 + t."""
    k = 4 + t
    edges = [(a, b) for a in range(4) for b in range(a + 1, 4)]
    edges += [(0, 4 + i) for i in range(t)]
    edges += [(h, h + k) for h in range(k)] + [(h + k, h + 2 * k) for h in range(k)]
    return 3 * k, edges


def masks(n, edges):
    adj = [0] * n
    for a, b in edges:
        assert a != b and 0 <= a < n and 0 <= b < n
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    return adj


def decode_graph6(s):
    s = s.strip()
    n = ord(s[0]) - 63
    assert 0 <= n <= 62, "only graphs with at most 62 vertices"
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits.extend((v >> (5 - i)) & 1 for i in range(6))
    edges, k = [], 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                edges.append((i, j))
            k += 1
    return n, edges


def encode_graph6(n, adj):
    bits = [adj[i] >> j & 1 for j in range(1, n) for i in range(j)]
    bits += [0] * (-len(bits) % 6)
    return chr(63 + n) + "".join(
        chr(63 + sum(b << (5 - i) for i, b in enumerate(bits[k:k + 6])))
        for k in range(0, len(bits), 6))


def connected(n, adj):
    seen, todo = 1, deque([0])
    while todo:
        v = todo.popleft()
        new = adj[v] & ~seen
        seen |= new
        todo.extend(u for u in range(n) if new >> u & 1)
    return seen == (1 << n) - 1


def is_total_dominating(adj, d):
    return all(a & d for a in adj)


def exists_tds_of_size(n, adj, k):
    for c in itertools.combinations(range(n), k):
        d = 0
        for v in c:
            d |= 1 << v
        if is_total_dominating(adj, d):
            return d
    return None


def gamma_t(n, adj):
    """Total domination number by subset search; None if some vertex is isolated."""
    if any(a == 0 for a in adj):
        return None
    k = 1
    while exists_tds_of_size(n, adj, k) is None:
        k += 1
    return k


def gamma_t_check(n, adj, k):
    """Check gamma_t = k by two subset searches (monotonicity: no (k-1)-set suffices)."""
    return exists_tds_of_size(n, adj, k) is not None and exists_tds_of_size(n, adj, k - 1) is None


def max_indep(adj, cand):
    """Largest independent set inside the vertex mask cand, by enumerating independent sets."""
    if cand == 0:
        return 0
    v = (cand & -cand).bit_length() - 1
    rest = cand & ~(1 << v)
    return max(max_indep(adj, rest), 1 + max_indep(adj, rest & ~adj[v]))


def max_clique(adj, cand):
    """Largest clique inside the vertex mask cand, by enumerating cliques."""
    if cand == 0:
        return 0
    v = (cand & -cand).bit_length() - 1
    rest = cand & ~(1 << v)
    return max(max_clique(adj, rest), 1 + max_clique(adj, rest & adj[v]))


def local_independence(n, adj):
    """lambda(v) = alpha(H[N_H(v)]) for every vertex v of the graph H given by adj."""
    return [max_indep(adj, adj[v]) for v in range(n)]


def complement(n, adj):
    full = (1 << n) - 1
    return [full & ~adj[v] & ~(1 << v) for v in range(n)]


def lambda_complement(n, adj):
    """lambda in the complement, by methods A and B, which must agree."""
    a = local_independence(n, complement(n, adj))
    full = (1 << n) - 1
    b = [max_clique(adj, full & ~(adj[v] | 1 << v)) for v in range(n)]
    assert a == b, (a, b)
    return a


def frequency_of_min(values):
    m = min(values)
    return m, sum(1 for x in values if x == m)


def check_family(t):
    n, edges = family(t)
    adj = masks(n, edges)
    k = 4 + t
    assert connected(n, adj)
    g = gamma_t(n, adj) if n <= 15 else None
    assert gamma_t_check(n, adj, 2 * k)
    if g is not None:
        assert g == 2 * k
    lam = lambda_complement(n, adj)
    expected = [2] * 4 + [3] * t + [3] * 4 + [4] * t + [4] * k
    assert lam == expected, (lam, expected)
    m, f = frequency_of_min(lam)
    assert (m, f) == (2, 4)
    gap = 2 * (2 * k) - (n + f)
    assert gap == t
    # The reading without the complement: lambda in G itself.
    lam_g = local_independence(n, adj)
    m_g, f_g = frequency_of_min(lam_g)
    assert (m_g, f_g) == (1, k) and 2 * (2 * k) == n + f_g
    print(f"t={t}: n={n}, edges={len(edges)}, gamma_t={2 * k}, lambda in complement: "
          f"hubs {lam[:k]}, middles {lam[k:2 * k]}, leaves {lam[2 * k:]}; "
          f"min={m}, frequency={f}, bound=({n}+{f})/2={(n + f) / 2}, "
          f"2*gamma_t-(n+f)={gap}; without complement: min={m_g}, frequency={f_g}, equality")
    return gap


def check_small(g6, n_expected, gamma_expected):
    n, edges = decode_graph6(g6)
    adj = masks(n, edges)
    assert n == n_expected and connected(n, adj)
    g = gamma_t(n, adj)
    lam = lambda_complement(n, adj)
    m, f = frequency_of_min(lam)
    assert g == gamma_expected and f == 1 and 2 * g > n + f, (g6, g, m, f)
    return g, m, f, lam


def main_default():
    n, edges = decode_graph6(G15_GRAPH6)
    assert n == 15 and sorted(edges) == sorted(G15_EDGES) == sorted(family(1)[1]), \
        "graph6 string does not match the 15-vertex graph"
    adj = masks(n, edges)
    assert encode_graph6(n, adj) == G15_GRAPH6
    assert gamma_t(n, adj) == 10
    print(f"graph6 {G15_GRAPH6}: n=15, 17 edges, matches the Lean edge list and G_1; "
          f"gamma_t=10 by full subset search")
    for t in range(5):
        check_family(t)
    n, edges = decode_graph6(SMALLEST_12[0])
    assert sorted(edges) == sorted(G12_EDGES), "graph6 string does not match graph12"
    for g6 in SMALLEST_12:
        g, m, f, lam = check_small(g6, 12, 7)
        print(f"{g6}: n=12, gamma_t={g}, lambda in complement {lam}, min={m}, frequency={f}, "
              f"bound={(12 + f) / 2}")
    for g6 in UNIT_13:
        g, m, f, lam = check_small(g6, 13, 8)
        print(f"{g6}: n=13, gamma_t={g}, min={m}, frequency={f}, bound={(13 + f) / 2}")
    print("OK: G_t violates the bound by t/2 for t = 1..4 (equality at t = 0); the ten graphs on "
          "12 vertices violate it by 1/2 and the six on 13 vertices by 1")


def histogram(h):
    return "{" + ", ".join(f"{k}: {v}" for k, v in sorted(h.items())) + "}"


def main_graph6():
    """Check every connected graph with n > 2. The frequency f is at least 1, so a violation
    (2*gamma_t > n + f) needs 2*gamma_t >= n + 2; lambda is computed only when 2*gamma_t >= n,
    and the slack n + f - 2*gamma_t is reported for those graphs. The summary lines have the
    same format as those of sweep_wowii300.c. Exit status 1 if a graph violates the bound."""
    skipped, count, violations = 0, Counter(), Counter()
    gamma_hist, near, slack_hist = defaultdict(Counter), Counter(), defaultdict(Counter)
    for line in sys.stdin:
        line = line.strip()
        if not line or line.startswith(">"):
            continue
        n, edges = decode_graph6(line)
        adj = masks(n, edges)
        if n <= 2 or not connected(n, adj):
            skipped += 1
            continue
        count[n] += 1
        g = gamma_t(n, adj)
        gamma_hist[n][g] += 1
        if 2 * g < n:
            continue
        _, f = frequency_of_min(lambda_complement(n, adj))
        near[n] += 1
        slack = n + f - 2 * g
        slack_hist[n][slack] += 1
        if slack < 0:
            violations[n] += 1
            print(f"VIOLATION {line} n={n} gamma_t={g} frequency={f}")
        elif slack == 0:
            print(f"EQUALITY {line} n={n} gamma_t={g} frequency={f}")
    for n in sorted(count):
        print(f"n={n}: {count[n]} connected graphs; gamma_t histogram {histogram(gamma_hist[n])}; "
              f"2*gamma_t >= n on {near[n]}, slack histogram {histogram(slack_hist[n])}; "
              f"violations {violations[n]}")
    print(f"skipped {skipped} graphs with n <= 2 or disconnected")
    ok = sum(count.values()) > 0 and sum(violations.values()) == 0
    print("OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    if sys.argv[1:] == ["--graph6"]:
        sys.exit(main_graph6())
    elif sys.argv[1:]:
        sys.exit("usage: check_wowii300.py [--graph6]")
    else:
        main_default()
