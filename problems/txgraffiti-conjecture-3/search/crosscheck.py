"""Cross-check the exact solvers in tx3lib on random regular graphs: i(G) by pysat, CP-SAT and
maximal-independent-set enumeration; mu*(G) by pysat, CP-SAT and (small graphs) brute force.
Also checks the returned witnesses.  Usage: python3 crosscheck.py TRIALS"""
import random
import sys
import time

import networkx as nx

from tx3lib import i_brute, i_cp, i_sat, mustar_brute, mustar_cp, mustar_sat

random.seed(1)
cnt = viol = 0
t0 = time.time()
for trial in range(int(sys.argv[1])):
    r = random.choice([3, 4, 5, 6])
    n = random.choice([x for x in range(r + 1, 15) if (x * r) % 2 == 0])
    G = nx.random_regular_graph(r, n, seed=random.randrange(10**9))
    a, D = i_sat(G)
    b, c = i_cp(G), i_brute(G)
    m1, M = mustar_sat(G)
    m2 = mustar_cp(G)
    assert a == b == c, (a, b, c, nx.to_graph6_bytes(G))
    assert m1 == m2, (m1, m2)
    if G.number_of_edges() <= 30 and trial % 5 == 0:
        m3 = mustar_brute(G)
        assert m3 == m1, (m1, m3)
    Ds = set(D)
    assert all(not (u in Ds and v in Ds) for u, v in G.edges())
    assert all(v in Ds or any(u in Ds for u in G[v]) for v in G)
    cov = [x for e in M for x in e]
    assert len(cov) == len(set(cov))
    assert all(u in cov or v in cov for u, v in G.edges())
    if a > m1:
        viol += 1
        print("VIOLATION", r, n, a, m1, nx.to_graph6_bytes(G, header=False))
    cnt += 1
print("checked", cnt, "graphs; violations", viol, f"{time.time() - t0:.1f}s")
