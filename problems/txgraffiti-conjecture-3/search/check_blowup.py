"""i and mu* of the cubic counterexamples G48 and G50 and of their blow-ups G[K_2-bar] (6-regular):
pysat decision queries around the expected values, then CP-SAT optimisation for t = 2.
G48 is read from a graph6 file (`python3 ../certificates/g48_cnf.py --g6 > g48.g6`); G50 is built
from the 15-variable, 20-clause formula of Afrasyab (arXiv:2609.10783, Section 2): vertices 2j, 2j+1
are the literals of variable j + 1 (edge between them), vertex 29 + a is clause a, adjacent to its
three literals.  Usage: python3 check_blowup.py g48.g6"""
import sys
import time

import networkx as nx

from tx3lib import blowup, i_cp, ids_exists, load_g6, mm_exists, mustar_cp

C = [(1, 9, -11), (-4, -10, -13), (1, -9, -14), (2, 6, 14), (-5, -6, 15), (2, -3, 15),
     (3, 5, -9), (-6, -12, -15), (-1, 5, -11), (4, -7, -15), (-2, 8, -12), (3, 9, 11),
     (-4, -8, 10), (7, -8, 13), (4, 7, -13), (-2, -7, 14), (-3, 11, -14), (8, 10, 12),
     (-10, 12, 13), (-1, -5, 6)]


def lit(l):
    return 2 * (abs(l) - 1) + (1 if l > 0 else 0)


G50 = nx.Graph()
G50.add_nodes_from(range(50))
for j in range(15):
    G50.add_edge(2 * j, 2 * j + 1)
for a, cl in enumerate(C, start=1):
    for l in cl:
        G50.add_edge(29 + a, lit(l))
G48 = load_g6(sys.argv[1])
for name, G in [("G48", G48), ("G50", G50)]:
    for t in [1, 2]:
        H = blowup(G, t)
        degs = sorted(set(d for _, d in H.degree()))
        t0 = time.time()
        k = 16 * t
        D_hi, D_lo = ids_exists(H, k), ids_exists(H, k - 1)
        ti = time.time() - t0
        M = mm_exists(H, 15 * t)
        print(f"{name}[K{t}]: n={H.number_of_nodes()} m={H.number_of_edges()} deg={degs} "
              f"conn={nx.is_connected(H)} IDS<={k}: {D_hi is not None}  IDS<={k - 1}: "
              f"{D_lo is not None} ({ti:.1f}s)  MM<={15 * t}: {M is not None}", flush=True)
        if t == 2:
            t0 = time.time()
            print("   CP-SAT i =", i_cp(H, workers=4, limit=600), f"({time.time() - t0:.1f}s)")
            t0 = time.time()
            print("   CP-SAT mu* =", mustar_cp(H, workers=4, limit=600),
                  f"({time.time() - t0:.1f}s)", flush=True)
