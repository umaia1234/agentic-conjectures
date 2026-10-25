"""Compare the output of `tx3check -v` (lines "i mu* graph6") with the pysat solvers in tx3lib.
Usage: python3 xcheck_c.py FILE"""
import sys

import networkx as nx

from tx3lib import i_sat, mustar_sat

bad = cnt = 0
for line in open(sys.argv[1]):
    if line.startswith("SUMMARY"):
        continue
    i, mu, g6 = line.split()
    G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(g6.encode()))
    a, _ = i_sat(G)
    b, _ = mustar_sat(G)
    if (a, b) != (int(i), int(mu)):
        bad += 1
        print("MISMATCH", g6, i, mu, a, b)
    cnt += 1
print("compared", cnt, "graphs; mismatches", bad)
sys.exit(1 if bad else 0)
