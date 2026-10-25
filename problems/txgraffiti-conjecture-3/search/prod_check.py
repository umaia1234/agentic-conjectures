"""Cartesian products G x K_t of graph6 graphs (t = 2: cubic -> 4-regular; t = 3: cubic ->
5-regular).  First asks pysat for an independent dominating set of size <= ceil(m/(2r-1)), a lower
bound for mu*; only if there is none does it compute mu* exactly (descending pysat queries) and
ask for one of size <= mu*.  Usage: python3 prod_check.py 2,3 FILE.g6 ..."""
import sys
import time

import networkx as nx

from tx3lib import ids_exists, load_g6, mustar_sat

for path in sys.argv[2:]:
    G = load_g6(path)
    for t in map(int, sys.argv[1].split(",")):
        P = nx.convert_node_labels_to_integers(nx.cartesian_product(G, nx.complete_graph(t)))
        degs = sorted({d for _, d in P.degree()})
        lb = -(-P.number_of_edges() // (2 * max(degs) - 1))
        t0 = time.time()
        if ids_exists(P, lb) is not None:
            verdict = f"i<=ceil(m/(2r-1))={lb}<=mu*"
        else:
            mu, _ = mustar_sat(P)
            D = ids_exists(P, mu)
            verdict = f"mu*={mu} " + ("i<=mu*" if D is not None else "NO IDS OF SIZE <= mu* (candidate)")
        print(f"{path.split('/')[-1]} x K{t}: n={P.number_of_nodes()} deg={degs} {verdict} "
              f"secs={time.time() - t0:.1f}", flush=True)
