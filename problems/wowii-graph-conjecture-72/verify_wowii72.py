#!/usr/bin/env python3
"""Independent check of the counterexample to the formal statement of WOWII Conjecture 72.

The Lean proof in AgenticConjectures/WowiiGraphConjecture72.lean is the
certificate; this script recomputes every number it relies on with a separate
implementation (standard library only, exact rational arithmetic).

For a connected graph G, tree(G) is the order of a largest induced tree, A is
the average of the eccentricities ecc(v), and l(v) is the independence number of
the subgraph induced by the neighbours of v, with L = max l. Formal Conjectures
(commit c094b97) states

  ceil(A + L / 3) <= tree(G)    for every finite connected G on >= 2 vertices.

Default mode (CI) checks the 28-vertex graph in g28.txt:
  * it is the graph defined by levels in the Lean file;
  * it is connected and its eccentricities sum to 150, so A = 75/14;
  * L = 5, by exhaustive search inside every neighbourhood;
  * tree(G) = 7, by growing every induced tree one leaf at a time, and again by
    testing every vertex subset of order at most 8 (an induced tree on more
    than 8 vertices would contain one on exactly 8, by deleting leaves);
  * ceil(A + L/3) = 8 > 7, so the formal statement fails, while the evenly
    divided reading ceil((A + L)/3) = 4 <= 7 holds on this graph.
It also checks the invariants on paths, cycles, complete graphs and stars.

  python3 verify_wowii72.py
  geng -cq 8 | python3 verify_wowii72.py --graph6   # nauty input, local only
"""
import argparse
import itertools
import math
import sys
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent


def level(i):
    """The level of vertex i, as `lvl` in the Lean file."""
    if i == 0:
        return 1
    if i == 1:
        return 2
    if i <= 5:
        return 3
    if i == 6:
        return 4
    if i == 7:
        return 5
    return 0 if i <= 17 else 6


def level_graph():
    """Distinct vertices are adjacent when their levels differ by one or are both 0 or both 6."""
    n = 28
    adj = [0] * n
    for u in range(n):
        for v in range(n):
            lu, lv = level(u), level(v)
            if u != v and (abs(lu - lv) == 1 or lu == lv == 0 or lu == lv == 6):
                adj[u] |= 1 << v
    return n, adj


def read_edge_list(path):
    """Read `name`, then `n m`, then m lines `u v`; reject loops and repeated edges."""
    lines = [line.split() for line in path.read_text().splitlines() if line.strip()]
    n, m = map(int, lines[1])
    adj, seen = [0] * n, set()
    for u, v in (map(int, line) for line in lines[2:]):
        if u == v or (min(u, v), max(u, v)) in seen:
            raise ValueError(f"loop or repeated edge {u} {v}")
        seen.add((min(u, v), max(u, v)))
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    if len(seen) != m:
        raise ValueError(f"header says {m} edges, file has {len(seen)}")
    return n, adj


def bits(s):
    while s:
        low = s & -s
        yield low.bit_length() - 1
        s ^= low


def eccentricities(n, adj):
    """Breadth-first search from every vertex; None if the graph is disconnected."""
    ecc = []
    for s in range(n):
        dist, frontier, d = {s: 0}, [s], 0
        while frontier:
            d += 1
            nxt = []
            for x in frontier:
                for y in bits(adj[x]):
                    if y not in dist:
                        dist[y] = d
                        nxt.append(y)
            frontier = nxt
        if len(dist) < n:
            return None
        ecc.append(max(dist.values()))
    return ecc


def independent(adj, s):
    return all(not adj[v] & s for v in bits(s))


def local_independence(n, adj):
    """l(v): the largest independent subset of N(v), over all subsets of N(v)."""
    lam = []
    for v in range(n):
        best, sub = 0, adj[v]
        while True:
            if independent(adj, sub):
                best = max(best, bin(sub).count("1"))
            if sub == 0:
                break
            sub = (sub - 1) & adj[v]
        lam.append(best)
    return lam


def induced_trees(n, adj):
    """trees[k] is the set of k-vertex induced trees, as bitmasks.

    Deleting a leaf of an induced tree on k + 1 >= 2 vertices leaves an induced
    tree on k vertices, in which the leaf has exactly one neighbour; conversely,
    adding such a vertex to an induced tree gives an induced tree. So each size
    is obtained from the previous one, and the list stops at tree(G).
    """
    trees = [set(), {1 << v for v in range(n)}] if n else [set()]
    while trees[-1]:
        nxt = set()
        for t in trees[-1]:
            border = 0
            for v in bits(t):
                border |= adj[v]
            for v in bits(border & ~t):
                if bin(adj[v] & t).count("1") == 1:
                    nxt.add(t | 1 << v)
        trees.append(nxt)
    trees.pop()
    return trees


def induces_tree(adj, s, k):
    """Whether the k-vertex set s induces a tree: k - 1 edges and connected."""
    if sum(bin(adj[v] & s).count("1") for v in bits(s)) != 2 * (k - 1):
        return False
    seen = frontier = s & -s
    while frontier:
        v = (frontier & -frontier).bit_length() - 1
        frontier &= frontier - 1
        new = adj[v] & s & ~seen
        seen |= new
        frontier |= new
    return seen == s


def invariants(n, adj):
    """Return (A, L, tree, trees) for a connected graph, or None if disconnected."""
    ecc = eccentricities(n, adj)
    if ecc is None:
        return None
    trees = induced_trees(n, adj)
    return Fraction(sum(ecc), n), max(local_independence(n, adj)), len(trees) - 1, trees


def sanity(failures):
    """tree(P_n) = n, tree(C_n) = n - 1, tree(K_n) = 2, tree(K_1,m) = m + 1 = l(centre) + 1."""
    for n in range(2, 9):
        path = [(1 << (v - 1) if v else 0) | (1 << (v + 1) if v < n - 1 else 0)
                for v in range(n)]
        cycle = [(1 << ((v - 1) % n)) | (1 << ((v + 1) % n)) for v in range(n)]
        complete = [((1 << n) - 1) ^ (1 << v) for v in range(n)]
        star = [((1 << n) - 2)] + [1] * (n - 1)
        expected = [("P", path, n), ("K", complete, 2), ("K_1,", star, n)]
        if n >= 3:
            expected.append(("C", cycle, n - 1))
        for name, adj, tree in expected:
            got = invariants(n, adj)[2]
            if got != tree:
                failures.append(f"tree({name}{n}) = {got}, expected {tree}")
        if local_independence(n, star)[0] != n - 1:
            failures.append(f"l(centre of K_1,{n - 1}) is wrong")
    print("sanity: tree(P_n) = n, tree(C_n) = n - 1, tree(K_n) = 2 and "
          "tree(K_1,m) = m + 1 for n <= 8")


def check_counterexample(failures):
    n, adj = read_edge_list(HERE / "g28.txt")
    if (n, adj) != level_graph():
        failures.append("g28.txt is not the level graph of the Lean file")
    edges = sum(bin(a).count("1") for a in adj) // 2
    print(f"g28.txt: n = {n}, {edges} edges, equal to the level graph of the Lean file")

    ecc = eccentricities(n, adj)
    if ecc is None:
        failures.append("g28.txt is disconnected")
        return
    avg = Fraction(sum(ecc), n)
    print(f"connected; eccentricities by level 0..6: "
          f"{[sorted({ecc[v] for v in range(n) if level(v) == k}) for k in range(7)]}; "
          f"sum {sum(ecc)}, A = {avg}")
    if (sum(ecc), avg) != (150, Fraction(75, 14)):
        failures.append("unexpected eccentricities")

    lam = local_independence(n, adj)
    big_l = max(lam)
    print(f"L = max l(v) = {big_l}, attained at {[v for v in range(n) if lam[v] == big_l]}")
    if big_l != 5:
        failures.append("unexpected L")

    trees = induced_trees(n, adj)
    tree = len(trees) - 1
    print(f"induced trees by order 1..{tree}: {[len(t) for t in trees[1:]]}; tree(G) = {tree}")
    witness = sum(1 << v for v in (8, 0, 1, 2, 3, 4, 5))
    if tree != 7 or witness not in trees[7] or not induces_tree(adj, witness, 7):
        failures.append("unexpected tree(G)")

    for k in range(1, 9):
        count = sum(induces_tree(adj, sum(1 << v for v in c), k)
                    for c in itertools.combinations(range(n), k))
        expected = len(trees[k]) if k <= tree else 0
        print(f"brute force, all {math.comb(n, k)} subsets of order {k}: "
              f"{count} induce a tree ({'match' if count == expected else 'MISMATCH'})")
        if count != expected:
            failures.append(f"brute force disagrees at order {k}")

    formal = math.ceil(avg + Fraction(big_l, 3))
    even = math.ceil((avg + big_l) / 3)
    print(f"formal statement: ceil(A + L/3) = ceil({avg + Fraction(big_l, 3)}) = {formal} "
          f"<= tree(G) = {tree} is {formal <= tree}")
    print(f"evenly divided reading: ceil((A + L)/3) = ceil({(avg + big_l) / 3}) = {even} "
          f"<= {tree} is {even <= tree}")
    if (formal, even) != (8, 4) or formal <= tree:
        failures.append("the counterexample does not behave as documented")


def parse_graph6(line):
    data = [ord(c) - 63 for c in line]
    if data[0] > 62:
        raise ValueError("graph6 with n > 62 is not supported")
    n, bitlist = data[0], []
    for x in data[1:]:
        bitlist.extend((x >> k) & 1 for k in range(5, -1, -1))
    adj, k = [0] * n, 0
    for j in range(1, n):
        for i in range(j):
            if bitlist[k]:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            k += 1
    return n, adj


def check_graph6(failures):
    graphs = tight = 0
    min_gap = None
    for line in sys.stdin:
        line = line.strip()
        if not line or line.startswith(">"):
            continue
        n, adj = parse_graph6(line)
        result = invariants(n, adj) if n >= 2 else None
        if result is None:
            failures.append(f"{line}: not a connected graph on >= 2 vertices")
            continue
        avg, big_l, tree, _ = result
        graphs += 1
        gap = tree - (avg + Fraction(big_l, 3))
        min_gap = gap if min_gap is None else min(min_gap, gap)
        tight += math.ceil(avg + Fraction(big_l, 3)) == tree
        if math.ceil(avg + Fraction(big_l, 3)) > tree:
            failures.append(f"formal statement fails on {line}")
        if math.ceil((avg + big_l) / 3) > tree:
            failures.append(f"evenly divided reading fails on {line}")
    print(f"graphs checked: {graphs}; ceil(A + L/3) = tree(G) on {tight}; "
          f"minimum of tree(G) - (A + L/3): {min_gap}")
    if graphs == 0:
        failures.append("no graphs read")


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--graph6", action="store_true",
                    help="read connected graphs in graph6 format from stdin instead")
    args = ap.parse_args()
    failures = []
    if args.graph6:
        check_graph6(failures)
    else:
        sanity(failures)
        check_counterexample(failures)
    for failure in failures[:10]:
        print("FAIL:", failure)
    print("OK" if not failures else "FAILED")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
