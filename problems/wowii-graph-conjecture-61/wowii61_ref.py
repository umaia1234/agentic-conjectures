#!/usr/bin/env python3
"""Independent reference implementation for WOWII Graph Conjecture 61.

Computes, for connected graphs G, the quantities of

    f(G) >= r(G) + ceil(D(G)/3)

with code that shares nothing with wowii61.cpp:

* f (largest induced forest): exhaustive search over vertex subsets in
  decreasing size, acyclicity tested with a union-find over the induced
  edges;
* alpha (independence number): exhaustive search over vertex subsets;
* D (diameter): breadth-first search from every vertex;
* r (Havel--Hakimi residue): a literal transcription of `havelHakimiStep`
  and `residueAux` from FormalConjecturesForMathlib (`List.splitAt`,
  truncated natural-number subtraction, descending re-sort).

With --nx (needs networkx, local use only) every graph is additionally
parsed by networkx and connectivity, diameter, independence number (maximum
clique of the complement) and the acyclicity of the forest witness are
recomputed with networkx and compared.

Modes (the summary format is the one of wowii61.cpp, so outputs can be
compared with `diff` after dropping the CROSSCHECK line):

  geng -cq N | python3 wowii61_ref.py [--nx]          summary of graph6 input
  python3 wowii61_ref.py --labeled N                  all labeled graphs on N
  python3 wowii61_ref.py --check-dump FILE [--nx]     recompute the lines
                                                      "g6 n m D f alpha r"
                                                      written by wowii61 --dump
Standard library only unless --nx is given.
"""

import sys
from itertools import combinations

CHECK_NAMES = ["conj", "thm1", "thm2a", "thm2b", "fms", "hh", "tree_f",
               "xf", "xa", "xd", "xr"]


# ------------------------------------------------------------------ graph6
def parse_graph6(line):
    """Return (n, adjacency sets) of a graph6 string (n <= 62)."""
    data = [ord(c) - 63 for c in line]
    if not data or not 0 <= data[0] <= 62 or any(not 0 <= x < 64 for x in data):
        raise ValueError("bad graph6 string: %r" % line)
    n = data[0]
    bits = []
    for x in data[1:]:
        bits.extend((x >> (5 - i)) & 1 for i in range(6))
    adj = [set() for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i].add(j)
                adj[j].add(i)
            k += 1
    return n, adj


def to_graph6(n, adj):
    bits = [1 if j in adj[i] else 0 for j in range(1, n) for i in range(j)]
    while len(bits) % 6:
        bits.append(0)
    out = [chr(63 + n)]
    for p in range(0, len(bits), 6):
        v = 0
        for b in bits[p:p + 6]:
            v = 2 * v + b
        out.append(chr(63 + v))
    return "".join(out)


# ---------------------------------------------------------------- invariants
def eccentricities(n, adj):
    """BFS from every vertex; None if the graph is disconnected."""
    ecc = []
    for s in range(n):
        dist = {s: 0}
        queue = [s]
        for u in queue:
            for w in adj[u]:
                if w not in dist:
                    dist[w] = dist[u] + 1
                    queue.append(w)
        if len(dist) < n:
            return None
        ecc.append(max(dist.values()))
    return ecc


def is_forest(vertices, adj):
    """Union-find over the edges induced by `vertices`."""
    parent = {v: v for v in vertices}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for u in vertices:
        for w in adj[u]:
            if w in parent and u < w:
                ru, rw = find(u), find(w)
                if ru == rw:
                    return False
                parent[ru] = rw
    return True


def largest_induced_forest(n, adj):
    """Return (f, witness): exhaustive search, largest subsets first."""
    for k in range(n, 0, -1):
        for sub in combinations(range(n), k):
            if is_forest(sub, adj):
                return k, sub
    return 0, ()


def independence_number(n, adj):
    for k in range(n, 0, -1):
        for sub in combinations(range(n), k):
            s = set(sub)
            if all(not (adj[v] & s) for v in sub):
                return k
    return 0


def havel_hakimi_step(s):
    """Literal transcription of `SimpleGraph.havelHakimiStep`."""
    if not s:
        return [], False
    d, rest = s[0], s[1:]
    to_decrement, remaining = rest[:d], rest[d:]      # List.splitAt d
    anomaly = d > len(rest) or 0 in to_decrement
    decremented = [max(x - 1, 0) for x in to_decrement]  # ℕ subtraction
    return sorted(decremented + remaining, reverse=True), anomaly


def residue(degrees):
    """`residueAux` applied to the descending degree sequence."""
    s = sorted(degrees, reverse=True)
    anomaly = False
    while True:
        if not s:
            return 0, anomaly
        if s[0] == 0:
            return 1 + len(s[1:]), anomaly
        s, a = havel_hakimi_step(s)
        anomaly = anomaly or a


def invariants(n, adj):
    """Return None for disconnected graphs, else a dict of invariants."""
    ecc = eccentricities(n, adj)
    if ecc is None:
        return None
    f, witness = largest_induced_forest(n, adj)
    r, anomaly = residue([len(adj[v]) for v in range(n)])
    return {
        "m": sum(len(a) for a in adj) // 2,
        "D": max(ecc),
        "f": f,
        "alpha": independence_number(n, adj),
        "r": r,
        "hh": anomaly,
        "witness": witness,
    }


def nx_check(line, n, adj, inv):
    """Recompute with networkx; return the list of disagreeing fields."""
    import networkx as nx

    G = nx.from_graph6_bytes(line.encode())
    bad = []
    if G.number_of_nodes() != n or {frozenset(e) for e in G.edges()} != {
            frozenset((u, w)) for u in range(n) for w in adj[u] if u < w}:
        return ["parse"]
    if not nx.is_connected(G):
        return ["connected"]
    if nx.diameter(G) != inv["D"]:
        bad.append("D")
    if n == 1:
        alpha = 1
    else:
        alpha = nx.max_weight_clique(nx.complement(G), weight=None)[1]
    if alpha != inv["alpha"]:
        bad.append("alpha")
    if not nx.is_forest(G.subgraph(inv["witness"])) or len(inv["witness"]) != inv["f"]:
        bad.append("f")
    return bad


# ------------------------------------------------------------------ summary
class Summary:
    def __init__(self, K=5):
        self.K = K
        self.graphs = 0
        self.disconnected = 0
        self.count = {}
        self.trees = {}
        self.hist = {}
        self.checks = {}
        self.exs = {}
        self.exfa = {}

    def _offer(self, table, key, val, g6):
        cur = table.get(key)
        if cur is None or val < cur[0]:
            table[key] = [val, [g6]]
        elif val == cur[0]:
            cur[1] = sorted(set(cur[1] + [g6]))[:self.K]

    def add(self, g6, n, inv):
        self.graphs += 1
        if inv is None:
            self.disconnected += 1
            return
        D, f, alpha, r = inv["D"], inv["f"], inv["alpha"], inv["r"]
        c3, c4 = -(-D // 3), -(-D // 4)
        self.count[n] = self.count.get(n, 0) + 1
        tree = inv["m"] == n - 1
        if tree:
            self.trees[n] = self.trees.get(n, 0) + 1
        key = (n, D, f - alpha, alpha - r)
        self.hist[key] = self.hist.get(key, 0) + 1
        ck = self.checks.setdefault(n, [0] * len(CHECK_NAMES))
        ck[0] += f - r - c3 < 0
        ck[1] += f < alpha + c4
        ck[2] += n >= 2 and f < alpha + 1
        ck[3] += f == alpha + 1 and D > 4
        ck[4] += r > alpha
        ck[5] += inv["hh"]
        ck[6] += tree and f != n
        self._offer(self.exs, (n, D), f - r - c3, g6)
        self._offer(self.exfa, (n, D), f - alpha, g6)

    def lines(self):
        out = ["WOWII61-SUMMARY v1", "CROSSCHECK 0",
               "GRAPHS %d" % self.graphs, "DISCONNECTED %d" % self.disconnected]
        out += ["N %d %d" % kv for kv in sorted(self.count.items())]
        out += ["TREES %d %d" % kv for kv in sorted(self.trees.items())]
        out += ["H %d %d %d %d %d" % (k + (c,)) for k, c in sorted(self.hist.items())]
        for n in sorted(self.checks):
            out += ["CHECK %d %s %d" % (n, nm, c)
                    for nm, c in zip(CHECK_NAMES, self.checks[n])]
        for tag, table in (("EX_SLACK", self.exs), ("EX_FA", self.exfa)):
            for (n, D), (val, g6s) in sorted(table.items()):
                out += ["%s %d %d %d %s" % (tag, n, D, val, s) for s in g6s]
        return out


# -------------------------------------------------------------------- modes
def main(argv):
    use_nx = "--nx" in argv
    args = [a for a in argv if a != "--nx"]
    nx_bad = 0
    if args[:1] == ["--check-dump"]:
        total = mismatches = 0
        with open(args[1]) as fh:
            for raw in fh:
                parts = raw.split()
                if not parts:
                    continue
                g6, vals = parts[0], [int(x) for x in parts[1:]]
                n, adj = parse_graph6(g6)
                inv = invariants(n, adj)
                mine = None if inv is None else [n, inv["m"], inv["D"], inv["f"],
                                                 inv["alpha"], inv["r"]]
                total += 1
                if mine != vals:
                    mismatches += 1
                    print("MISMATCH", g6, vals, mine)
                if use_nx and inv is not None and nx_check(g6, n, adj, inv):
                    nx_bad += 1
                    print("NX-MISMATCH", g6)
        print("checked %d dumped graphs: %d mismatches%s" % (
            total, mismatches, ", %d networkx disagreements" % nx_bad if use_nx else ""))
        return 0 if mismatches == 0 and nx_bad == 0 else 1
    summ = Summary()
    if args[:1] == ["--labeled"]:
        n = int(args[1])
        pairs = [(i, j) for j in range(1, n) for i in range(j)]
        for e in range(1 << len(pairs)):
            adj = [set() for _ in range(n)]
            for k, (i, j) in enumerate(pairs):
                if (e >> k) & 1:
                    adj[i].add(j)
                    adj[j].add(i)
            summ.add(to_graph6(n, adj), n, invariants(n, adj))
    else:
        for raw in sys.stdin:
            g6 = raw.strip()
            if not g6 or g6.startswith(">"):
                continue
            n, adj = parse_graph6(g6)
            inv = invariants(n, adj)
            if use_nx and inv is not None and nx_check(g6, n, adj, inv):
                nx_bad += 1
                print("NX-MISMATCH", g6, file=sys.stderr)
            summ.add(g6, n, inv)
    print("\n".join(summ.lines()))
    if use_nx:
        print("networkx disagreements: %d" % nx_bad, file=sys.stderr)
    return 0 if nx_bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
