"""Exact solvers for i(G) (independent domination) and mu*(G) (saturation number = min maximal
matching) -- two independent implementations each: pysat/CaDiCaL decision queries and CP-SAT
optimisation. Graphs are networkx graphs with integer labels 0..n-1."""
import itertools
import networkx as nx
from ortools.sat.python import cp_model
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153


def load_g6(path):
    G = nx.from_graph6_bytes(open(path).read().strip().encode())
    return nx.convert_node_labels_to_integers(G)


def ids_cnf(G, k):
    """CNF: an independent dominating set of size <= k exists. var(v) = v + 1."""
    n = G.number_of_nodes()
    cls = [[v + 1] + [u + 1 for u in G[v]] for v in range(n)]
    cls += [[-(u + 1), -(v + 1)] for u, v in G.edges()]
    cls += CardEnc.atmost(lits=list(range(1, n + 1)), bound=k, top_id=n,
                          encoding=EncType.seqcounter).clauses
    return cls


def ids_exists(G, k):
    with Cadical153(bootstrap_with=ids_cnf(G, k)) as s:
        if s.solve():
            m = s.get_model()
            return [v for v in range(G.number_of_nodes()) if m[v] > 0]
        return None


def mm_exists(G, k):
    """Maximal matching with <= k edges (pysat). Returns the matching or None."""
    E = list(G.edges())
    ev = {e: j + 1 for j, e in enumerate(E)}
    inc = {v: [] for v in G}
    for e, j in ev.items():
        inc[e[0]].append(j)
        inc[e[1]].append(j)
    cls = []
    for v in G:
        for a, b in itertools.combinations(inc[v], 2):
            cls.append([-a, -b])
    for u, v in E:
        cls.append(inc[u] + inc[v])
    cls += CardEnc.atmost(lits=list(ev.values()), bound=k, top_id=len(E),
                          encoding=EncType.seqcounter).clauses
    with Cadical153(bootstrap_with=cls) as s:
        if s.solve():
            m = s.get_model()
            return [E[j - 1] for j in ev.values() if m[j - 1] > 0]
        return None


def i_sat(G):
    """Exact i(G) by descending decision queries."""
    D = ids_exists(G, G.number_of_nodes())
    while True:
        D2 = ids_exists(G, len(D) - 1)
        if D2 is None:
            return len(D), D
        D = D2


def mustar_sat(G):
    M = mm_exists(G, G.number_of_edges())
    while True:
        M2 = mm_exists(G, len(M) - 1)
        if M2 is None:
            return len(M), M
        M = M2


def _cp(G, kind, workers=1, limit=None):
    m = cp_model.CpModel()
    if kind == 'mu':
        E = list(G.edges())
        y = {e: m.NewBoolVar('') for e in E}
        inc = {v: [] for v in G}
        for e in E:
            inc[e[0]].append(y[e])
            inc[e[1]].append(y[e])
        for v in G:
            m.Add(sum(inc[v]) <= 1)
        for u, v in E:
            m.Add(sum(inc[u]) + sum(inc[v]) >= 1)
        m.Minimize(sum(y.values()))
    else:
        x = {v: m.NewBoolVar('') for v in G}
        for v in G:
            m.Add(x[v] + sum(x[u] for u in G[v]) >= 1)
        for u, v in G.edges():
            m.Add(x[u] + x[v] <= 1)
        m.Minimize(sum(x.values()))
    s = cp_model.CpSolver()
    s.parameters.num_workers = workers
    if limit:
        s.parameters.max_time_in_seconds = limit
    st = s.Solve(m)
    if st != cp_model.OPTIMAL:
        return None
    return int(round(s.ObjectiveValue()))


def i_cp(G, workers=1, limit=None):
    return _cp(G, 'i', workers, limit)


def mustar_cp(G, workers=1, limit=None):
    return _cp(G, 'mu', workers, limit)


def i_brute(G):
    best = G.number_of_nodes()
    # maximal independent sets = maximal cliques of the complement
    for S in nx.find_cliques(nx.complement(G)):
        best = min(best, len(S))
    return best


def mustar_brute(G):
    """min over independent U with G-U having a perfect matching: (n-|U|)/2."""
    # exhaustive over edge subsets in order of size (small graphs only)
    E = list(G.edges())
    for k in range(0, len(E) + 1):
        for M in itertools.combinations(E, k):
            cov = set()
            ok = True
            for u, v in M:
                if u in cov or v in cov:
                    ok = False
                    break
                cov.add(u)
                cov.add(v)
            if not ok:
                continue
            if all(u in cov or v in cov for u, v in E):
                return k
    return None


def blowup(G, t):
    """Lexicographic product G[K_t-bar]: vertex (v, a) -> v * t + a."""
    H = nx.Graph()
    n = G.number_of_nodes()
    H.add_nodes_from(range(n * t))
    for u, v in G.edges():
        for a in range(t):
            for b in range(t):
                H.add_edge(u * t + a, v * t + b)
    return H
