#!/usr/bin/env python3
"""Validate the symmetry breaking in general mode (where solutions exist):
for each group, SAT(no symmetry breaking) must equal OR over the cases, and
the number of distinct solutions f must equal the size of the union of the
Aut(G)-conjugates of the case solutions.  usage: test_sb.py groups cases lo hi"""
import sys
from pysat.solvers import Solver
from tinv_cnf import cnf, read_group
from export_cases import aut_gens

gpath, cpath, lo, hi = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
cases = {}
for l in open(cpath):
    m, i, a, b = map(int, l.split())
    cases.setdefault((m, i), []).append((a, b))


def all_solutions(m, cl, assum=()):
    s = Solver(name="cadical153", bootstrap_with=cl)
    sols = []
    while s.solve(assumptions=list(assum)):
        if len(sols) >= 50000:
            raise SystemExit("too many solutions")
        mod = s.get_model()
        f = tuple(v for z in range(m) for v in range(m) if mod[z * m + v] > 0)
        sols.append(f)
        s.add_clause([-(z * m + f[z] + 1) for z in range(m)])
    return sols


for (m, i), cs in sorted(cases.items()):
    if not lo <= m <= hi:
        continue
    _, _, desc, mul = read_group(gpath, m, i)
    nv, cl = cnf(m, mul, False)
    full = set(all_solutions(m, cl))
    part = set()
    for a, b in cs:
        part |= set(all_solutions(m, cl, [a + 1, a * m + b + 1]))
    assert part == {f for f in full if any(f[0] == a and f[a] == b for a, b in cs)}
    # completeness: the Aut(G)-conjugates of the case solutions are all solutions
    gens = aut_gens(m, i, [v for row in mul for v in row])
    clos, queue = set(part), list(part)
    for f in queue:
        for p in gens:
            pinv = [0] * m
            for x, y in enumerate(p):
                pinv[y] = x
            g = tuple(p[f[pinv[x]]] for x in range(m))
            if g not in clos:
                clos.add(g)
                queue.append(g)
    assert clos == full, (m, i)
    print(m, i, desc, "full", len(full), "cases", len(cs), "case-sols", len(part),
          "OK" if bool(full) == bool(part) else "MISMATCH", flush=True)
