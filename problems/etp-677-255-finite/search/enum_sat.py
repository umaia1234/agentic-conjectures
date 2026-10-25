#!/usr/bin/env python3
"""Enumerate all models of a gen_cnf.py CNF (projected on the table vars)
with pysat/CaDiCaL + blocking clauses; print canonical tables.
usage: enum_sat.py n cnf_file"""
import sys
from pysat.formula import CNF
from pysat.solvers import Solver

n = int(sys.argv[1])
f = CNF(from_file=sys.argv[2])
s = Solver(name="cadical153", bootstrap_with=f.clauses)
count = 0
while s.solve():
    m = s.get_model()
    tab = []
    block = []
    for x in range(n):
        for y in range(n):
            for v in range(n):
                var = 1 + (x * n + y) * n + v
                if m[var - 1] > 0:
                    tab.append(v)
                    block.append(-var)
    # sanity: verify E677 independently
    T = [tab[i * n:(i + 1) * n] for i in range(n)]
    assert all(T[y][T[x][T[T[y][x]][y]]] == x for x in range(n) for y in range(n))
    count += 1
    print("SOL", " ".join(map(str, tab)))
    s.add_clause(block)
print("COUNT", count)
