#!/usr/bin/env python3
"""Symmetry-breaking cases for the translation-invariant search.

Aut(G) acts on solutions f by conjugation f -> phi o f o phi^-1 (phi is an
isomorphism between the two magmas and preserves fixed points), so we may
assume that f(e) = a is the least element of its Aut(G)-orbit and that
f(a) = b is the least element of its Stab(a)-orbit.  Only the generators of
Aut(G) come from GAP; each is checked here to be an automorphism of the
exported Cayley table, and orbits and stabilizer generators (Schreier's
lemma) are computed here.  Missing generators would only weaken the
symmetry breaking, never make it unsound.  One line per case:
  order id a b
usage: export_cases.py <groups file> lo hi [general] > cases.txt
(anti mode omits a = e and b = a: f must be fixed-point free.)"""
import sys
from sage.all__sagemath_gap import libgap


def orbits(m, gens):
    orb, seen = [], [False] * m
    for s in range(m):
        if not seen[s]:
            o, seen[s] = [s], True
            for c in o:
                for g in gens:
                    if not seen[g[c]]:
                        seen[g[c]] = True
                        o.append(g[c])
            orb.append(o)
    return orb


def stabilizer_gens(m, gens, a):
    trans = {a: list(range(m))}          # trans[c] maps a to c
    queue = [a]
    for c in queue:
        for g in gens:
            d = g[c]
            if d not in trans:
                trans[d] = [g[trans[c][x]] for x in range(m)]
                queue.append(d)
    sg = set()
    for c, t in trans.items():
        for g in gens:
            ti = [0] * m
            for x, y in enumerate(trans[g[c]]):
                ti[y] = x
            s = tuple(ti[g[t[x]]] for x in range(m))   # t_{g(c)}^-1 g t_c
            assert s[a] == a
            sg.add(s)
    return [list(s) for s in sg]


def aut_gens(m, i, tab):
    """Generators of Aut(SmallGroup(m, i)) as permutations of the element
    numbering of export_groups.py, each checked against the table."""
    G = libgap.SmallGroup(m, i)
    els = list(libgap.Elements(G))
    one = libgap.Identity(G)
    els.sort(key=lambda g: g != one)
    pos = {str(g): k for k, g in enumerate(els)}
    assert tab == [pos[str(x * y)] for x in els for y in els]
    mul = [tab[k * m:(k + 1) * m] for k in range(m)]
    gens = []
    for phi in libgap.GeneratorsOfGroup(libgap.AutomorphismGroup(G)):
        p = [pos[str(libgap.Image(phi, g))] for g in els]
        assert sorted(p) == list(range(m))
        assert all(p[mul[x][y]] == mul[p[x]][p[y]] for x in range(m) for y in range(m))
        gens.append(p)
    return gens


def main():
    path, lo, hi = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    general = "general" in sys.argv[4:]
    tables = {}
    with open(path) as fh:
        for line in fh:
            t = line.split()
            tables[(int(t[0]), int(t[1]))] = list(map(int, t[3:]))
    for m in range(lo, hi + 1):
        for i in range(1, int(libgap.NumberSmallGroups(m)) + 1):
            gens = aut_gens(m, i, tables[(m, i)])
            for a in sorted(min(o) for o in orbits(m, gens)):
                if a == 0 and not general:
                    continue
                for b in sorted(min(o) for o in orbits(m, stabilizer_gens(m, gens, a))):
                    if b == a and not general:
                        continue
                    sys.stdout.write("%d %d %d %d\n" % (m, i, a, b))
            sys.stdout.flush()


if __name__ == "__main__":
    main()
