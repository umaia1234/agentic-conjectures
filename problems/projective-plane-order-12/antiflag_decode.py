#!/usr/bin/env python3
"""Decode a model of antiflag_cnf.py and verify that it is a projective plane.

Usage: python3 antiflag_decode.py n solver_output

Reads the `v` lines of a SAT solver model, extracts the permutations pi_s, and rebuilds
the incidence structure explicitly, independently of the CNF:
  points: P, (0,x) [on l], (i,x) for i = 1..r;  lines: l, (0',y) [through P], (j,y);
  P on (0',y) for all y; (0,x) on l; (0,x) on (0',y) iff x = y; (0,x) on (j,y) iff x = y;
  (i,x) on (0',y) iff x = y; (i,x) on (j,y) iff pi_{x-y}(i-1) = j-1  (x - y != 0),
with all coordinates in Z_{n+1}.  It then checks: n^2+n+1 points and lines, every line
has n+1 points, every point is on n+1 lines, any two points lie on exactly one common
line, and the map x -> x+1 is a collineation fixing only P and l.  Exit 0 iff all hold.
"""
import itertools
import sys


def main():
    if len(sys.argv) != 3:
        print(__doc__)
        return 2
    n = int(sys.argv[1])
    w, r = n + 1, n - 1
    true = set()
    with open(sys.argv[2]) as fh:
        for line in fh:
            if line.startswith("v "):
                true.update(int(t) for t in line.split()[1:] if int(t) > 0)
    pi = {}
    for s in range(1, n + 1):
        pi[s] = {}
        for i in range(r):
            js = [j for j in range(r) if 1 + ((s - 1) * r + i) * r + j in true]
            if len(js) != 1:
                print("FAIL: model is not a permutation")
                return 1
            pi[s][i] = js[0]
    points = ["P"] + [(0, x) for x in range(w)] + [(i, x) for i in range(1, r + 1)
                                                   for x in range(w)]
    lines = ["l"] + [("0'", y) for y in range(w)] + [(j, y) for j in range(1, r + 1)
                                                     for y in range(w)]

    def inc(p, L):
        if p == "P":
            return L != "l" and L[0] == "0'"
        if L == "l":
            return p[0] == 0
        (i, x), (j, y) = p, L
        if j == "0'":
            return x == y
        if i == 0:
            return x == y
        d = (x - y) % w
        return d != 0 and pi[d][i - 1] == j - 1

    v = n * n + n + 1
    if len(points) != v or len(lines) != v:
        print("FAIL: wrong counts")
        return 1
    on = {p: frozenset(L for L in lines if inc(p, L)) for p in points}
    if any(len(on[p]) != n + 1 for p in points):
        print("FAIL: point degree")
        return 1
    if any(sum(1 for p in points if inc(p, L)) != n + 1 for L in lines):
        print("FAIL: line size")
        return 1
    for p, q in itertools.combinations(points, 2):
        if len(on[p] & on[q]) != 1:
            print("FAIL: two points not on exactly one line", p, q)
            return 1

    def shift(e):
        return e if e in ("P", "l") else (e[0], (e[1] + 1) % w)

    for p in points:
        for L in lines:
            if inc(p, L) != inc(shift(p), shift(L)):
                print("FAIL: shift is not a collineation")
                return 1
    fixed = [p for p in points if shift(p) == p] + [L for L in lines if shift(L) == L]
    if fixed != ["P", "l"]:
        print("FAIL: fixed elements", fixed)
        return 1
    print(f"OK: projective plane of order {n} with a Z_{w} collineation fixing only P, l")
    for s in range(1, n + 1):
        print(f"pi_{s} = {[pi[s][i] for i in range(r)]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
