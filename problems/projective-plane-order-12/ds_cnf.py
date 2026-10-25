#!/usr/bin/env python3
"""Method C: DIMACS CNF for normalised lambda = 1 (relative) difference sets in Z_v.

Usage: python3 ds_cnf.py v k m out.cnf [R]

The formula is satisfiable iff Z_v contains a set D with 0, 1 in D such that every
element of Z_v outside N = m Z_v is a difference d - e (d, e in D) exactly once, no
nonzero element of N is a difference, and (if R >= 3) D satisfies the ratio normal form
below.  (m = v gives N = {0}: planar difference sets.)  k is only used for the sanity
check k(k-1) = v - |N|; |D| = k is implied by exact coverage and is not encoded.

Variables (1-based DIMACS numbering):
  x_i            = i + 1                    for i in Z_v           (i in D)
  y_{i,c}        = v + 1 + c*v + i          for class c, i in Z_v  (i, i + d_c both in D)
where the classes c = 0..C-1 are the pairs {d, -d} with d not in N and d < v - d,
listed by increasing representative d_c.

Clauses:
  (1) x_0 and x_1 (unit clauses);
  (2) y_{i,c} <-> (x_i and x_{i+d_c});
  (3) for every class c: at least one y_{i,c}, and pairwise at most one y_{i,c};
  (4) for every f in N with 0 < f < v - f: not (x_i and x_{i+f}) for all i;
  (5) only if R >= 3, for j = 3..R, every a in Z_v and every unit s of Z_v:
        x_3 or x_4 or ... or x_j or not x_a or not x_{a+s} or not x_{a+js}
      (tautologies dropped, duplicates merged).
Coverage of the class {d, -d} by exactly one unordered pair {i, i+d} is the same as
each of d and -d being represented exactly once as an ordered difference.

Why (1) and (5) lose no generality (details in README.md): x -> u x + c with u a unit
maps difference sets to difference sets.  Call (c - a)/(b - a) (b - a a unit) the ratio
of an ordered triple of distinct elements; ratios are invariant under these maps, and
they are >= 3 when differences are distinct.  If (a, b, c) attains the least ratio t of
D, then D' = (D - a)/(b - a) contains 0, 1 and t, all its elements other than 0, 1 are
ratios (so D' meets [2, t) nowhere), and no ratio of D' is below t.  Clause (5) for j
says: if D' meets [3, j] nowhere (so t > j) then no triple a, a+s, a+js (ratio j) lies
in D'.  Hence the normal-form image D' satisfies (1)-(5) whenever D is a solution.
"""
import sys
from math import gcd


def build(v, k, m, ratio_bound=0):
    if v % m != 0 or m < 2 or v < 3:
        raise ValueError("need m | v, m >= 2")
    n_size = v // m
    if k * (k - 1) != v - n_size:
        raise ValueError("k(k-1) != v - |N|")
    if any(2 * d % v == 0 for d in range(1, v) if d % m != 0):
        raise ValueError("self-inverse element outside N")
    reps = [d for d in range(1, v) if d % m != 0 and d < v - d]
    forb = [f for f in range(1, v) if f % m == 0 and f < v - f]
    nvars = v + len(reps) * v

    def x(i):
        return i % v + 1

    def y(i, c):
        return v + 1 + c * v + i

    clauses = [[x(0)], [x(1)]]
    for c, d in enumerate(reps):
        for i in range(v):
            clauses.append([-y(i, c), x(i)])
            clauses.append([-y(i, c), x(i + d)])
            clauses.append([y(i, c), -x(i), -x(i + d)])
        clauses.append([y(i, c) for i in range(v)])
        for i in range(v):
            for j in range(i + 1, v):
                clauses.append([-y(i, c), -y(j, c)])
    for f in forb:
        for i in range(v):
            clauses.append([-x(i), -x(i + f)])
    if ratio_bound >= 3:
        units = [s for s in range(1, v) if gcd(s, v) == 1]
        seen = set()
        for j in range(3, ratio_bound + 1):
            prefix = [x(i) for i in range(3, j + 1)]
            for a in range(v):
                for s in units:
                    tri = {a % v, (a + s) % v, (a + j * s) % v}
                    if len(tri) < 3 or any(3 <= e <= j for e in tri):
                        continue  # degenerate triple or tautology
                    cl = tuple(sorted(prefix + [-x(e) for e in tri]))
                    if cl not in seen:
                        seen.add(cl)
                        clauses.append(list(cl))
    return nvars, clauses, reps


def main():
    if len(sys.argv) not in (5, 6):
        print(__doc__)
        return 2
    v, k, m = (int(a) for a in sys.argv[1:4])
    ratio_bound = int(sys.argv[5]) if len(sys.argv) == 6 else 0
    nvars, clauses, reps = build(v, k, m, ratio_bound)
    with open(sys.argv[4], "w") as fh:
        fh.write(f"c lambda=1 difference sets in Z_{v}, k={k}, N={m}Z_{v}, 0 and 1 in D, "
                 f"ratio normal form up to {ratio_bound}\n")
        fh.write(f"p cnf {nvars} {len(clauses)}\n")
        for cl in clauses:
            fh.write(" ".join(map(str, cl)) + " 0\n")
    print(f"vars={nvars} clauses={len(clauses)} classes={len(reps)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
