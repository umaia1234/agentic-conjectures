#!/usr/bin/env python3
"""Semantic audit of a DIMACS formula for normalised lambda = 1 difference sets.

Usage: python3 audit_ds_cnf.py v k m R formula.cnf

Independently of ds_cnf.py, checks that EVERY clause of the formula is one of the
clause types below, each of which is satisfied by the normal-form image of any
(relative) difference set D of Z_v (relative to N = m Z_v), with x_i = [i in D] and
y_{i,c} = [i in D and i + d_c in D]  (variable numbering as documented in ds_cnf.py):
  U   unit clause x_0 or x_1;
  D1  (-y_{i,c} or x_i),  D2  (-y_{i,c} or x_{i+d_c}),  D3  (y_{i,c} or -x_i or -x_{i+d_c});
  ALO (y_{0,c} or ... or y_{v-1,c}) with ALL v literals of one class c;
  AMO (-y_{i,c} or -y_{j,c}), i != j;
  F   (-x_a or -x_{a+f}) with 0 != f in N;
  RAT (x_3 or ... or x_j or -x_a or -x_{a+s} or -x_{a+js}) with 3 <= j <= R, s a unit,
      the three points distinct and none of them in [3, j].
A formula all of whose clauses are valid is implied by the existence of a difference
set, so if it is unsatisfiable (DRAT-checked) no difference set exists.  Subsets of the
full formula (e.g. an UNSAT core) pass this audit as well.  Exit 0 iff all clauses pass.
"""
import sys
from collections import Counter
from math import gcd


def main():
    if len(sys.argv) != 6:
        print(__doc__)
        return 2
    v, k, m, R = (int(a) for a in sys.argv[1:5])
    if v % m or k * (k - 1) != v - v // m:
        print("FAIL: inconsistent parameters")
        return 1
    if any(2 * d % v == 0 for d in range(1, v) if d % m):
        print("FAIL: self-inverse element outside N")
        return 1
    reps = [d for d in range(1, v) if d % m and d < v - d]
    nv_expected = v + len(reps) * v

    def xvar(lit):  # element of Z_v for an x literal, or None
        a = abs(lit)
        return a - 1 if 1 <= a <= v else None

    def yvar(lit):  # (i, c) for a y literal, or None
        a = abs(lit) - v - 1
        if 0 <= a < len(reps) * v:
            return a % v, a // v
        return None

    counts = Counter()
    header = None
    with open(sys.argv[5]) as fh:
        for raw in fh:
            line = raw.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p"):
                _, fmt, nv, nc = line.split()
                header = (fmt, int(nv), int(nc))
                if fmt != "cnf" or int(nv) != nv_expected:
                    print("FAIL: header", line)
                    return 1
                continue
            lits = [int(t) for t in line.split()]
            if lits[-1] != 0 or 0 in lits[:-1]:
                print("FAIL: malformed clause", line)
                return 1
            cl = set(lits[:-1])
            kind = classify(cl, v, m, R, reps, xvar, yvar)
            if kind is None:
                print("FAIL: unjustified clause", sorted(cl))
                return 1
            counts[kind] += 1
    total = sum(counts.values())
    if header is None or total != header[2]:
        print("FAIL: clause count does not match header")
        return 1
    print(f"OK: all {total} clauses justified;",
          " ".join(f"{t}={counts[t]}" for t in sorted(counts)))
    return 0


def classify(cl, v, m, R, reps, xvar, yvar):
    lits = sorted(cl, key=abs)
    xs = [l for l in lits if xvar(l) is not None]
    ys = [l for l in lits if yvar(l) is not None]
    if len(xs) + len(ys) != len(lits):
        return None
    if not ys:
        if len(xs) == 1 and xs[0] > 0 and xvar(xs[0]) in (0, 1):
            return "U"
        pos = sorted(xvar(l) for l in xs if l > 0)
        neg = sorted(xvar(l) for l in xs if l < 0)
        if not pos and len(neg) == 2:
            f = (neg[1] - neg[0]) % v
            return "F" if f % m == 0 else None
        if len(neg) == 3 and pos:
            j = pos[-1]
            if pos != list(range(3, j + 1)) or j > R:
                return None
            if any(3 <= e <= j for e in neg):
                return None
            for a in neg:
                for b in neg:
                    s = (b - a) % v
                    if a == b or gcd(s, v) != 1:
                        continue
                    c = (a + j * s) % v
                    if c in neg and c not in (a, b):
                        return "RAT"
        return None
    if not xs:
        cs = {yvar(l)[1] for l in ys}
        if len(cs) != 1:
            return None
        c = cs.pop()
        if all(l > 0 for l in ys) and sorted(yvar(l)[0] for l in ys) == list(range(v)):
            return "ALO"
        if len(ys) == 2 and all(l < 0 for l in ys):
            return "AMO"
        return None
    if len(ys) != 1:
        return None
    (i, c), d = yvar(ys[0]), reps[yvar(ys[0])[1]]
    pts = sorted(xvar(l) for l in xs)
    if ys[0] < 0 and len(xs) == 1 and xs[0] > 0 and pts[0] in (i, (i + d) % v):
        return "D12"
    if ys[0] > 0 and len(xs) == 2 and all(l < 0 for l in xs) and \
            pts == sorted([i, (i + d) % v]):
        return "D3"
    return None


if __name__ == "__main__":
    sys.exit(main())
