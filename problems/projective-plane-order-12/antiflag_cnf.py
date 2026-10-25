#!/usr/bin/env python3
"""CNF for projective planes of order n with a cyclic collineation group G = Z_{n+1}
fixing an antiflag (P, l) and acting semiregularly on the other points and lines.

Usage: python3 antiflag_cnf.py n out.cnf [--interval]

For n = 12 every collineation of order 13 has exactly this action (README, part 3).
Write w = n + 1 and r = n - 1 (the number of point orbits off l and different from P).
After choosing orbit base points (README), such a plane is the same as a family of
permutations pi_s of {0..r-1}, one for each s in Z_w \\ {0}, such that

  (*) for every delta in Z_w \\ {0} and all i, i' in {0..r-1} there is exactly one
      s in Z_w \\ {0, delta} with pi_s(i) = pi_{s - delta}(i').

(pi_s(i) = j means: the base point of point orbit i lies on the line j shifted by -s.)
Relabelling the line orbits replaces every pi_s by tau o pi_s, so WLOG pi_1 = identity.
Relabelling the point orbits replaces every pi_s by pi_s o kappa; combined with the line
relabelling tau = kappa^{-1} this conjugates every pi_s by kappa and keeps pi_1 = id and (*).
Every permutation is conjugate to a product of cycles on consecutive intervals
(a a+1 ... b), i.e. to a permutation with pi(i) <= i + 1 for all i; so with --interval we
may also assume pi_2(i) <= i + 1 (n >= 3).

Variables (1-based):
  x(s,i,j) = 1 + ((s-1)*r + i)*r + j        s = 1..n, i, j = 0..r-1   [pi_s(i) = j]
  z(s,t,i,i') for 1 <= s < t <= n           [pi_s(i) = pi_t(i')], numbered after x
Clauses:
  (1) each pi_s is a permutation: exactly one j per (s,i) and one i per (s,j);
  (2) pi_1 = identity: unit clauses x(1,i,i);
  (2') only with --interval: unit clauses -x(2,i,j) for j > i + 1;
  (3) z(s,t,i,i') <-> OR_j (x(s,i,j) and x(t,i',j)), as
      (-x(s,i,j) or -x(t,i',j) or z) and (-z or -x(s,i,j) or x(t,i',j)) for all j;
  (4) (*) as exactly-one constraints over the r literals z(s, s-delta, i, i')
      (z(s,t,i,i') with s > t means z(t,s,i',i)): one at-least-one clause and pairwise
      at-most-one clauses; duplicates (delta and -delta) are merged.
"""
import sys


def build(n, interval=False):
    w, r = n + 1, n - 1
    if n < 2:
        raise ValueError("n >= 2")

    def x(s, i, j):
        return 1 + ((s - 1) * r + i) * r + j

    nx = n * r * r
    zid = {}

    def z(s, t, i, ip):
        if s > t:
            s, t, i, ip = t, s, ip, i
        key = (s, t, i, ip)
        if key not in zid:
            zid[key] = nx + 1 + len(zid)
        return zid[key]

    clauses = []
    seen = set()

    def add(cl):
        key = tuple(sorted(cl))
        if key not in seen:
            seen.add(key)
            clauses.append(list(key))

    def exactly_one(lits):
        add(lits)
        for a in range(len(lits)):
            for b in range(a + 1, len(lits)):
                add([-lits[a], -lits[b]])

    for s in range(1, n + 1):
        for i in range(r):
            exactly_one([x(s, i, j) for j in range(r)])
        for j in range(r):
            exactly_one([x(s, i, j) for i in range(r)])
    for i in range(r):
        add([x(1, i, i)])
    if interval and n >= 3:
        for i in range(r):
            for j in range(i + 2, r):
                add([-x(2, i, j)])
    for s in range(1, n + 1):
        for t in range(s + 1, n + 1):
            for i in range(r):
                for ip in range(r):
                    zz = z(s, t, i, ip)
                    for j in range(r):
                        add([-x(s, i, j), -x(t, ip, j), zz])
                        add([-zz, -x(s, i, j), x(t, ip, j)])
    for delta in range(1, w):
        for i in range(r):
            for ip in range(r):
                lits = [z(s, (s - delta) % w, i, ip) for s in range(1, w) if s != delta]
                exactly_one(lits)
    return nx + len(zid), clauses


def main():
    if len(sys.argv) not in (3, 4) or (len(sys.argv) == 4 and sys.argv[3] != "--interval"):
        print(__doc__)
        return 2
    n = int(sys.argv[1])
    interval = len(sys.argv) == 4
    nvars, clauses = build(n, interval)
    with open(sys.argv[2], "w") as fh:
        fh.write(f"c planes of order {n} with Z_{n + 1} fixing an antiflag, pi_1 = id"
                 f"{', pi_2 interval form' if interval else ''}\n")
        fh.write(f"p cnf {nvars} {len(clauses)}\n")
        for cl in clauses:
            fh.write(" ".join(map(str, cl)) + " 0\n")
    print(f"vars={nvars} clauses={len(clauses)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
