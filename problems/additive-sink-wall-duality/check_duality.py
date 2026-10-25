#!/usr/bin/env python3
"""Check the sink-wall duality eq:conj of arXiv:2601.18715v3 by direct computation.

For every additive set S = {s1, s2, s1 + s2} with 1 <= s1 < s2 <= B, the script computes both
nim-sequences straight from their mex recursions,

    wall:  v_w(x) = mex{v_w(x - s) : s in S, s <= x}              for x >= 0,
    sink:  v_s(y) = 0 for y <= 0,  v_s(y) = mex{v_s(y - s) : s in S}  for y >= 1,

takes p from the period formula of Theorem 3 (thm:main) of the paper, and checks

  1. eq:conj, v_w([x]_p) = sigma(v_s([-s2 - x]_p)), for every residue x mod p, where [.]_p is the
     least nonnegative residue and sigma swaps 0 and 2 (both sides depend only on x mod p);
  2. that p is a period of both sequences (the wall from 0, the sink from 1), and v_s(p) = 0;
  3. that p is the least period of the sink nim-sequence and of the wall outcomes, as Theorem 3
     and Corollary 4 of the paper state.

Usage: python3 check_duality.py [B]        (default B = 40, the 780 sets with s2 <= 40)
"""
import sys
from math import gcd

SIGMA = {0: 2, 1: 1, 2: 0, 3: 3}


def mex(values):
    m = 0
    while m in values:
        m += 1
    return m


def period(s1, s2):
    """p(m, delta) of thm:main, with m = s1 and delta = s2 - s1."""
    m, delta = s1, s2 - s1
    d = delta % (2 * m)
    if d <= m:
        return 3 * m + 2 * delta - d
    return m * (m + 2 * delta + d) // gcd(m, d)


def wall_values(S, n):
    """[v_w(0), ..., v_w(n - 1)]."""
    v = []
    for x in range(n):
        v.append(mex({v[x - s] for s in S if s <= x}))
    return v


def sink_values(S, n):
    """[v_s(0), ..., v_s(n - 1)], where v_s(0) = 0 is the sink."""
    v = [0]
    for y in range(1, n):
        v.append(mex({v[y - s] if y - s > 0 else 0 for s in S}))
    return v


def prime_divisors(n):
    out, q = [], 2
    while q * q <= n:
        if n % q == 0:
            out.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        out.append(n)
    return out


def has_period(seq, start, q, p):
    """seq[i + q] == seq[i] for start <= i < start + p (enough once seq is p-periodic)."""
    return all(seq[i + q] == seq[i] for i in range(start, start + p))


def check(s1, s2):
    """Return a list of failure messages for S = {s1, s2, s1 + s2}."""
    S = (s1, s2, s1 + s2)
    p = period(s1, s2)
    n = 2 * p + S[2] + 1
    w = wall_values(S, n)
    v = sink_values(S, n)
    bad = []
    for x in range(p):
        if w[x] != SIGMA[v[(-s2 - x) % p]]:
            bad.append(f"eq:conj fails at x = {x}")
            break
    # Moves from x >= s3 (wall) or y > s3 (sink) see only the previous s3 values, so agreement on
    # one window of length p + s3 gives p-periodicity everywhere.
    if not has_period(w, 0, p, p + S[2]):
        bad.append("p is not a period of the wall sequence")
    if not has_period(v, 1, p, p + S[2]):
        bad.append("p is not a period of the sink sequence")
    if v[p] != 0:
        bad.append("v_s(p) != 0")
    outcome = [int(t == 0) for t in w]
    for q in prime_divisors(p):
        if has_period(v, 1, p // q, p):
            bad.append(f"the sink sequence has the smaller period {p // q}")
        if has_period(outcome, 0, p // q, p):
            bad.append(f"the wall outcomes have the smaller period {p // q}")
    return bad


def main():
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    sets = failures = 0
    for s2 in range(2, B + 1):
        for s1 in range(1, s2):
            sets += 1
            for msg in check(s1, s2):
                failures += 1
                print(f"S = {{{s1}, {s2}, {s1 + s2}}}: {msg}")
    print(f"checked {sets} sets with s2 <= {B}: {failures} failures")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
