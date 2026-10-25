#!/usr/bin/env python3
"""Second check, sharing no code with check_duality.py: the facts the proof of eq:conj uses.

Let S = {a, b, a + b} with 1 <= a < b, c = a + b, let P be the set of P-positions (value 0) of
the wall game, and let p be the period of Theorem 3 of arXiv:2601.18715v3. For every such set
with b <= B the script checks, over several periods,

  (T1)    the wall value of x is 0, 1, 2 or 3 according as x, x - a, x + b or none of them lies in P;
  (T2)    the sink value of t + 1 is 0, 1, 2 or 3 according as t - c, t, t - a or none of them
          lies in P (the three conditions in (T1), and in (T2), are mutually exclusive);
  (gap)   no element of P lies in [p - c, p);
  (T3)    x in P iff p - c - 1 - x in P, for 0 <= x <= p - c - 1;
  (B)     the n-th element of P is n + a floor(n / a) + b floor(n / N) with
          N = a floor(b / 2a) + min(a, b mod 2a), and p = 2 lcm(a, N) + (a / gcd(a, N)) b.

Usage: python3 check_translates.py [B]        (default B = 40)
"""
import sys
from math import gcd


def least_excluded(mask):
    """Smallest k >= 0 whose bit is clear in mask."""
    k = 0
    while mask >> k & 1:
        k += 1
    return k


def paper_period(a, b):
    m = a
    delta = b - a
    d = delta % (2 * m)
    return 3 * m + 2 * delta - d if d <= m else m * (m + 2 * delta + d) // gcd(m, d)


def nim_tables(a, b, size):
    """Wall values on [0, size) and sink values on [-c, size), the latter as a dict."""
    c = a + b
    wall = [0] * size
    for x in range(size):
        mask = 0
        for s in (a, b, c):
            if x >= s:
                mask |= 1 << wall[x - s]
        wall[x] = least_excluded(mask)
    sink = {y: 0 for y in range(-c, 1)}
    for y in range(1, size):
        sink[y] = least_excluded((1 << sink[y - a]) | (1 << sink[y - b]) | (1 << sink[y - c]))
    return wall, sink


def failures(a, b):
    c = a + b
    p = paper_period(a, b)
    size = 4 * p + 2 * c
    wall, sink = nim_tables(a, b, size)
    in_p = [val == 0 for val in wall]
    span = 3 * p  # positions checked; x + b and t + 1 stay inside the tables
    out = []
    for x in range(span):
        conds = [in_p[x], x >= a and in_p[x - a], in_p[x + b]]
        if sum(conds) > 1 or wall[x] != (conds.index(True) if any(conds) else 3):
            out.append(f"(T1) fails at x = {x}")
            break
    for t in range(span):
        conds = [t >= c and in_p[t - c], in_p[t], t >= a and in_p[t - a]]
        if sum(conds) > 1 or sink[t + 1] != (conds.index(True) if any(conds) else 3):
            out.append(f"(T2) fails at t = {t}")
            break
    if any(in_p[x] for x in range(p - c, p)):
        out.append("(gap) fails")
    if any(in_p[x] != in_p[p - c - 1 - x] for x in range(p - c)):
        out.append("(T3) fails")
    N = a * (b // (2 * a)) + min(a, b % (2 * a))
    zeros = [x for x in range(span) if in_p[x]]
    if zeros != [n + a * (n // a) + b * (n // N) for n in range(len(zeros))]:
        out.append("(B) the bracket formula fails")
    if p != 2 * (a * N // gcd(a, N)) + (a // gcd(a, N)) * b:
        out.append("(B) the period identity fails")
    return out


def main():
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    total = bad = 0
    for b in range(2, B + 1):
        for a in range(1, b):
            total += 1
            for msg in failures(a, b):
                bad += 1
                print(f"S = {{{a}, {b}, {a + b}}}: {msg}")
    print(f"checked {total} sets with s2 <= {B}: {bad} failures")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
