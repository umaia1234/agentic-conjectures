#!/usr/bin/env python3
"""Sanity checks for OEIS A046969 Conjecture I (standard library only).

The proof of a(p) = 12(2p - 1) is the Lean module
AgenticConjectures/OeisA046969.lean; this script only cross-checks it and
the copied definition numerically, with exact rational arithmetic:

1. a(n) = den(B_{2n} / (2n(2n - 1))) for n >= 1, computed from the
   Bernoulli recurrence sum_{k<=n} C(n+1, k) B_k = 0 (B_1 = -1/2), matches
   the 35 terms of the OEIS DATA line.
2. For every prime 3 < p <= limit with 2p - 1 prime, a(p) = 12(2p - 1),
   the denominator of B_{2p} is 6, p divides its numerator and 2p - 1 does
   not, so a(p) / 12 = 2p - 1 is prime.
"""
import argparse
import sys
from fractions import Fraction
from math import comb

# OEIS A046969 DATA line (offset 1), as fetched on 2026-10-24.
OEIS_DATA = [
    12, 360, 1260, 1680, 1188, 360360, 156, 122400, 244188, 125400, 5796,
    1506960, 300, 93960, 2492028, 505920, 396, 2418179400, 444, 21106800,
    3109932, 118680, 25380, 104700960, 6468, 324360, 2283876, 382800, 40356,
    201025024200, 732, 2056320, 25241580, 8040, 646668,
]


def bernoulli_numbers(n_max: int) -> list[Fraction]:
    """B_0..B_{n_max} with B_1 = -1/2, as in Mathlib's `bernoulli`."""
    b = [Fraction(0)] * (n_max + 1)
    b[0] = Fraction(1)
    for n in range(1, n_max + 1):
        if n > 1 and n % 2 == 1:
            continue  # odd Bernoulli numbers beyond B_1 vanish
        s = sum(comb(n + 1, k) * b[k] for k in range(n) if b[k])
        b[n] = -s / (n + 1)
    return b


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def a(n: int, b: list[Fraction]) -> int:
    if n == 0:
        return 0
    m = 2 * n
    return (b[m] / (m * (m - 1))).denominator


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--limit", type=int, default=200, help="largest p to check")
    args = parser.parse_args()
    n_max = max(args.limit, len(OEIS_DATA))
    b = bernoulli_numbers(2 * n_max)

    for n, expected in enumerate(OEIS_DATA, start=1):
        got = a(n, b)
        if got != expected:
            print(f"FAIL: a({n}) = {got}, OEIS DATA says {expected}")
            return 1
    print(f"OK: a(1..{len(OEIS_DATA)}) match the OEIS DATA line")

    checked = []
    for p in range(5, args.limit + 1):
        q = 2 * p - 1
        if not (is_prime(p) and is_prime(q)):
            continue
        bern = b[2 * p]
        num, den = bern.numerator, bern.denominator
        ok = (den == 6 and num % p == 0 and num % q != 0
              and a(p, b) == 12 * q and is_prime(a(p, b) // 12))
        if not ok:
            print(f"FAIL at p = {p}: B_2p = {bern}, a(p) = {a(p, b)}")
            return 1
        checked.append(p)
    print(f"OK: a(p) = 12(2p-1) and a(p)/12 prime for all {len(checked)} primes "
          f"3 < p <= {args.limit} with 2p-1 prime: {checked}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
