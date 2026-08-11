#!/usr/bin/env python3
"""Exact search for A245211 solutions with exactly two prime factors.

For n = p**a * q**b with p < q, every solution has b <= a.  For a
fixed exponent pair, monotonicity leaves a finite interval of possible p.
Once p is fixed, elementary bounds on the tail of the local factor force
the sole possible integer q.  All final comparisons use Python integers.
"""

from __future__ import annotations

import argparse

from sympy import isprime, nextprime


def valuation_two(value: int) -> int:
    return (value & -value).bit_length() - 1


def local_factor(exponent: int, prime: int) -> tuple[int, int]:
    """Return (sum_{j=0}^a (j+1)p^j, p^a)."""
    power = 1
    total = 1
    for j in range(1, exponent + 1):
        power *= prime
        total += (j + 1) * power
    return total, power


def search(max_exponent: int) -> tuple[list[tuple[int, int, int, int]], int, int]:
    solutions: list[tuple[int, int, int, int]] = []
    exponent_pairs = 0
    prime_candidates = 0

    for a in range(1, max_exponent + 1):
        for b in range(1, a + 1):
            divisor_count = (a + 1) * (b + 1)

            # Exact 2-adic necessary condition from the report.
            lhs_v2 = valuation_two((a + 1) * (a + 2) // 2)
            lhs_v2 += valuation_two((b + 1) * (b + 2) // 2)
            if lhs_v2 != valuation_two(divisor_count + 1):
                continue
            exponent_pairs += 1

            # Necessary inequality p > a(b+1).
            p = int(nextprime(a * (b + 1)))
            while True:
                ba, p_to_a = local_factor(a, p)
                bb_at_p, p_to_b = local_factor(b, p)

                # Since q>p and the normalized local factors decrease,
                # equality is impossible from this p onward once this fails.
                if ba * bb_at_p <= (divisor_count + 1) * p_to_a * p_to_b:
                    break

                # Required tail y_b(q) = G/ba.  The inequalities
                # b/q <= y_b(q) < b/(q-1) put q in an interval of length 1.
                gap_numerator = (divisor_count + 1) * p_to_a - (b + 1) * ba
                if gap_numerator > 0:
                    q = (b * ba + gap_numerator - 1) // gap_numerator
                    if q > p and isprime(q):
                        prime_candidates += 1
                        bb, q_to_b = local_factor(b, q)
                        if ba * bb == (divisor_count + 1) * p_to_a * q_to_b:
                            solutions.append((p, a, q, b))

                p = int(nextprime(p))

    return solutions, exponent_pairs, prime_candidates


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("max_exponent", nargs="?", type=int, default=200)
    args = parser.parse_args()
    solutions, pairs, candidates = search(args.max_exponent)
    print(f"max_exponent {args.max_exponent}")
    print(f"admissible_exponent_pairs {pairs}")
    print(f"prime_candidates_exactly_checked {candidates}")
    print("solutions", *solutions)


if __name__ == "__main__":
    main()
