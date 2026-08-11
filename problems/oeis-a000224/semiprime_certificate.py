#!/usr/bin/env python3
"""Finite certificate for the squarefree-semiprime part of OEIS A000224.

The accompanying proof reduces a hypothetical n = p*q, 3 <= p < q odd
prime, to p <= 61.  Put a=(p+1)/2, b=(q+1)/2, and R=a*b.  Since R must
divide n^2-1, necessarily b divides p^2-1 = 4*a*(a-1).  This script
exhausts exactly those remaining divisors using only the Python standard
library.  It retains candidates for which R divides n^2-1, and verifies
that R-1 divides none of them.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path


EXPECTED = [
    (3, 7, 8, 6),
    (5, 7, 12, 3),
    (5, 11, 18, 15),
    (5, 47, 72, 57),
    (7, 11, 24, 17),
    (7, 23, 48, 23),
    (11, 19, 60, 20),
    (11, 23, 72, 37),
    (11, 59, 180, 13),
    (13, 83, 294, 151),
    (19, 29, 150, 87),
    (19, 71, 360, 29),
    (19, 179, 900, 266),
    (23, 43, 264, 23),
    (23, 263, 1584, 938),
    (29, 41, 315, 92),
    (29, 419, 3150, 2786),
    (31, 479, 3840, 3674),
    (37, 683, 6498, 825),
    (41, 839, 8820, 1875),
    (47, 367, 4416, 1150),
    (47, 1103, 13248, 4155),
]


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    for d in range(3, isqrt(n) + 1, 2):
        if n % d == 0:
            return False
    return True


def divisors(n: int) -> list[int]:
    small: list[int] = []
    large: list[int] = []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            small.append(d)
            if d * d != n:
                large.append(n // d)
    return small + large[::-1]


def run() -> dict:
    records: list[tuple[int, int, int, int]] = []
    divisor_candidates = 0

    for a in range(2, 32):
        p = 2 * a - 1
        if not is_prime(p):
            continue
        for b in divisors(4 * a * (a - 1)):
            if b <= a:
                continue
            q = 2 * b - 1
            if not is_prime(q):
                continue
            divisor_candidates += 1
            n = p * q
            r = a * b
            if (n * n - 1) % r:
                continue
            remainder = (n * n - 1) % (r - 1)
            if remainder == 0:
                raise AssertionError(f"counterexample found: n={n}, p={p}, q={q}")
            records.append((p, q, r, remainder))

    if records != EXPECTED:
        raise AssertionError("candidate table differs from the audited table")

    source_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return {
        "claim": (
            "no n=p*q with distinct odd primes p<q satisfies "
            "R(n)(R(n)-1) | n^2-1"
        ),
        "status": "VERIFIED FINITE REDUCTION",
        "reduction": (
            "the proof gives p<=61; b=(q+1)/2 must divide p^2-1"
        ),
        "prime_divisor_candidates_after_b_condition": divisor_candidates,
        "candidates_also_satisfying_R_divides_n2_minus_1": len(records),
        "columns": ["p", "q", "R", "(n^2-1) mod (R-1)"],
        "records": records,
        "all_final_remainders_nonzero": True,
        "script_sha256": source_hash,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run()
    rendered = json.dumps(result, indent=2, sort_keys=True)
    print(rendered)
    if args.output:
        args.output.write_text(rendered + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

