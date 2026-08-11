#!/usr/bin/env python3
"""Search the OEIS A297707 previous-prime-gap question.

Requires gmpy2 and sympy.  Candidate gaps are pre-sieved, then the remaining
3,000--4,000 digit integers are tested with the Baillie--PSW probable-prime
test.  A reported endpoint still needs a primality certificate before it is
treated as a proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time

import gmpy2
from sympy import factorint, primerange


def a297707(n: int) -> gmpy2.mpz:
    value = gmpy2.mpz(1)
    for k in range(1, n):
        for term in range(n, 0, -k):
            value *= term
    return value


def first_probable_prime_below(
    value: gmpy2.mpz, max_gap: int, sieve_bound: int
) -> tuple[int, gmpy2.mpz, int]:
    alive = bytearray(b"\1") * (max_gap + 1)
    alive[0] = 0
    alive[2::2] = b"\0" * (max_gap // 2)

    for q in primerange(3, sieve_bound + 1):
        residue = int(value % q)
        if residue == 0:
            residue = q
        if residue <= max_gap:
            alive[residue::q] = b"\0" * (((max_gap - residue) // q) + 1)

    tested = 0
    for gap in range(1, max_gap + 1, 2):
        if alive[gap]:
            tested += 1
            candidate = value - gap
            if gmpy2.is_bpsw_prp(candidate):
                return gap, candidate, tested
    raise RuntimeError(f"no probable prime found within gap {max_gap}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    parser.add_argument("--max-gap", type=int, default=200_000)
    parser.add_argument("--sieve-bound", type=int, default=5_000_000)
    args = parser.parse_args()

    sys.set_int_max_str_digits(1_000_000)
    started = time.time()
    value = a297707(args.n)
    gap, previous_prime_prp, tested = first_probable_prime_below(
        value, args.max_gap, args.sieve_bound
    )
    value_decimal = str(value)
    prime_decimal = str(previous_prime_prp)
    result = {
        "n": args.n,
        "digits": len(value_decimal),
        "gap": gap,
        "gap_factorization": {str(k): v for k, v in factorint(gap).items()},
        "gap_is_composite": gap > 1 and not bool(gmpy2.is_prime(gap)),
        "prp_tests_after_sieve": tested,
        "a_sha256": hashlib.sha256(value_decimal.encode()).hexdigest(),
        "previous_prime_prp_sha256": hashlib.sha256(prime_decimal.encode()).hexdigest(),
        "seconds": round(time.time() - started, 3),
    }
    print(json.dumps(result, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
