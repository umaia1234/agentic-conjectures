#!/usr/bin/env python3
"""Exact bounded-support exclusion using cached Legendre-symbol bitsets.

For a candidate union U contained in the first K primes, the already proved
cardinality bound |U| >= 60 means that U is obtained from those K primes by
removing at most K-60 entries.  The reciprocal-sum condition prunes this list
exactly with Fraction arithmetic.

The expensive local condition is checked without multiplying the primes in U.
For every possible numerator p_j we cache the bitset of odd denominators p_i
for which (p_j/p_i)=-1.  Removing p_j toggles precisely those bits.  This is
algebraically identical to recomputing every Legendre symbol from scratch.
"""

from __future__ import annotations

import argparse
import json
import random
import time
from math import prod

try:
    from .enumerate_59 import legendre, primes_through, removal_sets, sum_inverse
except ImportError:
    from enumerate_59 import legendre, primes_through, removal_sets, sum_inverse


MINIMUM_UNION_SIZE = 60


def local_bitset_tables(primes: list[int]) -> tuple[int, list[int], int]:
    """Return (bad_for_full_set, removal_toggles, odd_denominator_mask)."""
    odd_mask = sum(1 << i for i, prime in enumerate(primes) if prime != 2)
    toggles = [0] * len(primes)
    for numerator_index, numerator in enumerate(primes):
        bits = 0
        for denominator_index, denominator in enumerate(primes):
            if denominator == 2 or denominator_index == numerator_index:
                continue
            if legendre(numerator, denominator) == -1:
                bits |= 1 << denominator_index
        toggles[numerator_index] = bits

    # For denominator p_i, XOR parity over all other numerators is negative
    # exactly when bit i is set here.
    bad_full = 0
    for bits in toggles:
        bad_full ^= bits
    return bad_full, toggles, odd_mask


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--prime-count",
        type=int,
        default=67,
        help="use the first K primes as the proposed support (default: 67)",
    )
    parser.add_argument(
        "--audit-samples",
        type=int,
        default=0,
        help="compare cached and direct local symbols on this many seeded subsets",
    )
    args = parser.parse_args()
    count = args.prime_count
    if not MINIMUM_UNION_SIZE <= count <= 100:
        parser.error("require 60 <= prime-count <= 100")

    # The 100th prime is 541, so this fixed sieve is ample for the CLI range.
    all_primes = primes_through(600)
    full = all_primes[:count]
    next_prime = all_primes[count]
    excess = sum_inverse(full) - 2
    if excess < 0:
        raise AssertionError("the full support itself has reciprocal sum below 2")
    # Any feasible candidate must contain 2, allowing the specialised mod-8
    # formula below and excluding the denominator 2 from Legendre symbols.
    assert sum_inverse(full[1:]) < 2

    index = {prime: i for i, prime in enumerate(full)}
    bad_full, toggles, odd_mask = local_bitset_tables(full)
    full_sum_mod8 = sum(full[1:]) % 8
    full_product_mod8 = 1
    for prime in full[1:]:
        full_product_mod8 = full_product_mod8 * prime % 8
    full_u = sum(prime % 4 == 3 for prime in full[1:])
    full_v = sum(prime % 8 in (3, 5) for prime in full[1:])

    if args.audit_samples:
        generator = random.Random(307_000 + count)
        for _ in range(args.audit_samples):
            removed = generator.sample(
                full[1:], generator.randrange(count - MINIMUM_UNION_SIZE + 1)
            )
            removed_bits = 0
            local_bad = bad_full
            for prime in removed:
                bit = index[prime]
                removed_bits |= 1 << bit
                local_bad ^= toggles[bit]
            cached = not (local_bad & odd_mask & ~removed_bits)
            values = [prime for prime in full if prime not in set(removed)]
            product = prod(values)
            direct = all(
                legendre(product // prime, prime) == 1
                for prime in values
                if prime != 2
            )
            assert cached == direct
        print(
            f"audit: {args.audit_samples} cached/direct local-symbol checks passed",
            flush=True,
        )

    totals = {
        "reciprocal_sum_at_least_2_and_size_at_least_60": 0,
        "union_mod8": 0,
        "aggregate_reciprocity_after_mod8": 0,
        "all_local_legendre_after_cheap_filters": 0,
    }
    rows: list[dict[str, int]] = []
    started = time.monotonic()

    for removed_count in range(count - MINIMUM_UNION_SIZE + 1):
        removals = (
            [()]
            if removed_count == 0
            else removal_sets(full, removed_count, excess)
        )
        row = {key: 0 for key in totals}
        for removed in removals:
            # Since deleting 2 leaves reciprocal sum below 2, it cannot occur
            # in a tuple emitted by the exact removal-mass filter.
            assert 2 not in removed
            row["reciprocal_sum_at_least_2_and_size_at_least_60"] += 1
            totals["reciprocal_sum_at_least_2_and_size_at_least_60"] += 1

            removed_sum = 0
            removed_product = 1
            removed_u = 0
            removed_v = 0
            removed_bits = 0
            local_bad = bad_full
            for prime in removed:
                removed_sum += prime
                removed_product = removed_product * prime % 8
                removed_u += prime % 4 == 3
                removed_v += prime % 8 in (3, 5)
                bit = index[prime]
                removed_bits |= 1 << bit
                local_bad ^= toggles[bit]

            s = (full_sum_mod8 - removed_sum) % 8
            # Odd residues are their own inverses modulo 8, so division by
            # the removed product is multiplication by the same residue.
            t = full_product_mod8 * removed_product % 8
            if (2 * s - (5 * t - 1)) % 8:
                continue
            row["union_mod8"] += 1
            totals["union_mod8"] += 1

            u = full_u - removed_u
            v = full_v - removed_v
            if (v + u * (u - 1) // 2) % 2:
                continue
            row["aggregate_reciprocity_after_mod8"] += 1
            totals["aggregate_reciprocity_after_mod8"] += 1

            # Conditions belonging to removed denominators are ignored.
            if local_bad & odd_mask & ~removed_bits:
                continue
            row["all_local_legendre_after_cheap_filters"] += 1
            totals["all_local_legendre_after_cheap_filters"] += 1

        rows.append({"removed": removed_count, **row})
        print(
            f"removed={removed_count} candidates="
            f"{row['reciprocal_sum_at_least_2_and_size_at_least_60']} "
            f"local_survivors={row['all_local_legendre_after_cheap_filters']} "
            f"elapsed={time.monotonic() - started:.3f}s",
            flush=True,
        )

    result = {
        "prime_count": count,
        "largest_supported_prime": full[-1],
        "next_possible_largest_prime": next_prime,
        "result": (
            "no candidate union passes every necessary condition"
            if totals["all_local_legendre_after_cheap_filters"] == 0
            else "at least one candidate survives the necessary conditions"
        ),
        "totals": totals,
        "by_removed": rows,
        "elapsed_seconds": time.monotonic() - started,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
