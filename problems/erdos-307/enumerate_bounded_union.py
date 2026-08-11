#!/usr/bin/env python3
"""Exclude every candidate union supported on the first 66 primes."""

from __future__ import annotations

import json

try:
    from .enumerate_59 import (
        aggregate_reciprocity,
        first_local_failure,
        primes_through,
        removal_sets,
        sum_inverse,
        union_mod8,
    )
except ImportError:
    from enumerate_59 import (
        aggregate_reciprocity,
        first_local_failure,
        primes_through,
        removal_sets,
        sum_inverse,
        union_mod8,
    )


def main() -> None:
    primes = primes_through(500)
    full = primes[:66]
    assert full[-1] == 317 and primes[66] == 331
    excess = sum_inverse(full) - 2
    assert excess > 0
    # Even the largest reciprocal sum supported here after deleting 2 is <2.
    assert sum_inverse(full[1:]) < 2

    totals = {
        "reciprocal_sum_at_least_2_and_size_at_least_60": 0,
        "union_mod8": 0,
        "aggregate_reciprocity_after_mod8": 0,
        "all_local_legendre_after_cheap_filters": 0,
    }
    by_removed: list[dict[str, int]] = []
    for count in range(0, 7):
        removals = [()] if count == 0 else removal_sets(full, count, excess)
        row = {key: 0 for key in totals}
        for removed in removals:
            removed_set = set(removed)
            values = tuple(prime for prime in full if prime not in removed_set)
            assert len(values) >= 60 and 2 in values
            # removal_sets already enforces this exact inequality; checking the
            # at-most-six removed reciprocals is a cheap independent assertion.
            assert sum_inverse(removed) <= excess
            row["reciprocal_sum_at_least_2_and_size_at_least_60"] += 1
            totals["reciprocal_sum_at_least_2_and_size_at_least_60"] += 1
            if not union_mod8(values):
                continue
            row["union_mod8"] += 1
            totals["union_mod8"] += 1
            if not aggregate_reciprocity(values):
                continue
            row["aggregate_reciprocity_after_mod8"] += 1
            totals["aggregate_reciprocity_after_mod8"] += 1
            if first_local_failure(values) is not None:
                continue
            row["all_local_legendre_after_cheap_filters"] += 1
            totals["all_local_legendre_after_cheap_filters"] += 1
        by_removed.append({"removed": count, **row})

    assert totals["all_local_legendre_after_cheap_filters"] == 0
    print(json.dumps({
        "support": "all primes at most 317 (the first 66 primes)",
        "next_possible_largest_prime": 331,
        "result": "no candidate union supported on primes at most 317",
        "totals": totals,
        "by_removed": by_removed,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
