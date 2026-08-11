#!/usr/bin/env python3
"""Deterministic randomized and composite-toy tests of the proof identities."""

from __future__ import annotations

import json
import math
import random

try:  # Support both direct execution and namespace-package imports.
    from .enumerate_59 import primes_through
    from .exact_checker import (
        generalized_pair_report,
        numerator_a,
        pairwise_coprime,
        product,
        reciprocal_sum,
        reciprocity_identity,
    )
except ImportError:
    from enumerate_59 import primes_through
    from exact_checker import (
        generalized_pair_report,
        numerator_a,
        pairwise_coprime,
        product,
        reciprocal_sum,
        reciprocity_identity,
    )


SEED = 307_2026_08_11


def generalized_mod8_check(p_values: list[int], q_values: list[int]) -> bool:
    """The mod-8 calculation only needs odd self-inverses, not primality."""
    union = p_values + q_values
    odd = [value for value in union if value != 2]
    t = product(odd) % 8
    s = sum(odd) % 8
    if 2 not in union:
        union_ok = (s - 2 * t) % 8 == 0
        partition_ok = ((sum(p_values) - t) % 8 == 0 and
                        (sum(q_values) - t) % 8 == 0)
    else:
        containing = p_values if 2 in p_values else q_values
        opposite = q_values if 2 in p_values else p_values
        union_ok = (1 + 2 * s - 5 * t) % 8 == 0
        partition_ok = ((sum(opposite) - 2 * t) % 8 == 0 and
                        (1 + 2 * sum(value for value in containing
                                   if value != 2) - t) % 8 == 0)
    return union_ok and partition_ok


def toy_solution_check(p_values: list[int], q_values: list[int]) -> dict[str, object]:
    report = generalized_pair_report(p_values, q_values)
    assert report["P_pairwise_coprime"] and report["Q_pairwise_coprime"]
    assert report["cross_pairwise_coprime"]
    assert report["forcing_identities"] and report["product_equals_one"]
    union = p_values + q_values
    assert numerator_a(union) == product(p_values) ** 2 + product(q_values) ** 2
    assert generalized_mod8_check(p_values, q_values)

    # The cross congruence gives an explicit square root of M(U)/r modulo r.
    n = product(union)
    for side, opposite in ((p_values, q_values), (q_values, p_values)):
        root = product(opposite)
        for denominator in side:
            if denominator != 1:
                assert (n // denominator - root * root) % denominator == 0
    return report


def random_composite_set(generator: random.Random, include_two: bool) -> list[int]:
    composites = [value for value in range(9, 500, 2)
                  if any(value % divisor == 0
                         for divisor in range(3, math.isqrt(value) + 1, 2))]
    generator.shuffle(composites)
    chosen = [2] if include_two else []
    target = generator.randint(2, 8)
    for value in composites:
        if all(math.gcd(value, old) == 1 for old in chosen):
            chosen.append(value)
            if len(chosen) >= target + int(include_two):
                break
    assert pairwise_coprime(chosen)
    return chosen


def main() -> None:
    generator = random.Random(SEED)
    primes = primes_through(200)

    prime_reciprocity_trials = 2000
    with_two = 0
    for _ in range(prime_reciprocity_trials):
        size = generator.randint(1, 14)
        values = generator.sample(primes, size)
        if generator.randrange(2) == 0 and 2 not in values:
            values[0] = 2
        values = sorted(set(values))
        with_two += int(2 in values)
        result = reciprocity_identity(values)
        assert result["matches"]
        m = product(values)
        a = numerator_a(values)
        assert math.gcd(a, m) == 1

    composite_jacobi_trials = 1000
    composite_with_two = 0
    for trial in range(composite_jacobi_trials):
        values = random_composite_set(generator, trial % 2 == 0)
        composite_with_two += int(2 in values)
        result = reciprocity_identity(values, use_jacobi=True)
        assert result["matches"]

    forcing_equivalence_trials = 2000
    for _ in range(forcing_equivalence_trials):
        p_values = generator.sample(primes[:25], generator.randint(1, 8))
        q_values = generator.sample(primes[:25], generator.randint(1, 8))
        equation = reciprocal_sum(p_values) * reciprocal_sum(q_values) == 1
        forcing = (numerator_a(p_values) == product(q_values) and
                   numerator_a(q_values) == product(p_values))
        assert equation == forcing

    toys = [
        toy_solution_check([1, 5], [2, 3]),
        toy_solution_check([1, 41], [2, 3, 7]),
        # 1805=5*19^2 is genuinely composite; 2,3,7,43 are pairwise
        # coprime and their reciprocal sum is 1805/1806.
        toy_solution_check([1, 1805], [2, 3, 7, 43]),
    ]

    # Every unit modulo 24 is self-inverse, which is the sole extra input in
    # the mod-24 strengthening when 3 is absent.
    units24 = [value for value in range(24) if math.gcd(value, 24) == 1]
    assert all(value * value % 24 == 1 for value in units24)

    print(json.dumps({
        "seed": SEED,
        "prime_reciprocity_trials": prime_reciprocity_trials,
        "prime_trials_with_2": with_two,
        "composite_jacobi_trials": composite_jacobi_trials,
        "composite_trials_with_2": composite_with_two,
        "forcing_equivalence_trials": forcing_equivalence_trials,
        "toy_solutions": toys,
        "units_mod_24": units24,
        "status": "all exact identity tests passed",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
