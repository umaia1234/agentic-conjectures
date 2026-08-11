#!/usr/bin/env python3
"""Exact finite exclusion of a 59-prime union for Erdős problem #307."""

from __future__ import annotations

import json
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from typing import Iterator

try:  # Support both direct execution and namespace-package imports.
    from .exact_checker import legendre, product
except ImportError:
    from exact_checker import legendre, product


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for prime in range(2, int(limit**0.5) + 1):
        if sieve[prime]:
            sieve[prime * prime:limit + 1:prime] = b"\x00" * (
                (limit - prime * prime) // prime + 1)
    return [value for value in range(2, limit + 1) if sieve[value]]


@lru_cache(maxsize=None)
def inverse(value: int) -> Fraction:
    return Fraction(1, value)


def sum_inverse(values: tuple[int, ...] | list[int]) -> Fraction:
    return sum((inverse(value) for value in values), Fraction())


def removal_sets(base: list[int], count: int,
                 limit: Fraction) -> Iterator[tuple[int, ...]]:
    """All count-subsets R of base with sum(1/r) <= limit, exactly."""
    minimum_tail = [Fraction()]
    for left in range(1, count + 1):
        minimum_tail.append(sum_inverse(base[-left:]))

    def recurse(start: int, left: int, total: Fraction,
                chosen: tuple[int, ...]) -> Iterator[tuple[int, ...]]:
        if left == 0:
            yield chosen
            return
        for index in range(start, len(base) - left + 1):
            # The last left-1 base primes give the smallest possible
            # reciprocal contribution of any completion after this choice.
            lower_bound = total + inverse(base[index]) + minimum_tail[left - 1]
            if lower_bound <= limit:
                yield from recurse(index + 1, left - 1,
                                   total + inverse(base[index]),
                                   chosen + (base[index],))

    yield from recurse(0, count, Fraction(), ())


def addition_sets(tail: list[int], count: int,
                  target: Fraction) -> Iterator[tuple[int, ...]]:
    """All count-subsets A of tail with sum(1/a) >= target, exactly."""
    def recurse(start: int, left: int, total: Fraction,
                chosen: tuple[int, ...]) -> Iterator[tuple[int, ...]]:
        if left == 0:
            if total >= target:
                yield chosen
            return
        if start + left > len(tail):
            return
        maximum = total + sum_inverse(tail[start:start + left])
        if maximum < target:
            return
        for index in range(start, len(tail) - left + 1):
            if left == 1:
                maximum_after_choice = total + inverse(tail[index])
            else:
                maximum_after_choice = (total + inverse(tail[index]) +
                                        sum_inverse(tail[index + 1:index + left]))
            # Later choices only have smaller reciprocals, so break is sound.
            if maximum_after_choice < target:
                break
            yield from recurse(index + 1, left - 1,
                               total + inverse(tail[index]),
                               chosen + (tail[index],))

    yield from recurse(0, count, Fraction(), ())


def union_mod8(values: tuple[int, ...]) -> bool:
    assert 2 in values
    odd = [value for value in values if value != 2]
    s = sum(odd) % 8
    t = product(odd) % 8
    return (2 * s - (5 * t - 1)) % 8 == 0


def aggregate_reciprocity(values: tuple[int, ...]) -> bool:
    odd = [value for value in values if value != 2]
    u = sum(value % 4 == 3 for value in odd)
    v = sum(value % 8 in (3, 5) for value in odd)
    return (v + u * (u - 1) // 2) % 2 == 0


def first_local_failure(values: tuple[int, ...]) -> int | None:
    n = product(values)
    for prime in values:
        if prime != 2 and legendre(n // prime, prime) != 1:
            return prime
    return None


def fraction_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def main() -> None:
    primes = primes_through(1000)
    base = primes[:59]
    outside = primes[59:]
    assert base[-1] == 277 and outside[0] == 281
    h58 = sum_inverse(base[:58])
    h59 = sum_inverse(base)
    maximum_without_two = sum_inverse(primes[1:60])
    assert h58 < 2 < h59
    assert maximum_without_two < 2
    delta = h59 - 2

    # Replacing k base primes loses at least L_k, obtained by removing the k
    # largest base primes and adding the k smallest outside primes.  L_k is
    # strictly increasing; L_6 > delta makes every k >= 6 impossible.
    losses = {
        count: sum_inverse(base[-count:]) - sum_inverse(outside[:count])
        for count in range(1, 7)
    }
    assert losses[6] > delta
    assert all(losses[count + 1] > losses[count] for count in range(1, 6))

    cumulative = {
        "reciprocal_sum_at_least_2": 0,
        "union_mod8": 0,
        "aggregate_reciprocity": 0,
        "all_local_legendre": 0,
    }
    by_replacements: list[dict[str, int]] = []
    failures: Counter[int] = Counter()

    def check(values: tuple[int, ...], row: dict[str, int]) -> None:
        assert len(values) == 59 and len(set(values)) == 59
        assert sum_inverse(values) >= 2
        row["reciprocal_sum_at_least_2"] += 1
        cumulative["reciprocal_sum_at_least_2"] += 1
        # Check the strongest local condition on every candidate, independently
        # of the cheaper filters below.  This avoids relying computationally on
        # the mod-8 or aggregate derivations to obtain the final zero count.
        failed_at = first_local_failure(values)
        if failed_at is None:
            row["all_local_legendre"] += 1
            cumulative["all_local_legendre"] += 1
        else:
            failures[failed_at] += 1
        if not union_mod8(values):
            return
        row["union_mod8"] += 1
        cumulative["union_mod8"] += 1
        if not aggregate_reciprocity(values):
            return
        row["aggregate_reciprocity"] += 1
        cumulative["aggregate_reciprocity"] += 1

    row0 = {key: 0 for key in cumulative}
    check(tuple(base), row0)
    by_replacements.append({"replacements": 0, **row0})

    for count in range(1, 6):
        # A candidate's removed reciprocal mass is at least that of the last
        # count base primes.  Even if its first count-1 additions are the
        # smallest possible outside primes, the largest added prime q must
        # satisfy 1/q >= positive_remainder.  This yields a rigorous finite
        # upper bound for every added prime.
        minimum_target = sum_inverse(base[-count:]) - delta
        positive_remainder = minimum_target - sum_inverse(outside[:count - 1])
        assert positive_remainder > 0
        largest_added_bound = positive_remainder.denominator // positive_remainder.numerator
        assert largest_added_bound < 1000
        eligible_tail = [prime for prime in outside if prime <= largest_added_bound]
        assert eligible_tail and eligible_tail[-1] < 1000

        maximum_added_mass = sum_inverse(outside[:count])
        removals = list(removal_sets(base, count, delta + maximum_added_mass))
        row = {key: 0 for key in cumulative}
        for removed in removals:
            target = sum_inverse(removed) - delta
            for added in addition_sets(eligible_tail, count, target):
                values = tuple(sorted((set(base) - set(removed)) | set(added)))
                check(values, row)
        by_replacements.append({
            "replacements": count,
            "eligible_added_primes": len(eligible_tail),
            "eligible_removal_sets": len(removals),
            **row,
        })

    assert cumulative == {
        "reciprocal_sum_at_least_2": 49961,
        "union_mod8": 12493,
        "aggregate_reciprocity": 6149,
        "all_local_legendre": 0,
    }
    result = {
        "result": "no 59-prime union passes the necessary local Legendre conditions",
        "first_58_prime_reciprocal_sum": fraction_text(h58),
        "first_59_prime_reciprocal_sum": fraction_text(h59),
        "maximum_59_prime_sum_without_2": fraction_text(maximum_without_two),
        "delta_above_2": fraction_text(delta),
        "minimum_loss_for_6_replacements": fraction_text(losses[6]),
        "counts": cumulative,
        "by_replacements": by_replacements,
        "first_local_failure_histogram": dict(sorted(failures.items())),
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
