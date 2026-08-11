#!/usr/bin/env python3
"""Independent exact checks for the OEIS A242560 closed form."""

from __future__ import annotations

import argparse
import math


OEIS_TERMS_1_TO_70 = (
    2, 1, 2, 2, 4, 3, 6, 4, 6, 5, 10, 6, 12, 7, 10, 8, 16, 9,
    18, 10, 14, 11, 22, 12, 24, 13, 18, 14, 28, 15, 30, 16, 22, 17,
    28, 18, 36, 19, 26, 20, 40, 21, 42, 22, 30, 23, 46, 24, 42, 25,
    34, 26, 52, 27, 44, 28, 38, 29, 58, 30, 60, 31, 42, 32, 52, 33,
    66, 34, 46, 35,
)


def exact_definition(index: int) -> int:
    """Directly minimize the integer-divisibility definition."""
    factorial = math.factorial(index)
    for candidate in range(1, index + 2):
        if candidate == index:
            continue
        denominator = index - candidate
        numerator = factorial - candidate
        if numerator % denominator == 0:
            return candidate
    raise AssertionError("index + 1 always has denominator -1")


def reduced_definition(index: int) -> int:
    """Minimize an independently reduced test below the singular candidate."""
    for candidate in range(1, index):
        # Here d = index-candidate lies in [1,index], hence d divides index!.
        # Therefore d | (index!-candidate) iff d | candidate.
        if candidate % (index - candidate) == 0:
            return candidate
    return index + 1


def least_prime_factor(index: int) -> int:
    """Return the least prime factor of an integer at least 2."""
    assert index >= 2
    candidate = 2
    while candidate * candidate <= index:
        if index % candidate == 0:
            return candidate
        candidate += 1
    return index


def closed_form(index: int) -> int:
    """Evaluate N - N/spf(N), with the sequence's initial value at N=1."""
    if index == 1:
        return 2
    return index - index // least_prime_factor(index)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=400)
    args = parser.parse_args()
    if args.limit < 70:
        parser.error("--limit must be at least 70")

    observed = tuple(exact_definition(index) for index in range(1, 71))
    mismatches = [
        (index, official, computed)
        for index, (official, computed) in enumerate(
            zip(OEIS_TERMS_1_TO_70, observed), start=1
        )
        if official != computed
    ]
    assert mismatches == [(25, 24, 20)]

    for index in range(1, args.limit + 1):
        exact = exact_definition(index)
        assert exact == reduced_definition(index)
        assert exact == closed_form(index)

    for n in range(1, args.limit // 2 + 1):
        assert exact_definition(2 * n) == n

    print(
        "A242560 certificate passed: official terms 1..70 checked with the "
        "single documented mismatch a(25)=24 (official) vs 20 (definition); "
        f"the definition, reduced test, and closed form agree through index "
        f"{args.limit}; "
        f"a(2n)=n checked for 1<=n<={args.limit // 2}."
    )


if __name__ == "__main__":
    main()
