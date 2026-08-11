#!/usr/bin/env python3
"""Independent finite counterexample check for OEIS A319197.

The script uses two Fibonacci implementations to evaluate the exact n=7,
m=1 instance of the entry's displayed I(n;m), using its published terms
a(3),...,a(7).  It verifies exact division and the counterexample quotient 769.
"""

from __future__ import annotations

from functools import lru_cache
from math import prod


SOURCE_FACTORS_THROUGH_7 = (1, 9, 161, 51841, 6989569)
EXPECTED_INDEX = 96
EXPECTED_DENOMINATOR = 67205083036226688
EXPECTED_FIBONACCI = 51680708854858323072
EXPECTED_QUOTIENT = 769


def fib_iter(n: int) -> int:
    """Linear iterative Fibonacci implementation."""
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


@lru_cache(maxsize=None)
def fib_pair(n: int) -> tuple[int, int]:
    """Independent fast-doubling implementation returning (F_n, F_(n+1))."""
    if n == 0:
        return 0, 1
    a, b = fib_pair(n // 2)
    c = a * (2 * b - a)
    d = a * a + b * b
    return (d, c + d) if n % 2 else (c, d)


def fib_fast(n: int) -> int:
    return fib_pair(n)[0]


def main() -> None:
    n, m = 7, 1
    index = (1 << (n - 2)) * 3 * m
    denominator = (1 << n) * prod(SOURCE_FACTORS_THROUGH_7)
    value_iter = fib_iter(index)
    value_fast = fib_fast(index)
    quotient, remainder = divmod(value_iter, denominator)

    assert index == EXPECTED_INDEX
    assert denominator == EXPECTED_DENOMINATOR
    assert value_iter == value_fast == EXPECTED_FIBONACCI
    assert remainder == 0
    assert quotient == EXPECTED_QUOTIENT
    assert quotient != 1

    print(
        "A319197 counterexample verified independently: "
        f"I(7;1)={quotient}, not 1"
    )


if __name__ == "__main__":
    main()
