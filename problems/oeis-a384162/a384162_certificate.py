#!/usr/bin/env python3
"""Independently certify the n=2 counterexample to OEIS A384162.

Only the Python standard library is used.  The two sides are each computed in
two different ways:

* A384162(2): direct marked-word enumeration and generating-function recurrence;
* A342168(1): Chebyshev recurrence and the OEIS finite binomial sum.
"""

from fractions import Fraction
from itertools import product
from math import comb


def has_one_mark_per_run(word: tuple[int, ...], mark_mask: int) -> bool:
    """Return whether every maximal constant run has exactly one marked site."""
    start = 0
    while start < len(word):
        stop = start + 1
        while stop < len(word) and word[stop] == word[start]:
            stop += 1
        if sum((mark_mask >> i) & 1 for i in range(start, stop)) != 1:
            return False
        start = stop
    return True


def marked_word_count(n: int) -> int:
    """Brute-force the defining marked words over an n-letter alphabet."""
    return sum(
        has_one_mark_per_run(word, mark_mask)
        for word in product(range(n), repeat=n)
        for mark_mask in range(1 << n)
    )


def a384162_from_gf(n: int) -> int:
    """Extract [x^n] n*x/(1-(n+1)*x+x^2) by its coefficient recurrence."""
    if n == 0:
        return 0
    previous, current = 0, n
    for _ in range(2, n + 1):
        previous, current = current, (n + 1) * current - previous
    return current


def chebyshev_u(degree: int, x: Fraction) -> Fraction:
    """Evaluate U_degree(x) from U_0=1, U_1=2x."""
    if degree == 0:
        return Fraction(1)
    previous, current = Fraction(1), 2 * x
    for _ in range(2, degree + 1):
        previous, current = current, 2 * x * current - previous
    return current


def a342168_from_chebyshev(n: int) -> int:
    value = chebyshev_u(n, Fraction(n + 3, 2))
    assert value.denominator == 1
    return value.numerator


def a342168_from_binomial_sum(n: int) -> int:
    return sum(
        (n + 1) ** (n - k) * comb(2 * n + 1 - k, k)
        for k in range(n + 1)
    )


def main() -> None:
    left_enumeration = marked_word_count(2)
    left_gf = a384162_from_gf(2)
    a342168_chebyshev = a342168_from_chebyshev(1)
    a342168_sum = a342168_from_binomial_sum(1)
    right = 2 * a342168_chebyshev

    assert left_enumeration == left_gf == 6
    assert a342168_chebyshev == a342168_sum == 4
    assert right == 8
    assert left_enumeration != right

    print("A384162(2): marked-word enumeration = GF recurrence = 6")
    print("A342168(1): Chebyshev recurrence = binomial sum = 4")
    print("counterexample certified: 6 != 2 * 4 = 8")


if __name__ == "__main__":
    main()
