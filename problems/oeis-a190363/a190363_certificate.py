#!/usr/bin/env python3
"""Exact integer-arithmetic certificate for the A190363 recurrence counterexample."""

from math import isqrt


def beatty_part(n: int) -> int:
    """Return floor(n*sqrt(5)/2), using integer arithmetic only."""
    assert n >= 0
    return isqrt(5 * n * n) // 2


def a(n: int) -> int:
    """OEIS A190363: 2*n + floor(n*sqrt(5)/2) + floor(n/4)."""
    return 2 * n + beatty_part(n) + n // 4


def defect(n: int) -> int:
    """Zero iff the conjectured order-21 recurrence holds at base index n."""
    return a(n + 21) - a(n + 17) - a(n + 4) + a(n)


def square_interval(n: int) -> tuple[int, int, int, int]:
    """Certificate (q,(2q)^2,5n^2,(2q+2)^2) for q=floor(n*sqrt(5)/2)."""
    q = beatty_part(n)
    return q, (2 * q) ** 2, 5 * n * n, (2 * q + 2) ** 2


def shift17_margin(k: int) -> int:
    """A positive value certifies {k*sqrt(5)/2} < 1-delta.

    Here delta = 17*sqrt(5)/2 - 19.  Since k*sqrt(5)/2 is
    irrational, q below is its ceiling.  The desired strict inequality

        q - k*sqrt(5)/2 > delta

    is equivalent, after moving terms and squaring positive quantities, to

        4*(q+19)^2 > 5*(k+17)^2.
    """
    q = beatty_part(k) + 1
    return 4 * (q + 19) ** 2 - 5 * (k + 17) ** 2


def pell_pairs(count: int):
    """Yield Pell pairs that generate two recurrence failures each.

    Every pair satisfies 4*p^2 - 5*q^2 = 4 and

        0 < p - q*sqrt(5)/2 < 17*sqrt(5)/2 - 19.

    Consequently the recurrence defects at q-4 and q are +1 and -1.
    The recurrence multiplies the positive error by 9-4*sqrt(5), which
    lies strictly between zero and one, so it gives infinitely many pairs.
    """
    p, q = 161, 144
    for _ in range(count):
        yield p, q
        p, q = 9 * p + 10 * q, 8 * p + 9 * q


def main() -> None:
    # This is the exhaustive minimality certificate: every operation is on integers.
    assert all(defect(n) == 0 for n in range(1, 140))
    assert defect(140) == 1

    # More compact certificate for minimality.  For 1 <= n <= 139, both
    # k=n and k=n+4 are at most 143, so adding 17 never causes a floor carry.
    margins = [(shift17_margin(k), k) for k in range(1, 144)]
    assert min(margins) == (4, 127)
    assert shift17_margin(144) == -5

    first_failure = next(n for n in range(1, 10_000) if defect(n) != 0)
    print("first failure:", first_failure)
    print("defect at 140:", defect(140))
    print("a(140), a(144), a(157), a(161):", *(a(n) for n in (140, 144, 157, 161)))
    print("RHS a(157)+a(144)-a(140):", a(157) + a(144) - a(140))
    print("minimum shift-17 margin for k=1..143:", min(margins))
    print("shift-17 margin at k=144:", shift17_margin(144))
    print("square certificates (q, (2q)^2, 5n^2, (2q+2)^2):")
    for n in (140, 144, 157, 161):
        cert = square_interval(n)
        assert cert[1] <= cert[2] < cert[3]
        print(n, cert)

    pell_bases: list[int] = []
    previous_q = 0
    for p, q in pell_pairs(8):
        assert q > previous_q
        previous_q = q
        assert 4 * p * p - 5 * q * q == 4
        # p > q*sqrt(5)/2, while p+19 < (q+17)*sqrt(5)/2.
        assert 4 * p * p > 5 * q * q
        assert 4 * (p + 19) ** 2 < 5 * (q + 17) ** 2
        assert defect(q - 4) == 1
        assert defect(q) == -1
        pell_bases.extend((q - 4, q))
    print("first Pell-generated failure bases:", pell_bases[:8])


if __name__ == "__main__":
    main()
