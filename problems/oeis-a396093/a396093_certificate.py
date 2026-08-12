#!/usr/bin/env python3
"""Independent exact certificate for both OEIS A396093 parity conjectures.

Only the Python standard library is used.  The certificate:

* composes B(x) = x/(1-x)^2 three times using exact polynomial arithmetic;
* recovers the published rational generating function and order-eight recurrence;
* checks the published terms and an independent double-sum formula;
* proves the infinite parity pattern by a polynomial identity over F_2; and
* checks the resulting residue rule on 501 recurrence-generated coefficients.

Polynomials are represented by low-to-high coefficient tuples.
"""

from math import comb


Polynomial = tuple[int, ...]


def trim(p: Polynomial) -> Polynomial:
    values = list(p)
    while len(values) > 1 and values[-1] == 0:
        values.pop()
    return tuple(values)


def add(p: Polynomial, q: Polynomial) -> Polynomial:
    size = max(len(p), len(q))
    return trim(
        tuple(
            (p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0)
            for i in range(size)
        )
    )


def neg(p: Polynomial) -> Polynomial:
    return tuple(-coefficient for coefficient in p)


def sub(p: Polynomial, q: Polynomial) -> Polynomial:
    return add(p, neg(q))


def mul(p: Polynomial, q: Polynomial) -> Polynomial:
    values = [0] * (len(p) + len(q) - 1)
    for i, left in enumerate(p):
        for j, right in enumerate(q):
            values[i + j] += left * right
    return trim(tuple(values))


def square(p: Polynomial) -> Polynomial:
    return mul(p, p)


def mod_two(p: Polynomial) -> Polynomial:
    return trim(tuple(coefficient % 2 for coefficient in p))


def iterate_b(numerator: Polynomial, denominator: Polynomial) -> tuple[Polynomial, Polynomial]:
    """Return B(numerator/denominator) for B(x)=x/(1-x)^2."""
    return mul(numerator, denominator), square(sub(denominator, numerator))


def series_coefficients(
    numerator: Polynomial, denominator: Polynomial, count: int
) -> list[int]:
    """Expand numerator/denominator exactly through x^(count-1)."""
    assert denominator[0] == 1
    coefficients: list[int] = []
    for n in range(count):
        value = numerator[n] if n < len(numerator) else 0
        value -= sum(
            denominator[j] * coefficients[n - j]
            for j in range(1, min(n, len(denominator) - 1) + 1)
        )
        coefficients.append(value)
    return coefficients


def manyama_double_sum(n: int) -> int:
    """Independent OEIS formula for a(n), valid for n >= 1."""
    return sum(
        j * comb(n + i - 1, 2 * i - 1) * comb(i + j - 1, 2 * j - 1)
        for i in range(1, n + 1)
        for j in range(1, i + 1)
    )


def main() -> None:
    x: Polynomial = (0, 1)
    numerator: Polynomial = x
    denominator: Polynomial = (1,)
    for _ in range(3):
        numerator, denominator = iterate_b(numerator, denominator)

    expected_numerator = mul(mul(x, square((1, -1))), square((1, -3, 1)))
    inner_denominator: Polynomial = (1, -7, 13, -7, 1)
    expected_denominator = square(inner_denominator)
    assert numerator == expected_numerator
    assert denominator == expected_denominator

    assert denominator == (1, -14, 75, -196, 269, -196, 75, -14, 1)
    recurrence = tuple(-coefficient for coefficient in denominator[1:])
    assert recurrence == (14, -75, 196, -269, 196, -75, 14, -1)

    published = [
        0,
        1,
        6,
        33,
        174,
        892,
        4480,
        22149,
        108144,
        522685,
        2505112,
        11921919,
        56396508,
        265403751,
        1243376476,
        5802001140,
        26979276974,
        125062092939,
        578101278342,
        2665535043771,
        12262237690928,
        56292277012925,
        257928385148946,
        1179746378224461,
        5387375927372810,
        24565077404044268,
        111855801487635036,
    ]
    coefficients = series_coefficients(numerator, denominator, 501)
    assert coefficients[: len(published)] == published
    assert all(coefficients[n] == manyama_double_sum(n) for n in range(1, 31))
    assert all(
        coefficients[n]
        == sum(recurrence[j - 1] * coefficients[n - j] for j in range(1, 9))
        for n in range(8, len(coefficients))
    )

    # In F_2[[x]], this cross-multiplied polynomial identity proves
    # A(x) = (x+x^3+x^7+x^9)/(1+x^10).  Both denominators have constant
    # coefficient one, so their formal power-series inverses exist.
    one_plus_x10: Polynomial = (1,) + (0,) * 9 + (1,)
    x_times_pattern: Polynomial = mul(x, mul((1, 0, 1), (1, 0, 0, 0, 0, 0, 1)))
    assert mod_two(mul(numerator, one_plus_x10)) == mod_two(
        mul(denominator, x_times_pattern)
    )

    odd_residues = {1, 3, 7, 9}
    assert all(
        (coefficient % 2 == 1) == (n % 10 in odd_residues)
        for n, coefficient in enumerate(coefficients)
    )
    assert all(coefficients[2 * n] % 2 == 0 for n in range(1, 251))
    assert all(
        (coefficients[2 * n - 1] % 2 == 0) == (n % 5 == 3)
        for n in range(1, 251)
    )

    print("A396093 certificate OK")
    print("  exact identity: A(x) = B(B(B(x))), B(x)=x/(1-x)^2")
    print("  published rational function and order-8 recurrence recovered")
    print("  27 published terms and independent double sum through n=30 checked")
    print("  F_2 identity: A(x)=(x+x^3+x^7+x^9)/(1+x^10)")
    print("  both parity conjectures follow; 501 coefficients regression-checked")


if __name__ == "__main__":
    main()
