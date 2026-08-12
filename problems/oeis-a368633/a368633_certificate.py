#!/usr/bin/env python3
"""Exact finite certificate for the parity claim on OEIS A368633.

The coefficient sequence is constructed in two ways:

1. directly from the signed Cauchy products in
       A(x) = 1 + 2*x*A(x)^2 - x*A(-x)^2;
2. from the simplified exact recurrence derived from that equation.

The two constructions are compared through n=600.  The script also checks
the 25 terms in the canonical OEIS JSON data field (revision 26) and compares
coefficient parity with both the Catalan closed form and the claimed
power-of-two support.  Only Python standard-library integer arithmetic is
used.
"""

from math import comb


LIMIT = 600

# The complete `data` field returned by the canonical OEIS JSON endpoint for
# A368633 revision 26, checked 2026-08-12.  It contains a(0),...,a(24).
OEIS_JSON_DATA = (
    "1,1,6,13,114,290,2892,7901,84090,239222,2648244,7732914,"
    "87894324,261371940,3027588120,9125058525,107215635402,"
    "326501869166,3879094785060,11910103389734,142766337272988,"
    "441265565242268,5328172865489448,16559430499708018,"
    "201171901999797924"
)


def coefficients_from_functional_equation(limit: int) -> list[int]:
    """Construct coefficients using the two signed products literally."""
    coefficients = [1]
    for n in range(1, limit + 1):
        degree = n - 1
        a_square = 0
        a_at_minus_x_square = 0
        for left in range(degree + 1):
            right = degree - left
            product = coefficients[left] * coefficients[right]
            a_square += product
            left_sign = -1 if left % 2 else 1
            right_sign = -1 if right % 2 else 1
            a_at_minus_x_square += left_sign * right_sign * product
        coefficients.append(2 * a_square - a_at_minus_x_square)
    return coefficients


def coefficients_from_exact_recurrence(limit: int) -> list[int]:
    """Use a_n=(2-(-1)^(n-1))*sum_{i=0}^{n-1} a_i*a_{n-1-i}."""
    coefficients = [1]
    for n in range(1, limit + 1):
        convolution = sum(
            coefficients[left] * coefficients[n - 1 - left]
            for left in range(n)
        )
        multiplier = 1 if n % 2 else 3
        coefficients.append(multiplier * convolution)
    return coefficients


def is_power_of_two(value: int) -> bool:
    return value > 0 and value & (value - 1) == 0


def catalan(n: int) -> int:
    """Independent exact closed form C_n = binomial(2*n,n)/(n+1)."""
    return comb(2 * n, n) // (n + 1)


def main() -> None:
    assert LIMIT >= 600
    published_terms = tuple(int(term) for term in OEIS_JSON_DATA.split(","))
    assert len(published_terms) == 25

    direct = coefficients_from_functional_equation(LIMIT)
    recurrence = coefficients_from_exact_recurrence(LIMIT)

    # Independent implementations of the defining equation and its simplified
    # coefficient recurrence agree, and the exact published prefix matches.
    assert direct == recurrence
    assert tuple(direct[: len(published_terms)]) == published_terms

    odd_indices = []
    for n, coefficient in enumerate(direct):
        coefficient_is_odd = coefficient % 2 == 1
        catalan_is_odd = catalan(n) % 2 == 1
        claimed = is_power_of_two(n + 1)
        assert coefficient_is_odd == catalan_is_odd == claimed
        if coefficient_is_odd:
            odd_indices.append(n)

    expected_odd_indices = [(1 << exponent) - 1 for exponent in range(10)]
    assert odd_indices == expected_odd_indices

    print("OEIS JSON prefix matched: 25 terms (n=0..24)")
    print("functional equation and exact recurrence matched: n=0..600")
    print("parity matched Catalan parity and the conjecture: n=0..600")
    print("odd indices through 600:", odd_indices)


if __name__ == "__main__":
    main()
