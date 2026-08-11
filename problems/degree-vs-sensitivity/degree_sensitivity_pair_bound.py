#!/usr/bin/env python3
"""Exact certificates for low-layer bounds in the n=14,d<=5 search.

For a Boolean polynomial f, let q(t) be its average on the Hamming layer of
weight t.  Symmetrization makes q a univariate polynomial of degree at most 5.
The search normalization gives q(0)=0 and q(1)=1, while Booleanity gives
0 <= q(t) <= 1 at every integer layer.
"""

from fractions import Fraction
from math import comb


NODES = (0, 1, 5, 9, 13, 14)
EXPECTED = (
    Fraction(-22, 65),
    Fraction(231, 208),
    Fraction(77, 240),
    Fraction(-11, 80),
    Fraction(21, 208),
    Fraction(-11, 195),
)

TRIPLE_LOWER_NODES = (0, 1, 2, 5, 10, 14)
TRIPLE_LOWER_EXPECTED = (
    Fraction(11, 50),
    Fraction(-77, 78),
    Fraction(77, 48),
    Fraction(77, 450),
    Fraction(-11, 1200),
    Fraction(1, 936),
)
TRIPLE_UPPER_NODES = (0, 1, 2, 9, 13, 14)
TRIPLE_UPPER_EXPECTED = (
    Fraction(110, 273),
    Fraction(-165, 104),
    Fraction(15, 7),
    Fraction(11, 168),
    Fraction(-3, 52),
    Fraction(3, 91),
)

N = 14
DEGREE = 5


def lagrange_coefficients(x: int, nodes: tuple[int, ...]) -> tuple[Fraction, ...]:
    coefficients = []
    for i, node in enumerate(nodes):
        coefficient = Fraction(1)
        for j, other in enumerate(nodes):
            if i != j:
                coefficient *= Fraction(x - other, node - other)
        coefficients.append(coefficient)
    return tuple(coefficients)


def ceil_div(numerator: int, denominator: int) -> int:
    """Exact ceiling division for either sign of the denominator."""
    if denominator == 0:
        raise ZeroDivisionError
    return -((-numerator) // denominator)


def layer_interpolation_coefficients(target: int) -> tuple[int, ...]:
    """Express B_target as an integer linear form in B_0,...,B_5.

    Here B_t is the number of ones on the weight-t layer.  Since
    q(t)=B_t/binom(14,t) is a degree-at-most-five polynomial, ordinary
    Lagrange interpolation gives this identity.  For n=14 all coefficients
    after rescaling by the layer sizes happen to be integral.
    """
    coefficients = tuple(
        Fraction(comb(N, target), comb(N, node))
        * lagrange_coefficients(target, tuple(range(DEGREE + 1)))[node]
        for node in range(DEGREE + 1)
    )
    assert all(value.denominator == 1 for value in coefficients)
    return tuple(int(value) for value in coefficients)


def feasible_layer_profiles() -> list[tuple[int, int, int, int]]:
    """Enumerate every feasible aggregate profile (B2,B3,B4,B5), exactly.

    This uses only 0 <= B_t <= binom(14,t), interpolation, and the two
    previously certified B2/B3 inequalities.  It is a necessary aggregate
    filter, not a construction of a Boolean function.
    """
    later = {
        target: layer_interpolation_coefficients(target)
        for target in range(DEGREE + 1, N + 1)
    }
    profiles: list[tuple[int, int, int, int]] = []
    for b2 in range(84, comb(N, 2) + 1):
        for b3 in range(comb(N, 3) + 1):
            if 300 * b3 - 1925 * b2 < -108801:
                continue
            if 21 * b3 - 180 * b2 > -11375:
                continue
            for b4 in range(comb(N, 4) + 1):
                lower = 0
                upper = comb(N, 5)
                for target, coefficients in later.items():
                    base = (
                        coefficients[1] * N
                        + coefficients[2] * b2
                        + coefficients[3] * b3
                        + coefficients[4] * b4
                    )
                    slope = coefficients[5]
                    cap = comb(N, target)
                    if slope > 0:
                        lower = max(lower, ceil_div(-base, slope))
                        upper = min(upper, (cap - base) // slope)
                    elif slope < 0:
                        lower = max(lower, ceil_div(cap - base, slope))
                        upper = min(upper, (-base) // slope)
                    elif not 0 <= base <= cap:
                        lower, upper = 1, 0
                    if lower > upper:
                        break
                profiles.extend(
                    (b2, b3, b4, b5) for b5 in range(lower, upper + 1)
                )
    return profiles


def main() -> None:
    coefficients = lagrange_coefficients(2, NODES)
    assert coefficients == EXPECTED
    assert sum(coefficients) == 1

    # q(0)=0, q(1)=1.  To minimize q(2), set the remaining positive-coefficient
    # q-values to zero and the remaining negative-coefficient q-values to one.
    lower_bound = coefficients[1] + coefficients[3] + coefficients[5]
    assert lower_bound == Fraction(11, 12)
    pair_count_lower_bound = (comb(14, 2) * lower_bound).__ceil__()
    assert pair_count_lower_bound == 84
    assert comb(14, 2) - pair_count_lower_bound == 7

    print("Lagrange coefficients:", ", ".join(map(str, coefficients)))
    print(f"q(2) >= {lower_bound}")
    print(f"B_2 >= {pair_count_lower_bound}; zero-valued pairs <= 7")

    lower_coefficients = lagrange_coefficients(3, TRIPLE_LOWER_NODES)
    upper_coefficients = lagrange_coefficients(3, TRIPLE_UPPER_NODES)
    assert lower_coefficients == TRIPLE_LOWER_EXPECTED
    assert upper_coefficients == TRIPLE_UPPER_EXPECTED

    # With q(0)=0 and q(1)=1, minimize/maximize the coefficients belonging to
    # unknown layer averages independently within [0,1].  Retain q(2) rather
    # than replacing it by its lower bound, yielding two coupling inequalities.
    # Substitution q(2)=B_2/91 and q(3)=B_3/364, followed by clearing
    # denominators, gives the exact integer forms asserted below.
    lower_constant = Fraction(-77, 78) - Fraction(11, 1200)
    lower_q2 = Fraction(77, 48)
    upper_constant = (
        Fraction(-165, 104) + Fraction(11, 168) + Fraction(3, 91)
    )
    upper_q2 = Fraction(15, 7)
    assert Fraction(109200, 364) == 300
    assert -Fraction(109200 * 77, 48 * 91) == -1925
    assert 109200 * lower_constant == -108801
    assert Fraction(7644, 364) == 21
    assert -Fraction(7644 * 15, 7 * 91) == -180
    assert 7644 * upper_constant == -11375

    print("300*B_3 - 1925*B_2 >= -108801")
    print("21*B_3 - 180*B_2 <= -11375")
    for zero_pairs in range(8):
        b2 = 91 - zero_pairs
        b3_lower = (1925 * b2 - 108801 + 299) // 300
        b3_upper = (-11375 + 180 * b2) // 21
        # Directly check the uncleared rational inequalities as well.
        q2 = Fraction(b2, 91)
        assert Fraction(b3_lower, 364) >= lower_constant + lower_q2 * q2
        assert Fraction(b3_upper, 364) <= upper_constant + upper_q2 * q2
        print(
            f"zero pairs={zero_pairs}: {b3_lower} <= B_3 <= {b3_upper}"
        )

    # Use all fourteen integral layer counts, rather than bounding unknown
    # layer averages independently.  The short interval calculation in
    # feasible_layer_profiles() is exhaustive and dependency-free.
    profiles = feasible_layer_profiles()
    assert len(profiles) == 247
    print("aggregate degree-5 layer profiles:", len(profiles))
    for b2 in range(84, 92):
        b3_values = sorted({profile[1] for profile in profiles if profile[0] == b2})
        assert b3_values == list(range(b3_values[0], b3_values[-1] + 1))
        print(
            f"B_2={b2}: {b3_values[0]} <= B_3 <= {b3_values[-1]} "
            f"({sum(profile[0] == b2 for profile in profiles)} profiles)"
        )


if __name__ == "__main__":
    main()
