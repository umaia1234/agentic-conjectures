#!/usr/bin/env python3
"""Executable checks accompanying the proof of the A136433 recurrence."""

from __future__ import annotations


OFFICIAL_TERMS = [
    11,
    12,
    26,
    79,
    81,
    163,
    491,
    492,
    986,
    2959,
    2961,
    5923,
    17771,
    17772,
    35546,
    106639,
    106641,
    213283,
    639851,
    639852,
    1279706,
    3839119,
    3839121,
    7678243,
    23034731,
    23034732,
    46069466,
    138208399,
    138208401,
    276416803,
    829250411,
    829250412,
]


def multiplier(t: int) -> int:
    """c_t in a(t+1)=c_t*a(t)+d_t."""
    return (t - 1) % 3 + 1


def increment(t: int) -> int:
    """d_t in a(t+1)=c_t*a(t)+d_t."""
    return (t - 1) % 2 + 1


def sequence(n_max: int) -> list[int | None]:
    values: list[int | None] = [None] * (n_max + 1)
    values[1] = 11
    for t in range(1, n_max):
        assert values[t] is not None
        values[t + 1] = multiplier(t) * values[t] + increment(t)
    return values


def three_step_affine(t: int) -> tuple[int, int]:
    """Return A,B for a(t+3)=A*a(t)+B."""
    linear, constant = 1, 0
    for step in range(t, t + 3):
        linear, constant = (
            multiplier(step) * linear,
            multiplier(step) * constant + increment(step),
        )
    return linear, constant


def main() -> None:
    values = sequence(10_000)
    assert values[1 : len(OFFICIAL_TERMS) + 1] == OFFICIAL_TERMS

    constants = []
    for t in range(1, 7):
        linear, constant = three_step_affine(t)
        assert linear == 6
        constants.append(constant)
    assert constants == [13, 9, 7, 17, 6, 8]

    for t in range(1, 1000):
        assert three_step_affine(t)[0] == 6
        assert three_step_affine(t + 6) == three_step_affine(t)

    for n in range(10, 10_001):
        assert values[n] == (
            6 * values[n - 3] + values[n - 6] - 6 * values[n - 9]
        )

    print("A136433 certificate: PASS")
    print("  three-step constants by t mod 6:", constants)
    print("  conjectured order-9 recurrence checked through n=10000")


if __name__ == "__main__":
    main()
