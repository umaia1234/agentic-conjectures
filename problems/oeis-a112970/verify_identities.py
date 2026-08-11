#!/usr/bin/env python3
"""Finite independent audit of the OEIS A112970 identities.

The universal result is the Lean proof.  This script deliberately evaluates
the integer-index recurrence directly (rather than mirroring the guarded
natural-number implementation used by Lean) and checks a configurable finite
range as a transcription guard.
"""

from __future__ import annotations

import argparse
from functools import cache


@cache
def a(index: int) -> int:
    """Evaluate A112970 from its recurrence, including negative indices."""

    if index < 0:
        return 0
    if index in (0, 1):
        return 1
    if index % 2:
        return a(index // 2)
    half = index // 2
    return a(half) + a(half - 2)


def a033638(index: int) -> int:
    """Return the quarter-square formula recorded by OEIS A033638."""

    return index * index // 4 + 1


def verify(max_exponent: int) -> None:
    if max_exponent < 0:
        raise ValueError("max_exponent must be nonnegative")

    for exponent in range(max_exponent + 1):
        power = 1 << exponent
        power_value = a(power)
        shifted_value = a((1 << (exponent + 1)) + 1)
        expected = a033638(exponent)
        if not power_value == shifted_value == expected:
            raise AssertionError(
                "first identity failed at "
                f"n={exponent}: {power_value}, {shifted_value}, {expected}"
            )

        minus_one_value = a(power - 1)
        triple_value = a(3 * power - 1)
        if not minus_one_value == triple_value == 1:
            raise AssertionError(
                "second identity failed at "
                f"n={exponent}: {minus_one_value}, {triple_value}"
            )

    print(
        "PASS: independently evaluated A112970 and verified both conjectured "
        f"chains for n=0..{max_exponent}"
    )
    print(f"memoized recurrence states: {a.cache_info().currsize}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-exponent", type=int, default=64)
    args = parser.parse_args()
    verify(args.max_exponent)


if __name__ == "__main__":
    main()
