#!/usr/bin/env python3
"""Emit a DIMACS SAT encoding of a k-color Schur partition problem."""

from __future__ import annotations

import argparse
import sys
from collections.abc import Iterator


def variable(value: int, color: int, colors: int) -> int:
    """DIMACS variable for 1-based value and 0-based color."""
    return (value - 1) * colors + color + 1


def clauses(maximum: int, colors: int, canonical_colors: bool) -> Iterator[list[int]]:
    # Exactly one color for each integer.
    for value in range(1, maximum + 1):
        yield [variable(value, color, colors) for color in range(colors)]
        for left in range(colors):
            for right in range(left + 1, colors):
                yield [-variable(value, left, colors),
                       -variable(value, right, colors)]

    # No monochromatic x+y=z.  When x=y, the repeated literal is removed,
    # yielding the required two-variable inequality color(x) != color(2x).
    for x in range(1, maximum + 1):
        for y in range(x, maximum - x + 1):
            z = x + y
            for color in range(colors):
                if x == y:
                    yield [-variable(x, color, colors),
                           -variable(z, color, colors)]
                else:
                    yield [-variable(x, color, colors),
                           -variable(y, color, colors),
                           -variable(z, color, colors)]

    if canonical_colors:
        # Break color-permutation symmetry by requiring first occurrences to
        # appear in color order.  If value v has color c>0, some earlier value
        # must already have color c-1.  Every coloring has such a relabeling.
        for value in range(1, maximum + 1):
            for color in range(1, colors):
                yield ([-variable(value, color, colors)] +
                       [variable(previous, color - 1, colors)
                        for previous in range(1, value)])


def write_dimacs(stream: object, maximum: int, colors: int,
                 canonical_colors: bool) -> tuple[int, int]:
    # Materializing the clauses uses little memory here (~440k small lists)
    # and ensures an exact header without a fragile duplicated counting formula.
    encoded = list(clauses(maximum, colors, canonical_colors))
    variables = maximum * colors
    stream.write(f"p cnf {variables} {len(encoded)}\n")
    for clause in encoded:
        stream.write(" ".join(map(str, clause)) + " 0\n")
    return variables, len(encoded)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--maximum", type=int, default=537)
    parser.add_argument("--colors", type=int, default=6)
    parser.add_argument(
        "--no-canonical-colors", action="store_true",
        help="omit sound first-occurrence color-symmetry breaking",
    )
    args = parser.parse_args()
    if args.maximum < 1 or args.colors < 1:
        parser.error("maximum and colors must be positive")
    write_dimacs(sys.stdout, args.maximum, args.colors,
                 not args.no_canonical_colors)


if __name__ == "__main__":
    main()
