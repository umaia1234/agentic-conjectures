#!/usr/bin/env python3
"""Reconstruct Fredricksen--Sweet's symmetric partition of [1, 536]."""

from __future__ import annotations

import argparse
from pathlib import Path


CENTER = 537
EXCEPTION = frozenset((179, 358))


def read_half(path: Path) -> list[list[int]]:
    rows: list[list[int]] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.partition("#")[0].strip()
        if line:
            rows.append([int(token) for token in line.split()])
    if len(rows) != 6:
        raise ValueError(f"expected 6 color rows, found {len(rows)}")
    return rows


def reconstruct(rows: list[list[int]]) -> list[list[int]]:
    owner: dict[int, int] = {}
    for color, row in enumerate(rows, start=1):
        for value in row:
            if not 1 <= value < CENTER:
                raise ValueError(f"out-of-range listed value: {value}")
            if value in owner:
                raise ValueError(f"listed twice: {value}")
            owner[value] = color

    # The paper lists one representative from each symmetric pair.  Install a
    # reflected value only after all explicit entries have been installed, so
    # that the documented exceptional pair can carry two different colors.
    explicit = dict(owner)
    for value, color in explicit.items():
        reflected = CENTER - value
        previous = owner.get(reflected)
        if previous is None:
            owner[reflected] = color
        elif previous != color and frozenset((value, reflected)) != EXCEPTION:
            raise ValueError(
                f"unexpected asymmetric pair {value}, {reflected}: "
                f"colors {color}, {previous}"
            )

    expected = set(range(1, CENTER))
    actual = set(owner)
    if actual != expected:
        raise ValueError(
            f"not a partition: missing={sorted(expected-actual)}, "
            f"extra={sorted(actual-expected)}"
        )
    return [sorted(value for value, c in owner.items() if c == color)
            for color in range(1, 7)]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("half_file", type=Path)
    parser.add_argument(
        "--format", choices=("sets", "assignment"), default="sets",
        help="six set rows, or one 'integer color' pair per line",
    )
    args = parser.parse_args()
    colors = reconstruct(read_half(args.half_file))
    if args.format == "sets":
        for color in colors:
            print(" ".join(map(str, color)))
    else:
        assignment = {value: c for c, row in enumerate(colors, start=1)
                      for value in row}
        for value in sorted(assignment):
            print(value, assignment[value])


if __name__ == "__main__":
    main()
