#!/usr/bin/env python3
"""Flip SAT variable polarities so the solver's all-true phase is a seed coloring."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path


def read_assignment(path: Path, maximum: int, colors: int,
                    missing_color: int) -> list[int]:
    assignment = [missing_color] * (maximum + 1)
    seen: set[int] = set()
    rows = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.partition("#")[0].strip()
        if line:
            rows.append([int(token) for token in line.split()])
    if len(rows) != colors:
        raise ValueError(f"expected {colors} rows, found {len(rows)}")
    for color, row in enumerate(rows):
        for value in row:
            if not 1 <= value <= maximum or value in seen:
                raise ValueError(f"invalid or duplicate seed value: {value}")
            assignment[value] = color
            seen.add(value)
    return assignment


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cnf", type=Path)
    parser.add_argument("seed", type=Path)
    parser.add_argument("--maximum", type=int, default=537)
    parser.add_argument("--colors", type=int, default=6)
    parser.add_argument("--missing-color", type=int, default=5,
                        help="1-based phase color for values absent from seed")
    args = parser.parse_args()
    if not 1 <= args.missing_color <= args.colors:
        parser.error("missing color is out of range")
    phase = read_assignment(args.seed, args.maximum, args.colors,
                            args.missing_color - 1)

    with args.cnf.open(encoding="ascii") as source:
        for raw in source:
            if raw.startswith(("c", "p")) or not raw.strip():
                sys.stdout.write(raw)
                continue
            literals = [int(token) for token in raw.split()]
            transformed: list[int] = []
            for literal in literals:
                if literal == 0:
                    transformed.append(0)
                    continue
                variable = abs(literal)
                value = (variable - 1) // args.colors + 1
                color = (variable - 1) % args.colors
                desired_true = phase[value] == color
                transformed.append(literal if desired_true else -literal)
            sys.stdout.write(" ".join(map(str, transformed)) + "\n")


if __name__ == "__main__":
    main()
