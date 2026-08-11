#!/usr/bin/env python3
"""Decode a SAT solver model for encode_cnf.py into six set rows."""

from __future__ import annotations

import argparse
from pathlib import Path

from flip_phase import read_assignment


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("model", type=Path)
    parser.add_argument("--maximum", type=int, default=537)
    parser.add_argument("--colors", type=int, default=6)
    parser.add_argument("--phase-seed", type=Path)
    parser.add_argument("--missing-color", type=int, default=5)
    args = parser.parse_args()

    positives: set[int] = set()
    status = None
    for line in args.model.read_text(encoding="utf-8").splitlines():
        if line.startswith("s "):
            status = line[2:].strip()
        if line.startswith("v "):
            positives.update(int(token) for token in line[2:].split()
                             if int(token) > 0)
    if status is not None and status != "SATISFIABLE":
        raise SystemExit(f"solver did not report SAT: {status}")

    phase = None
    if args.phase_seed is not None:
        phase = read_assignment(args.phase_seed, args.maximum, args.colors,
                                args.missing_color - 1)

    rows: list[list[int]] = [[] for _ in range(args.colors)]
    for value in range(1, args.maximum + 1):
        selected = []
        for color in range(args.colors):
            encoded_true = ((value - 1) * args.colors + color + 1) in positives
            original_true = encoded_true
            if phase is not None and phase[value] != color:
                original_true = not encoded_true
            if original_true:
                selected.append(color)
        if len(selected) != 1:
            raise SystemExit(f"value {value} has {len(selected)} true colors")
        rows[selected[0]].append(value)
    for row in rows:
        print(" ".join(map(str, row)))


if __name__ == "__main__":
    main()
