#!/usr/bin/env python3
"""Independent checker for a Schur coloring stored as six set rows."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def read_sets(path: Path) -> list[list[int]]:
    rows: list[list[int]] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.partition("#")[0].strip()
        if line:
            rows.append([int(token) for token in line.split()])
    return rows


def verify(rows: list[list[int]], maximum: int, colors: int) -> dict[str, object]:
    duplicates: list[int] = []
    owner: dict[int, int] = {}
    out_of_range: list[int] = []
    for color, row in enumerate(rows, start=1):
        for value in row:
            if not 1 <= value <= maximum:
                out_of_range.append(value)
            if value in owner:
                duplicates.append(value)
            else:
                owner[value] = color

    missing = sorted(set(range(1, maximum + 1)) - set(owner))
    violations: list[dict[str, int]] = []
    for color, row in enumerate(rows, start=1):
        members = set(row)
        for x in sorted(members):
            # x <= y makes every unordered Schur triple appear exactly once.
            for y in range(x, maximum - x + 1):
                if y in members and x + y in members:
                    violations.append({"color": color, "x": x,
                                       "y": y, "z": x + y})
                    if len(violations) >= 20:
                        break
            if len(violations) >= 20:
                break
        if len(violations) >= 20:
            break

    valid = (
        len(rows) == colors
        and not duplicates
        and not out_of_range
        and not missing
        and len(owner) == maximum
        and not violations
    )
    return {
        "valid": valid,
        "maximum": maximum,
        "expected_colors": colors,
        "color_rows": len(rows),
        "color_sizes": [len(row) for row in rows],
        "assigned_distinct": len(owner),
        "missing": missing[:20],
        "duplicates": sorted(set(duplicates))[:20],
        "out_of_range": sorted(set(out_of_range))[:20],
        "violations": violations,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("coloring", type=Path)
    parser.add_argument("--maximum", type=int, required=True)
    parser.add_argument("--colors", type=int, default=6)
    args = parser.parse_args()
    result = verify(read_sets(args.coloring), args.maximum, args.colors)
    print(json.dumps(result, indent=2, sort_keys=True))
    raise SystemExit(0 if result["valid"] else 1)


if __name__ == "__main__":
    main()
