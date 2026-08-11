#!/usr/bin/env python3
"""Exact depth-limited repair search starting from a near Schur coloring."""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path


def read_coloring(path: Path, maximum: int, colors: int) -> list[int]:
    assignment = [-1] * (maximum + 1)
    rows = [line for raw in path.read_text(encoding="utf-8").splitlines()
            if (line := raw.partition("#")[0].strip())]
    if len(rows) != colors:
        raise ValueError(f"expected {colors} rows, found {len(rows)}")
    for color, row in enumerate(rows):
        for value in map(int, row.split()):
            if not 1 <= value <= maximum or assignment[value] != -1:
                raise ValueError(f"invalid or duplicate value {value}")
            assignment[value] = color
    missing = [value for value in range(1, maximum + 1)
               if assignment[value] < 0]
    if missing:
        raise ValueError(f"missing values: {missing[:10]}")
    return assignment


class Repair:
    def __init__(self, assignment: list[int], colors: int, seconds: float) -> None:
        self.color = assignment
        self.maximum = len(assignment) - 1
        self.colors = colors
        self.deadline = time.monotonic() + seconds
        self.triples: list[tuple[int, int, int]] = []
        self.incident: list[list[int]] = [[] for _ in assignment]
        for x in range(1, self.maximum + 1):
            for y in range(x, self.maximum - x + 1):
                index = len(self.triples)
                triple = (x, y, x + y)
                self.triples.append(triple)
                for value in dict.fromkeys(triple):
                    self.incident[value].append(index)
        self.bad = {index for index, triple in enumerate(self.triples)
                    if self.is_bad(triple)}
        # Three bits per value give an exact (not probabilistic) state key for
        # up to eight colors, so memoization cannot discard a state by collision.
        if colors > 8:
            raise ValueError("exact packed state supports at most 8 colors")
        self.state_code = 0
        for value in range(1, self.maximum + 1):
            self.state_code |= self.color[value] << (3 * value)
        self.nodes = 0
        self.best_bad = len(self.bad)
        self.timed_out = False

    def is_bad(self, triple: tuple[int, int, int], vertex: int = -1,
               replacement: int = -1) -> bool:
        x, y, z = triple
        cx = replacement if x == vertex else self.color[x]
        cy = replacement if y == vertex else self.color[y]
        cz = replacement if z == vertex else self.color[z]
        return cx == cy == cz

    def apply(self, vertex: int, replacement: int) -> tuple[int, list[tuple[int, bool]]]:
        old = self.color[vertex]
        changed: list[tuple[int, bool]] = []
        for index in self.incident[vertex]:
            before = index in self.bad
            after = self.is_bad(self.triples[index], vertex, replacement)
            if before != after:
                changed.append((index, before))
                if after:
                    self.bad.add(index)
                else:
                    self.bad.remove(index)
        shift = 3 * vertex
        self.state_code = ((self.state_code & ~(7 << shift)) |
                           (replacement << shift))
        self.color[vertex] = replacement
        return old, changed

    def undo(self, vertex: int, old: int,
             changed: list[tuple[int, bool]]) -> None:
        shift = 3 * vertex
        self.state_code = ((self.state_code & ~(7 << shift)) | (old << shift))
        self.color[vertex] = old
        for index, before in changed:
            if before:
                self.bad.add(index)
            else:
                self.bad.remove(index)

    def ordered_moves(self, conflict: int) -> list[tuple[int, int]]:
        candidates: list[tuple[int, int, int]] = []
        for vertex in dict.fromkeys(self.triples[conflict]):
            for replacement in range(self.colors):
                if replacement == self.color[vertex]:
                    continue
                old, changed = self.apply(vertex, replacement)
                candidates.append((len(self.bad), vertex, replacement))
                self.undo(vertex, old, changed)
        candidates.sort()
        return [(vertex, replacement) for _, vertex, replacement in candidates]

    def dfs(self, remaining: int, memo: set[tuple[int, int]],
            path_hashes: set[int]) -> bool:
        self.nodes += 1
        if not self.bad:
            return True
        self.best_bad = min(self.best_bad, len(self.bad))
        if remaining == 0:
            return False
        if (self.nodes & 4095) == 0 and time.monotonic() >= self.deadline:
            self.timed_out = True
            return False
        key = (remaining, self.state_code)
        if key in memo:
            return False
        memo.add(key)

        # Any repaired coloring must recolor at least one distinct vertex in a
        # currently bad triple, so branching on one bad triple is complete.
        conflict = min(self.bad)
        for vertex, replacement in self.ordered_moves(conflict):
            old, changed = self.apply(vertex, replacement)
            if self.state_code not in path_hashes:
                path_hashes.add(self.state_code)
                if self.dfs(remaining - 1, memo, path_hashes):
                    return True
                path_hashes.remove(self.state_code)
            self.undo(vertex, old, changed)
            if self.timed_out:
                return False
        return False

    def search(self, maximum_depth: int) -> bool:
        print(f"initial_violations={len(self.bad)}", file=sys.stderr)
        initial_hash = self.state_code
        for depth in range(maximum_depth + 1):
            before = self.nodes
            memo: set[tuple[int, int]] = set()
            if self.dfs(depth, memo, {initial_hash}):
                print(f"FOUND depth={depth} nodes={self.nodes}", file=sys.stderr)
                return True
            print(f"DEPTH depth={depth} nodes={self.nodes-before} "
                  f"best_violations={self.best_bad}", file=sys.stderr)
            if self.timed_out:
                print(f"TIMEOUT nodes={self.nodes}", file=sys.stderr)
                return False
        print(f"EXHAUSTED depth={maximum_depth} nodes={self.nodes}", file=sys.stderr)
        return False


def write_coloring(path: Path, assignment: list[int], colors: int) -> None:
    rows = [[value for value in range(1, len(assignment))
             if assignment[value] == color] for color in range(colors)]
    path.write_text("".join(" ".join(map(str, row)) + "\n" for row in rows),
                    encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("coloring", type=Path)
    parser.add_argument("--maximum", type=int, default=537)
    parser.add_argument("--colors", type=int, default=6)
    parser.add_argument("--depth", type=int, default=6)
    parser.add_argument("--seconds", type=float, default=60.0)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    repair = Repair(read_coloring(args.coloring, args.maximum, args.colors),
                    args.colors, args.seconds)
    found = repair.search(args.depth)
    if found and args.output is not None:
        write_coloring(args.output, repair.color, args.colors)
    raise SystemExit(0 if found else 2)


if __name__ == "__main__":
    main()
