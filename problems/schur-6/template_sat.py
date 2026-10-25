#!/usr/bin/env python3
"""Structured ("template") SAT encodings for sum-free 6-partitions of [1, n].

Subcommands:

  cnf     Emit DIMACS for a template class.
  decode  Turn a solver model into the six-row format read by verify.py.

Template options (all optional, combinable):

  --palindromic   c(x) = c(n+1-x).  One variable block per folded position
                  p = f(x) = min(x, n+1-x), p = 1..ceil(n/2).  A Schur triple
                  x+y=z then becomes a clause over {f(x), f(y), f(z)}.
  --frame Q D     The frame of Chen--Zhu--Long (arXiv:2610.31362, Def. 3),
                  stated for general n with N = n+1, on f(x):
                    f < j      => c != j          (j = 1..4)
                    f < D or Q-D < f < Q => c != 5
                    f in {D, N-2Q}       => c = 5
                    f < Q      => c != 6
                    f = Q or f > N-2Q    => c = 6     (solid middle)
                  Requires --palindromic.
  --frame6 Q      Only the color-6 part of the frame: f < Q => c != 6 and
                  f = Q or f > N-2Q => c = 6 (min C6 = Q, solid middle).
                  Requires --palindromic.
  --no-middle     Drop the solid-middle part of either frame (keep f = Q => 6).
  --fix FILE K    Fix c(x) for 1 <= x <= K to the colors of a six-row file
                  (colors renumbered by least elements first).
  --order [M]     Colors 1..M (default all) numbered by least elements: if
                  position p has color k, 1 < k <= M, then some earlier
                  position has color k-1.  Sound when the other constraints
                  treat colors 1..M symmetrically (e.g. M = 5 with --frame6).
  --amo           Add pairwise at-most-one clauses (only at-least-one
                  clauses are emitted otherwise; both are sound for UNSAT).

Colors are 1..K in this file (K = --colors, default 6); variable(p, k) =
K*(p-1) + k.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

K = 6


def var(p: int, k: int) -> int:
    return K * (p - 1) + k


def read_rows(path: Path) -> list[list[int]]:
    rows = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.partition("#")[0].strip()
        if line:
            rows.append([int(t) for t in line.split()])
    return rows


def frame_color_rules(n: int, q: int, d: int, middle: bool):
    """Return (forced, forbidden) maps on folded positions for frame g(Q, D)."""
    big_n = n + 1
    positions = (n + 1) // 2
    forced: dict[int, int] = {}
    forbidden: dict[int, set[int]] = {p: set() for p in range(1, positions + 1)}
    for p in range(1, positions + 1):
        for j in (1, 2, 3, 4):
            if p < j:
                forbidden[p].add(j)
        if p < d or q - d < p < q:
            forbidden[p].add(5)
        if p in (d, big_n - 2 * q):
            forced[p] = 5
        if p < q:
            forbidden[p].add(6)
        if p == q or (middle and p > big_n - 2 * q):
            if p in forced and forced[p] != 6:
                raise SystemExit(f"frame forces two colors at f(x) = {p}")
            forced[p] = 6
    return forced, forbidden


def build(args: argparse.Namespace) -> tuple[int, list[tuple[int, ...]]]:
    n = args.maximum
    pal = args.palindromic
    positions = (n + 1) // 2 if pal else n

    def fold(x: int) -> int:
        return min(x, n + 1 - x) if pal else x

    clauses: set[tuple[int, ...]] = set()
    for p in range(1, positions + 1):
        clauses.add(tuple(var(p, k) for k in range(1, K + 1)))
        if args.amo:
            for a in range(1, K + 1):
                for b in range(a + 1, K + 1):
                    clauses.add((-var(p, a), -var(p, b)))
    for x in range(1, n + 1):
        for y in range(x, n - x + 1):
            cell = sorted({fold(x), fold(y), fold(x + y)})
            for k in range(1, K + 1):
                clauses.add(tuple(-var(p, k) for p in cell))
    if args.frame:
        if not pal:
            raise SystemExit("--frame requires --palindromic")
        q, d = args.frame
        forced, forbidden = frame_color_rules(n, q, d, not args.no_middle)
        for p, k in forced.items():
            clauses.add((var(p, k),))
        for p, ks in forbidden.items():
            for k in ks:
                clauses.add((-var(p, k),))
    if args.frame6:
        if not pal or args.frame:
            raise SystemExit("--frame6 requires --palindromic and excludes --frame")
        q = args.frame6
        for p in range(1, positions + 1):
            if p < q:
                clauses.add((-var(p, 6),))
            elif p == q or (not args.no_middle and p > n + 1 - 2 * q):
                clauses.add((var(p, 6),))
    if args.fix:
        path, length = Path(args.fix[0]), int(args.fix[1])
        rows = sorted(read_rows(path), key=min)
        color = {x: i + 1 for i, row in enumerate(rows) for x in row}
        fixed: dict[int, int] = {}
        for x in range(1, length + 1):
            if fixed.setdefault(fold(x), color[x]) != color[x]:
                raise SystemExit(f"--fix gives two colors to folded position {fold(x)}")
            clauses.add((var(fold(x), color[x]),))
    if args.order:
        for p in range(1, positions + 1):
            for k in range(2, args.order + 1):
                clauses.add((-var(p, k),) + tuple(var(r, k - 1) for r in range(1, p)))
    return K * positions, sorted(clauses, key=lambda c: (len(c), c))


def decode(args: argparse.Namespace) -> None:
    n = args.maximum
    pal = args.palindromic
    true = set()
    for line in Path(args.model).read_text(encoding="utf-8").splitlines():
        if line.startswith("v "):
            true.update(int(t) for t in line.split()[1:] if int(t) > 0)
    rows: list[list[int]] = [[] for _ in range(K)]
    for x in range(1, n + 1):
        p = min(x, n + 1 - x) if pal else x
        colors = [k for k in range(1, K + 1) if var(p, k) in true]
        if not colors:
            raise SystemExit(f"no color for {x}")
        # Any true color is sound: every Schur clause is per color.
        rows[colors[0] - 1].append(x)
    for row in rows:
        print(" ".join(map(str, row)))


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("cnf", "decode"):
        s = sub.add_parser(name)
        s.add_argument("--maximum", type=int, required=True)
        s.add_argument("--palindromic", action="store_true")
        s.add_argument("--colors", type=int, default=6,
                       help="number of colors (only 6 with --frame)")
        if name == "cnf":
            s.add_argument("--frame", type=int, nargs=2, metavar=("Q", "D"))
            s.add_argument("--frame6", type=int, metavar="Q")
            s.add_argument("--no-middle", action="store_true")
            s.add_argument("--fix", nargs=2, metavar=("FILE", "K"))
            s.add_argument("--order", type=int, nargs="?", const=-1, metavar="M")
            s.add_argument("--amo", action="store_true")
        else:
            s.add_argument("model")
    args = parser.parse_args()
    global K
    K = args.colors
    if args.command == "cnf" and (args.frame or args.frame6) and K != 6:
        parser.error("frames are defined for six colors")
    if args.command == "cnf" and args.order == -1:
        args.order = K
    if args.command == "decode":
        decode(args)
        return
    variables, clauses = build(args)
    out = sys.stdout
    out.write(f"p cnf {variables} {len(clauses)}\n")
    for clause in clauses:
        out.write(" ".join(map(str, clause)) + " 0\n")


if __name__ == "__main__":
    main()
