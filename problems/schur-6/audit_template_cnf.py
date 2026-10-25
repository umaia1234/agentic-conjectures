#!/usr/bin/env python3
"""Soundness audit for a template CNF (independent of template_sat.py).

An UNSAT certificate for a CNF says nothing about Schur partitions unless
every clause of the CNF holds for every coloring in the claimed class.  This
script re-derives the class from its definition and accepts the CNF only if
each clause is one of:

  * at-least-one:  (v(p,1) | ... | v(p,6)) for a single position p;
  * at-most-one:   (-v(p,a) | -v(p,b)), a != b;
  * Schur clause:  (-v(p,k) for p in S) for one color k, where S is the set
                   of positions of some Schur triple x + y = z <= n (after
                   folding x -> min(x, n+1-x) for palindromic classes);
  * frame unit:    v(p,k) or -v(p,k) as dictated by the frame of
                   Chen--Zhu--Long (arXiv:2610.31362, Definition 3) with
                   parameters (Q, D), stated for N = n + 1, or by its
                   color-6 part alone (--frame6 Q: min C6 = Q and every x
                   with N-2Q < f(x) lies in C6), or by --fix FILE K (c(x)
                   equals the color of x in FILE for x <= K, colors of FILE
                   numbered by least elements);
  * order clause:  (-v(p,k) | v(1,k-1) | ... | v(p-1,k-1)), 1 < k <= M, i.e.
                   colors 1..M numbered by least elements.  This is a
                   normalization, accepted only when nothing else in the
                   class distinguishes colors 1..M (no frame: M <= 6;
                   --frame6: M <= 5; never with --frame or --fix).

Only soundness is needed: if the CNF is UNSAT then so is the stronger set of
all class constraints, hence the class is empty.  Variable v(p,k) is
6*(p-1) + k with colors 1..6.  Exit 0 iff every clause is accounted for.
"""

from __future__ import annotations

import argparse
import hashlib
import sys


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("cnf")
    ap.add_argument("--maximum", type=int, required=True)
    ap.add_argument("--palindromic", action="store_true")
    ap.add_argument("--frame", type=int, nargs=2, metavar=("Q", "D"))
    ap.add_argument("--frame6", type=int, metavar="Q")
    ap.add_argument("--no-middle", action="store_true")
    ap.add_argument("--fix", nargs=2, metavar=("FILE", "K"))
    ap.add_argument("--order", type=int, default=0, metavar="M")
    ap.add_argument("--sha256", help="also require this SHA-256 of the CNF file")
    args = ap.parse_args()
    if args.frame and args.frame6:
        print("choose at most one frame")
        return 1
    if args.order and (args.frame or args.fix or
                       args.order > (5 if args.frame6 else 6)):
        print("order normalization not justified for this class")
        return 1

    n = args.maximum
    colors = 6
    width = (n + 1) // 2 if args.palindromic else n

    def position(x: int) -> int:
        if args.palindromic and x > n + 1 - x:
            return n + 1 - x
        return x

    # Position sets of all Schur triples (x <= y, x + y <= n).
    schur_sets = set()
    for z in range(2, n + 1):
        for x in range(1, z // 2 + 1):
            schur_sets.add(frozenset((position(x), position(z - x), position(z))))

    # Frame: allowed colors per position, written directly from Definition 3.
    allowed = {p: set(range(1, colors + 1)) for p in range(1, width + 1)}
    if args.frame:
        if not args.palindromic:
            print("frame audit is only defined for palindromic classes")
            return 1
        q, d = args.frame
        big_n = n + 1
        for p in allowed:
            for j in range(1, 5):
                if p < j:
                    allowed[p].discard(j)
            if p < d or (q - d < p < q):
                allowed[p].discard(5)
            if p < q:
                allowed[p].discard(6)
            must = set()
            if p == d or p == big_n - 2 * q:
                must.add(5)
            if p == q or (not args.no_middle and p > big_n - 2 * q):
                must.add(6)
            if must:
                allowed[p] &= must
                if len(must) > 1:
                    allowed[p] = set()

    if args.frame6:
        if not args.palindromic:
            print("frame audit is only defined for palindromic classes")
            return 1
        q = args.frame6
        for p in allowed:
            if p < q:
                allowed[p].discard(6)
            if p == q or (not args.no_middle and p > n + 1 - 2 * q):
                allowed[p] &= {6}

    if args.fix:
        rows = []
        with open(args.fix[0], encoding="utf-8") as handle:
            for raw in handle:
                values = [int(t) for t in raw.split("#")[0].split()]
                if values:
                    rows.append(values)
        rows.sort(key=min)
        reference = {}
        for color, row in enumerate(rows, start=1):
            for x in row:
                reference[x] = color
        for x in range(1, int(args.fix[1]) + 1):
            allowed[position(x)] &= {reference[x]}

    if args.sha256:
        with open(args.cnf, "rb") as handle:
            digest = hashlib.sha256(handle.read()).hexdigest()
        if digest != args.sha256:
            print(f"sha256 mismatch: {digest}")
            return 1

    with open(args.cnf, encoding="ascii") as handle:
        header = handle.readline().split()
        if header[:2] != ["p", "cnf"] or int(header[2]) != colors * width:
            print(f"bad header {header}, expected {colors * width} variables")
            return 1
        declared = int(header[3])
        body = handle.read().split()

    clauses, current = [], []
    for token in body:
        literal = int(token)
        if literal == 0:
            clauses.append(current)
            current = []
        else:
            current.append(literal)
    if current or len(clauses) != declared:
        print(f"clause count mismatch: header {declared}, parsed {len(clauses)}")
        return 1

    def split(literal: int) -> tuple[int, int]:
        v = abs(literal)
        if not 1 <= v <= colors * width:
            raise ValueError(f"variable {v} out of range")
        return (v - 1) // colors + 1, (v - 1) % colors + 1

    kinds = {"at-least-one": 0, "at-most-one": 0, "schur": 0, "frame-unit": 0,
             "order": 0}
    for clause in clauses:
        cells = [split(lit) for lit in clause]
        positions = {p for p, _ in cells}
        hues = {k for _, k in cells}
        if all(lit > 0 for lit in clause):
            if len(clause) == colors and len(positions) == 1 and hues == set(
                    range(1, colors + 1)):
                kinds["at-least-one"] += 1
                continue
            if len(clause) == 1 and len(allowed[cells[0][0]]) == 1 and \
                    cells[0][1] in allowed[cells[0][0]]:
                kinds["frame-unit"] += 1
                continue
        elif sum(lit < 0 for lit in clause) == 1 and len(clause) > 1:
            p, k = split(min(clause))
            rest = sorted(split(lit) for lit in clause if lit > 0)
            if 1 < k <= args.order and rest == [(r, k - 1) for r in range(1, p)]:
                kinds["order"] += 1
                continue
        if all(lit < 0 for lit in clause):
            if len(clause) == 1 and 1 < cells[0][1] <= args.order and cells[0][0] == 1:
                kinds["order"] += 1
                continue
            if len(clause) == 2 and len(positions) == 1 and len(hues) == 2:
                kinds["at-most-one"] += 1
                continue
            if len(hues) == 1 and len(positions) == len(clause) and \
                    frozenset(positions) in schur_sets:
                kinds["schur"] += 1
                continue
            if len(clause) == 1 and cells[0][1] not in allowed[cells[0][0]]:
                kinds["frame-unit"] += 1
                continue
        print(f"UNJUSTIFIED clause: {clause}")
        return 1
    print(f"audit ok: n={n} palindromic={args.palindromic} frame={args.frame} "
          f"frame6={args.frame6} no_middle={args.no_middle} order={args.order} "
          f"fix={args.fix} "
          f"clauses={len(clauses)} {kinds}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
