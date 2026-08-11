#!/usr/bin/env python3
"""Semantic audit of the 40-variable C20 bicirculant certificate.

Unlike a SAT solver, this script checks what every input clause *means*:

* the first block is exactly the set of triangle-forbidding clauses for all
  triples of the 40 vertices, after quotienting edges by the C20 action;
* every remaining clause is exactly the edge-orbit disjunction induced by the
  concrete 10-vertex set on the corresponding line of the separator file.

After this audit, an independently checked UNSAT proof for the DIMACS file has
the claimed graph-theoretic interpretation.  Only the Python standard library
is used here.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


N = 40
ORBIT_SIZE = 20


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def edge_variable(u: int, v: int) -> int:
    if u > v:
        u, v = v, u
    if not (0 <= u < v < N):
        raise ValueError((u, v))
    if u < ORBIT_SIZE and v < ORBIT_SIZE:
        delta = (v - u) % ORBIT_SIZE
        return min(delta, ORBIT_SIZE - delta)
    if u >= ORBIT_SIZE and v >= ORBIT_SIZE:
        delta = (v - u) % ORBIT_SIZE
        return 10 + min(delta, ORBIT_SIZE - delta)
    if u >= ORBIT_SIZE:
        u, v = v, u
    assert u < ORBIT_SIZE <= v
    return 21 + ((v - ORBIT_SIZE - u) % ORBIT_SIZE)


def parse_dimacs(path: Path) -> tuple[int, list[list[int]]]:
    declared_variables = None
    declared_clauses = None
    clauses: list[list[int]] = []
    current: list[int] = []
    for raw_line in path.read_text(encoding="ascii").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            _, kind, nv, nc = line.split()
            if kind != "cnf":
                raise ValueError(f"not CNF: {kind}")
            declared_variables, declared_clauses = int(nv), int(nc)
            continue
        for token in map(int, line.split()):
            if token == 0:
                clauses.append(current)
                current = []
            else:
                current.append(token)
    if current:
        raise ValueError("unterminated DIMACS clause")
    if declared_variables is None or declared_clauses is None:
        raise ValueError("missing DIMACS header")
    if declared_clauses != len(clauses):
        raise ValueError((declared_clauses, len(clauses)))
    if max(map(abs, itertools.chain.from_iterable(clauses))) > declared_variables:
        raise ValueError("literal exceeds declared variable count")
    return declared_variables, clauses


def expected_triangle_clauses() -> list[list[int]]:
    clauses = {
        tuple(
            sorted(
                {
                    -edge_variable(u, v),
                    -edge_variable(u, w),
                    -edge_variable(v, w),
                }
            )
        )
        for u, v, w in itertools.combinations(range(N), 3)
    }
    return list(map(list, sorted(clauses)))


def parse_witnesses(path: Path) -> list[tuple[int, ...]]:
    result = []
    for line_number, raw_line in enumerate(
        path.read_text(encoding="ascii").splitlines(), 1
    ):
        witness = tuple(map(int, raw_line.split(",")))
        if len(witness) != 10 or len(set(witness)) != 10:
            raise ValueError(f"line {line_number}: not ten distinct vertices")
        if min(witness) < 0 or max(witness) >= N:
            raise ValueError(f"line {line_number}: vertex out of range")
        result.append(witness)
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cnf", type=Path)
    parser.add_argument("separators", type=Path)
    args = parser.parse_args()

    variables, clauses = parse_dimacs(args.cnf)
    if variables != 40:
        raise SystemExit(f"expected exactly 40 variables, got {variables}")

    triangle_clauses = expected_triangle_clauses()
    if clauses[: len(triangle_clauses)] != triangle_clauses:
        raise SystemExit("triangle-clause block does not match semantic audit")

    witnesses = parse_witnesses(args.separators)
    separator_clauses = clauses[len(triangle_clauses) :]
    if len(witnesses) != len(separator_clauses):
        raise SystemExit(
            f"witness/clause count mismatch: {len(witnesses)} vs "
            f"{len(separator_clauses)}"
        )
    for index, (witness, actual_clause) in enumerate(
        zip(witnesses, separator_clauses, strict=True), 1
    ):
        expected_clause = sorted(
            {
                edge_variable(u, v)
                for u, v in itertools.combinations(witness, 2)
            }
        )
        if actual_clause != expected_clause:
            raise SystemExit(f"separator clause {index} fails semantic audit")

    print(
        json.dumps(
            {
                "status": "SEMANTICS VERIFIED",
                "variables": variables,
                "triangle_clauses": len(triangle_clauses),
                "concrete_10_set_clauses": len(witnesses),
                "total_clauses": len(clauses),
                "cnf_sha256": sha256(args.cnf),
                "separator_sha256": sha256(args.separators),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
