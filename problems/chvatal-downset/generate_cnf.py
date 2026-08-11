#!/usr/bin/env python3
"""Generate or solve the saturated-search CNF for Chvatal's conjecture.

This script needs PySAT (`python-sat[pblib]`).  It deliberately does not call
an n=6 UNSAT answer a proof: unless a solver proof trace is independently
checked, the result remains a reproducible solver computation.
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

try:
    from pysat.card import CardEnc, EncType as CardEncType
    from pysat.formula import CNF, IDPool
    from pysat.pb import EncType as PBEncType
    from pysat.pb import PBEnc
    from pysat.solvers import Solver
except ImportError as exc:  # pragma: no cover - exercised only without PySAT
    raise SystemExit(
        'PySAT is required. Install it with: pip install "python-sat[pblib]"'
    ) from exc


@dataclass(frozen=True)
class VariableMap:
    """Stable DIMACS identifiers for membership variables."""

    n: int

    @property
    def number_of_sets(self) -> int:
        return 1 << self.n

    def x(self, subset: int) -> int:
        return subset + 1

    def y(self, subset: int) -> int:
        return self.number_of_sets + subset + 1

    @property
    def first_auxiliary(self) -> int:
        return 2 * self.number_of_sets + 1


def submasks(mask: int, *, include_zero: bool = True) -> Iterable[int]:
    current = mask
    while True:
        if current != 0 or include_zero:
            yield current
        if current == 0:
            return
        current = (current - 1) & mask


def build_cnf(
    n: int,
    *,
    reduced: bool,
    encoding: str,
) -> tuple[CNF, VariableMap, int]:
    """Build the CNF and return it with its variable map and top variable."""

    if n < 1:
        raise ValueError("n must be positive")
    if reduced and n < 4:
        raise ValueError("the literature reductions require n >= 4")

    variables = VariableMap(n)
    number_of_sets = variables.number_of_sets
    universe = number_of_sets - 1
    cnf = CNF()
    pool = IDPool(start_from=variables.first_auxiliary)

    # Y is pairwise intersecting.  Empty Y-membership is fixed below.
    for left in range(1, number_of_sets):
        complement = universe ^ left
        for right in submasks(complement, include_zero=False):
            if left < right:
                cnf.append([-variables.y(left), -variables.y(right)])

    # D equals down(Y), not merely a downset containing Y.
    for small in range(number_of_sets):
        complement = universe ^ small
        supersets: list[int] = []
        for extra in submasks(complement):
            large = small | extra
            supersets.append(variables.y(large))
            cnf.append([-variables.y(large), variables.x(small)])
        cnf.append([-variables.x(small), *supersets])

    # Saturation lemma: every omitted member of D is blocked by a disjoint
    # member of Y.
    for target in range(number_of_sets):
        complement = universe ^ target
        disjoint_y = [
            variables.y(member)
            for member in submasks(complement, include_zero=False)
        ]
        cnf.append(
            [-variables.x(target), variables.y(target), *disjoint_y]
        )

    # A counterexample has |Y| > every star.  The transformed cardinality
    # expression contains only literals with coefficient one.
    y_literals = [variables.y(member) for member in range(1, number_of_sets)]
    bound = number_of_sets // 2 + 1
    for element in range(n):
        literals = y_literals + [
            -variables.x(member)
            for member in range(number_of_sets)
            if member & (1 << element)
        ]
        if encoding == "bdd":
            encoded = PBEnc.atleast(
                lits=literals,
                bound=bound,
                vpool=pool,
                encoding=PBEncType.bdd,
            )
        elif encoding == "cardnet":
            encoded = CardEnc.atleast(
                lits=literals,
                bound=bound,
                vpool=pool,
                encoding=CardEncType.cardnetwrk,
            )
        else:  # guarded by argparse, retained for programmatic callers
            raise ValueError(f"unknown encoding: {encoding}")
        cnf.extend(encoded.clauses)

    cnf.append([variables.x(0)])
    cnf.append([-variables.y(0)])

    if reduced:
        # Corollary 3 and Proposition 5 of Eifler--Gleixner--Pulaj, plus
        # induction over the ground-set size.  See README.md for assumptions.
        for member in range(1, number_of_sets):
            if member.bit_count() <= 2:
                cnf.append([-variables.y(member)])
        for element in range(n):
            cnf.append([variables.x(1 << element)])
        cnf.append([variables.x((1 << 4) - 1)])

    return cnf, variables, pool.top


def validate_candidate(
    n: int,
    variables: VariableMap,
    model: Sequence[int],
) -> dict[str, object]:
    """Decode and independently validate a satisfying assignment."""

    number_of_sets = 1 << n
    positive = {literal for literal in model if literal > 0}
    downset = {
        member
        for member in range(number_of_sets)
        if variables.x(member) in positive
    }
    intersecting = {
        member
        for member in range(1, number_of_sets)
        if variables.y(member) in positive
    }

    expected_downset = {
        small
        for large in intersecting
        for small in submasks(large)
    }
    if downset != expected_downset:
        raise AssertionError("x is not exactly down(Y)")

    members = sorted(intersecting)
    for index, left in enumerate(members):
        for right in members[index + 1 :]:
            if left & right == 0:
                raise AssertionError("decoded Y is not intersecting")

    star_sizes = [
        sum(bool(member & (1 << element)) for member in downset)
        for element in range(n)
    ]
    if len(intersecting) <= max(star_sizes, default=0):
        raise AssertionError("decoded assignment is not a counterexample")

    for target in downset - intersecting:
        if all(target & member for member in intersecting):
            raise AssertionError("decoded Y violates saturation")

    return {
        "downset_size": len(downset),
        "intersecting_size": len(intersecting),
        "star_sizes": star_sizes,
        "downset_bitmasks": sorted(downset),
        "intersecting_bitmasks": members,
    }


def solve_cnf(
    cnf: CNF,
    variables: VariableMap,
    *,
    solver_name: str,
) -> dict[str, object]:
    started = time.perf_counter()
    with Solver(name=solver_name, bootstrap_with=cnf.clauses, use_timer=True) as solver:
        satisfiable = solver.solve()
        elapsed = time.perf_counter() - started
        result: dict[str, object] = {
            "status": "SAT" if satisfiable else "UNSAT",
            "solver": solver_name,
            "wall_seconds": elapsed,
            "solver_seconds": solver.time(),
            "stats": solver.accum_stats(),
            "external_proof_certificate": False,
        }
        if satisfiable:
            result["candidate"] = validate_candidate(
                variables.n, variables, solver.get_model()
            )
        return result


def self_test() -> None:
    # No literature reductions are needed for this tiny semantic check.
    cnf, variables, top = build_cnf(3, reduced=False, encoding="bdd")
    result = solve_cnf(cnf, variables, solver_name="cadical195")
    if result["status"] != "UNSAT":
        raise AssertionError("the n=3 core encoding should be UNSAT")
    print(
        json.dumps(
            {
                "self_test": "passed",
                "n": 3,
                "variables": top,
                "clauses": len(cnf.clauses),
                **result,
            },
            indent=2,
            sort_keys=True,
        )
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=6)
    parser.add_argument(
        "--reduced",
        action="store_true",
        help="apply literature reductions described in README.md",
    )
    parser.add_argument(
        "--encoding", choices=("bdd", "cardnet"), default="bdd"
    )
    parser.add_argument("--output", type=Path, help="write DIMACS CNF here")
    parser.add_argument("--solve", action="store_true")
    parser.add_argument("--solver", default="cadical195")
    parser.add_argument("--self-test", action="store_true")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.self_test:
        self_test()
        return

    started = time.perf_counter()
    cnf, variables, top = build_cnf(
        args.n, reduced=args.reduced, encoding=args.encoding
    )
    summary: dict[str, object] = {
        "n": args.n,
        "reduced": args.reduced,
        "encoding": args.encoding,
        "variables": top,
        "clauses": len(cnf.clauses),
        "build_seconds": time.perf_counter() - started,
    }

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        cnf.to_file(str(args.output))
        summary["dimacs_output"] = str(args.output.resolve())
    if args.solve:
        summary.update(
            solve_cnf(cnf, variables, solver_name=args.solver)
        )
    if not args.output and not args.solve:
        summary["note"] = "use --output and/or --solve"

    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

