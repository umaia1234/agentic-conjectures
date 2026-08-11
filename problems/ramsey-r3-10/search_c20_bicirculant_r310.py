#!/usr/bin/env python3
"""SAT+CEGAR search for a C20-invariant (3,10)-Ramsey graph on 40 vertices.

The cyclic group C20 acts semiregularly with two vertex orbits A_0,...,A_19
and B_0,...,B_19.  There are 40 edge orbits:

* 10 undirected cyclic distances within A;
* 10 undirected cyclic distances within B;
* 20 directed offsets A_i -- B_(i+d).

The default SAT instance imposes triangle-freeness and the necessary
degree-at-most-9 condition.  The ``--omit-degree-encoding`` option omits that
redundant bound and produces a semantically simpler certificate containing
only graph-theoretic clauses.  Independent 10-set clauses are separated
lazily: whenever SAT returns a graph, an exact bit-set search finds an
independent 10-set and the corresponding edge-orbit clause is added.  SAT
means a genuine 40-vertex (3,10)-graph; UNSAT exhausts this entire two-orbit
symmetry class.

Dependency: python-sat[pblib].  See README.md for the isolated-venv command.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import platform
import sys
import time
from pathlib import Path

from pysat.formula import CNF
from pysat.pb import PBEnc
from pysat.solvers import Solver

from search_circulant_r310 import (
    ALL_VERTICES,
    N,
    TARGET,
    find_independent_set,
    is_triangle_free,
    verify_witness,
)


ORBIT_SIZE = 20
PRIMARY_VARIABLES = 40


def edge_variable(u: int, v: int) -> int:
    """Return the 1-based SAT variable of the C20-orbit of edge {u,v}."""
    if not (0 <= u < v < N):
        raise ValueError((u, v))
    u_part, u_index = divmod(u, ORBIT_SIZE)
    v_part, v_index = divmod(v, ORBIT_SIZE)
    if u_part == v_part:
        distance = (v_index - u_index) % ORBIT_SIZE
        distance = min(distance, ORBIT_SIZE - distance)
        assert 1 <= distance <= ORBIT_SIZE // 2
        return (0 if u_part == 0 else 10) + distance
    assert u_part == 0 and v_part == 1
    offset = (v_index - u_index) % ORBIT_SIZE
    return 21 + offset


def base_clauses(include_degree_encoding: bool) -> tuple[list[list[int]], int, dict]:
    clauses: list[list[int]] = []

    triangle_clauses = {
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
    clauses.extend(map(list, sorted(triangle_clauses)))

    # Degree of A_0: paired internal distances contribute two neighbours,
    # antipodal distance 10 contributes one, and each cross offset contributes
    # one.  B_0 is analogous.  Triangle-free Ramsey candidates have degree <=9
    # because every neighbourhood is independent.
    a_lits = list(range(1, 10)) + [10] + list(range(21, 41))
    a_weights = [2] * 9 + [1] + [1] * 20
    b_lits = list(range(11, 20)) + [20] + list(range(21, 41))
    b_weights = [2] * 9 + [1] + [1] * 20

    top = PRIMARY_VARIABLES
    degree_a_clauses: list[list[int]] = []
    degree_b_clauses: list[list[int]] = []
    if include_degree_encoding:
        degree_a = PBEnc.atmost(
            a_lits, weights=a_weights, bound=9, top_id=top
        )
        top = degree_a.nv
        degree_b = PBEnc.atmost(
            b_lits, weights=b_weights, bound=9, top_id=top
        )
        top = degree_b.nv
        degree_a_clauses = degree_a.clauses
        degree_b_clauses = degree_b.clauses
        clauses.extend(degree_a_clauses)
        clauses.extend(degree_b_clauses)

    stats = {
        "distinct_triangle_clauses": len(triangle_clauses),
        "degree_encoding_included": include_degree_encoding,
        "degree_encoding_a_clauses": len(degree_a_clauses),
        "degree_encoding_b_clauses": len(degree_b_clauses),
        "base_variables_including_auxiliary": top,
    }
    return clauses, top, stats


def adjacency_from_model(model: list[int]) -> tuple[int, ...]:
    selected = {lit for lit in model if 0 < lit <= PRIMARY_VARIABLES}
    adjacency = [0] * N
    for u, v in itertools.combinations(range(N), 2):
        if edge_variable(u, v) in selected:
            adjacency[u] |= 1 << v
            adjacency[v] |= 1 << u
    return tuple(adjacency)


def independent_set_clause(witness: tuple[int, ...]) -> list[int]:
    """At least one pair in this 10-set must become an edge."""
    return sorted(
        {edge_variable(u, v) for u, v in itertools.combinations(witness, 2)}
    )


def verify_candidate(
    adjacency: tuple[int, ...], degree_encoding_included: bool
) -> dict:
    if not is_triangle_free(adjacency):
        raise AssertionError("SAT model contains a triangle")
    degrees = [adjacency[v].bit_count() for v in range(N)]
    if degree_encoding_included and max(degrees) > 9:
        raise AssertionError("SAT model violates degree bound")
    independent_ten = find_independent_set(adjacency, TARGET)
    return {
        "degrees": degrees,
        "independent_10_set": (
            None if independent_ten is None else list(independent_ten)
        ),
    }


def write_dimacs(path: Path, clauses: list[list[int]]) -> str:
    cnf = CNF(from_clauses=clauses)
    cnf.to_file(path)
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(
    solver_name: str,
    progress_every: int,
    cnf_output: Path | None,
    witness_output: Path | None,
    include_degree_encoding: bool,
) -> dict:
    clauses, top, base_stats = base_clauses(include_degree_encoding)
    started = time.perf_counter()
    iterations = 0
    independent_clause_lengths: dict[int, int] = {}
    separator_witnesses: list[tuple[int, ...]] = []
    result_status = "UNKNOWN"
    candidate_record = None

    with Solver(name=solver_name, bootstrap_with=clauses) as solver:
        while solver.solve():
            iterations += 1
            adjacency = adjacency_from_model(solver.get_model())
            check = verify_candidate(adjacency, include_degree_encoding)
            witness_list = check["independent_10_set"]
            if witness_list is None:
                result_status = "SAT"
                primary_model = sorted(
                    lit
                    for lit in solver.get_model()
                    if 0 < lit <= PRIMARY_VARIABLES
                )
                candidate_record = {
                    "selected_edge_orbit_variables": primary_model,
                    "degrees": check["degrees"],
                }
                break

            witness = tuple(witness_list)
            if not verify_witness(adjacency, witness):
                raise AssertionError("invalid separator witness")
            clause = independent_set_clause(witness)
            if any(lit in solver.get_model() for lit in clause):
                raise AssertionError("separator clause does not block current model")
            clauses.append(clause)
            separator_witnesses.append(witness)
            solver.add_clause(clause)
            independent_clause_lengths[len(clause)] = (
                independent_clause_lengths.get(len(clause), 0) + 1
            )

            if progress_every and iterations % progress_every == 0:
                print(
                    json.dumps(
                        {
                            "iterations": iterations,
                            "learned_independent_set_clauses": iterations,
                            "elapsed_seconds": round(
                                time.perf_counter() - started, 3
                            ),
                        }
                    ),
                    flush=True,
                )
        else:
            result_status = "UNSAT"

    cnf_sha256 = None
    if cnf_output is not None:
        cnf_sha256 = write_dimacs(cnf_output, clauses)

    witness_sha256 = None
    if witness_output is not None:
        witness_output.write_text(
            "".join(
                ",".join(map(str, witness)) + "\n"
                for witness in separator_witnesses
            ),
            encoding="ascii",
        )
        witness_sha256 = hashlib.sha256(witness_output.read_bytes()).hexdigest()

    return {
        "problem": "C20-semiregular (two-orbit) (3,10)-Ramsey graph on 40 vertices",
        "status": result_status,
        "interpretation": (
            "SAT would be a 40-vertex graph with no triangle and no independent "
            "10-set; UNSAT excludes the whole stated symmetry class"
        ),
        "solver": solver_name,
        "primary_edge_orbit_variables": PRIMARY_VARIABLES,
        **base_stats,
        "iterations_sat_models_separated": iterations,
        "learned_independent_set_clauses": iterations,
        "independent_clause_length_histogram": independent_clause_lengths,
        "final_number_of_clauses": len(clauses),
        "largest_variable": top,
        "candidate": candidate_record,
        "cnf_output": None if cnf_output is None else str(cnf_output),
        "cnf_sha256": cnf_sha256,
        "separator_witness_output": (
            None if witness_output is None else str(witness_output)
        ),
        "separator_witness_sha256": witness_sha256,
        "elapsed_seconds": time.perf_counter() - started,
        "python": sys.version,
        "platform": platform.platform(),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", default="cadical195")
    parser.add_argument("--progress-every", type=int, default=1000)
    parser.add_argument("--cnf-output", type=Path)
    parser.add_argument("--witness-output", type=Path)
    parser.add_argument(
        "--omit-degree-encoding",
        action="store_true",
        help=(
            "omit the redundant degree<=9 PB constraints; this gives a larger "
            "but semantically simpler CNF using only triangle and independent-set clauses"
        ),
    )
    parser.add_argument("--json-output", type=Path)
    args = parser.parse_args()
    result = run(
        args.solver,
        args.progress_every,
        args.cnf_output,
        args.witness_output,
        not args.omit_degree_encoding,
    )
    rendered = json.dumps(result, indent=2, sort_keys=True)
    print(rendered)
    if args.json_output:
        args.json_output.write_text(rendered + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
