#!/usr/bin/env python3
"""Cross-solve the final C20 bicirculant CNF and emit a DRUP proof.

This is deliberately independent of the graph/CEGAR generator: it consumes
only a DIMACS file.  Four bundled SAT engines must all report UNSAT.  Glucose
4.2 additionally emits a proof trace ending in the empty clause.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from pathlib import Path

from pysat.formula import CNF
from pysat.solvers import Solver


SOLVERS = ("glucose42", "lingeling", "minisat22", "maplesat")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cnf", type=Path)
    parser.add_argument("--proof", type=Path)
    args = parser.parse_args()

    cnf = CNF(from_file=args.cnf)
    results = {}
    for name in SOLVERS:
        started = time.perf_counter()
        with Solver(name=name, bootstrap_with=cnf.clauses) as solver:
            is_sat = solver.solve()
        results[name] = {
            "status": "SAT" if is_sat else "UNSAT",
            "seconds": time.perf_counter() - started,
        }
        if is_sat:
            raise SystemExit(f"cross-check failed: {name} reports SAT")

    proof_record = None
    if args.proof is not None:
        with Solver(
            name="glucose42", bootstrap_with=cnf.clauses, with_proof=True
        ) as solver:
            if solver.solve():
                raise SystemExit("proof-producing Glucose run reports SAT")
            proof = solver.get_proof()
        if not proof or proof[-1].strip() != "0":
            raise SystemExit("proof trace does not end in the empty clause")
        args.proof.write_text("\n".join(proof) + "\n", encoding="ascii")
        proof_record = {
            "path": str(args.proof),
            "lines": len(proof),
            "sha256": sha256(args.proof),
        }

    print(
        json.dumps(
            {
                "cnf": str(args.cnf),
                "cnf_sha256": sha256(args.cnf),
                "variables": cnf.nv,
                "clauses": len(cnf.clauses),
                "solvers": results,
                "proof": proof_record,
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
