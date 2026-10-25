#!/usr/bin/env python3
"""Regenerate the Chvatal CNFs and check their DRAT certificates.

Standard library only; the external tools are called as subprocesses.

  repo-n6        Regenerate the reduced cardnet CNF for n = 6 with
                 generate_cnf.py, run under a Python that has PySAT (this
                 script's interpreter by default).  Its SHA256 must match
                 drat_manifest.json; generate_cnf.py --solve --proof writes
                 the DRAT trace of PySAT's CaDiCaL 1.9.5, which drat-trim
                 must accept.
  rank           Regenerate the rank-split CNFs of generate_rank_cnf.py,
                 compare their SHA256 with the manifest and check the
                 committed proofs in drat/ with drat-trim.
  rank --solve   The same for the cases whose proofs are too large to
                 commit: a fresh proof comes from the `cadical` binary.

Each case passes only if drat-trim prints "s VERIFIED" and exits with 0;
otherwise this script exits with status 1.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import generate_rank_cnf  # noqa: E402

MANIFEST = HERE / "drat_manifest.json"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def tool(name: str, override: str | None) -> str:
    found = override or shutil.which(name)
    if not found:
        raise SystemExit(f"{name} not found on PATH")
    return found


def drat_check(drat_trim: str, cnf: Path, proof: Path) -> dict:
    started = time.perf_counter()
    run = subprocess.run(
        [drat_trim, str(cnf), str(proof), "-w", "-t", "100000"],
        capture_output=True, text=True, errors="replace",
    )
    return {
        "drat_trim_verified": run.returncode == 0 and "s VERIFIED" in run.stdout,
        "drat_trim_seconds": round(time.perf_counter() - started, 2),
    }


def cadical_proof(cadical: str, cnf: Path, proof: Path) -> dict:
    version = subprocess.run([cadical, "--version"], capture_output=True,
                             text=True).stdout.strip()
    started = time.perf_counter()
    run = subprocess.run([cadical, str(cnf), str(proof)],
                         capture_output=True, text=True, errors="replace")
    record = {
        "solver": f"cadical {version}",
        "solver_unsat": run.returncode == 20,
        "solver_seconds": round(time.perf_counter() - started, 2),
        "proof_bytes": proof.stat().st_size if proof.exists() else 0,
    }
    for line in run.stdout.splitlines():
        if line.startswith("c conflicts:"):
            record["conflicts"] = int(line.split()[2])
    return record


def repo_n6(args: argparse.Namespace) -> list[dict]:
    expected = json.loads(MANIFEST.read_text())["repo_n6"]
    work = Path(args.workdir)
    cnf, proof = work / "repo_n6.cnf", work / "repo_n6.drat"
    started = time.perf_counter()
    run = subprocess.run(
        [args.pysat_python, str(HERE / "generate_cnf.py"), "--n", "6",
         "--reduced", "--encoding", "cardnet", "--output", str(cnf),
         "--solve", "--proof", str(proof)],
        check=True, capture_output=True, text=True,
    )
    result = json.loads(run.stdout)
    record = {
        "case": "repo_n6",
        "cnf_sha256": sha256(cnf),
        "solver": "PySAT cadical195 (CaDiCaL 1.9.5)",
        "solver_unsat": result["status"] == "UNSAT",
        "solver_seconds": round(time.perf_counter() - started, 2),
        "conflicts": result["stats"].get("conflicts"),
        "proof_bytes": proof.stat().st_size if proof.exists() else 0,
    }
    record["cnf_matches_manifest"] = record["cnf_sha256"] == expected["cnf_sha256"]
    record.update(drat_check(tool("drat-trim", args.drat_trim), cnf, proof))
    record["ok"] = (record["cnf_matches_manifest"] and record["solver_unsat"]
                    and record["drat_trim_verified"])
    return [record]


def rank_case(name: str, entry: dict, args: argparse.Namespace) -> dict:
    n, r = entry["n"], entry["rank"]
    work = Path(args.workdir)
    cnf = work / f"{name}.cnf"
    enc = generate_rank_cnf.build(n, r)
    cnf.write_text(generate_rank_cnf.dimacs(enc))
    record = {"case": name, "variables": enc.top, "clauses": len(enc.clauses),
              "cnf_sha256": sha256(cnf)}
    record["cnf_matches_manifest"] = record["cnf_sha256"] == entry["cnf_sha256"]
    solver_ok = True
    if args.solve:
        proof = work / f"{name}.drat"
        record.update(cadical_proof(tool("cadical", args.cadical), cnf, proof))
        solver_ok = record["solver_unsat"]
    else:
        proof = HERE / entry["proof"]
        record["proof_sha256"] = sha256(proof)
        record["proof_matches_manifest"] = (
            record["proof_sha256"] == entry["proof_sha256"])
    record.update(drat_check(tool("drat-trim", args.drat_trim), cnf, proof))
    if args.solve:
        proof.unlink(missing_ok=True)
    cnf.unlink(missing_ok=True)
    record["ok"] = (record["cnf_matches_manifest"] and solver_ok
                    and record["drat_trim_verified"])
    return record


def rank(args: argparse.Namespace) -> list[dict]:
    cases = json.loads(MANIFEST.read_text())["rank_split"]["cases"]
    wanted = "regenerate" if args.solve else "committed"
    selected = [name for name, entry in cases.items()
                if entry["certificate"] == wanted
                and (not args.cases or name in args.cases)]
    unknown = set(args.cases or []) - set(selected)
    if unknown:
        raise SystemExit(f"not {wanted} cases in the manifest: {sorted(unknown)}")
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        futures = [pool.submit(rank_case, name, cases[name], args)
                   for name in selected]
        records = []
        for future in futures:
            record = future.result()
            print(json.dumps(record, sort_keys=True), flush=True)
            records.append(record)
    return records


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=("repo-n6", "rank"))
    parser.add_argument("--solve", action="store_true",
                        help="rank mode: prove the 'regenerate' cases with cadical")
    parser.add_argument("--cases", nargs="+", help="rank mode: e.g. n7_r4")
    parser.add_argument("--pysat-python", default=sys.executable)
    parser.add_argument("--cadical")
    parser.add_argument("--drat-trim")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--workdir")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="chvatal-drat-") as tmp:
        args.workdir = args.workdir or tmp
        os.makedirs(args.workdir, exist_ok=True)
        if args.mode == "repo-n6":
            records = repo_n6(args)
            print(json.dumps(records[0], sort_keys=True))
        else:
            records = rank(args)
    failed = [r["case"] for r in records if not r["ok"]]
    print(json.dumps({"cases": len(records), "failed": failed}))
    return 1 if failed or not records else 0


if __name__ == "__main__":
    sys.exit(main())
