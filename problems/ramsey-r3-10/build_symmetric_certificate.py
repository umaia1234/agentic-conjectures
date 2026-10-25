#!/usr/bin/env python3
"""Build a certificate for one symmetric class (local tool, not run in CI).

Pipeline:

1. ``search_symmetric_r310.py instance`` (+ ``sbp`` when normalising);
2. the C++ back end ``cegar_symmetric_r310.cpp`` in IPASIR-UP mode collects
   10-set separators until CaDiCaL reports UNSAT;
3. a few trimming rounds keep only separators in a drat-trim UNSAT core;
4. the final DIMACS file is written by the independent audit
   (``audit_symmetric_certificate.py --write-cnf``), solved by CaDiCaL with a
   DRAT proof (options ``--final-flags``), and drat-trim emits the core
   lemmas as a binary DRAT proof, which is re-verified;
5. separators and proof are stored xz-compressed in ``--outdir``.

With ``--no-proof-output`` (for proofs too large to commit) step 4 only
checks the raw CaDiCaL proof with drat-trim and step 5 stores the separators
alone; ``<class>.build.json`` records the SHA-256 of the CNF and the proof.

Requires: a C++17 compiler, CaDiCaL (library + binary, >= 2.0 for
IPASIR-UP), drat-trim.  Example:

  python3 build_symmetric_certificate.py c10-4orb --normalise --outdir symmetric
"""

from __future__ import annotations

import argparse
import hashlib
import json
import lzma
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
GEN = HERE / "search_symmetric_r310.py"
AUDIT = HERE / "audit_symmetric_certificate.py"
CPP = HERE / "cegar_symmetric_r310.cpp"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 24), b""):
            digest.update(chunk)
    return digest.hexdigest()


def run(cmd: list[str], **kw) -> tuple[subprocess.CompletedProcess, float]:
    start = time.perf_counter()
    result = subprocess.run(cmd, capture_output=True, text=True, **kw)
    return result, time.perf_counter() - start


def need(result: subprocess.CompletedProcess, token: str, what: str) -> None:
    if token not in result.stdout:
        raise SystemExit(f"{what} failed:\n{result.stdout[-2000:]}\n{result.stderr[-2000:]}")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("cls")
    ap.add_argument("--outdir", type=Path, required=True)
    ap.add_argument("--normalise", action="store_true",
                    help="use the translation-normalisation and orbit-sorting blocks")
    ap.add_argument("--separators", type=Path, help="skip the search, start from this file")
    ap.add_argument("--rounds", type=int, default=3)
    ap.add_argument("--final-flags", default="--unsat",
                    help="CaDiCaL options for the final proof")
    ap.add_argument("--nodes", type=int, default=2000)
    ap.add_argument("--cadical-prefix", default="/opt/homebrew")
    ap.add_argument("--drat-trim", default=shutil.which("drat-trim") or "drat-trim")
    ap.add_argument("--workdir", type=Path)
    ap.add_argument("--no-proof-output", action="store_true",
                    help="check the raw proof only and do not store it")
    args = ap.parse_args()

    work = args.workdir or Path(tempfile.mkdtemp(prefix=f"r310-{args.cls}-"))
    work.mkdir(parents=True, exist_ok=True)
    args.outdir.mkdir(parents=True, exist_ok=True)
    py = sys.executable
    gen_flags = ["--normalise", "--sort-orbits"] if args.normalise else []
    audit_flags = ["--normalised", "--sorted-orbits"] if args.normalise else []
    record: dict = {"class": args.cls, "normalised": args.normalise,
                    "final_cadical_flags": args.final_flags}

    if args.separators:
        seps = args.separators
    else:
        binary = work / "cegar"
        prefix = args.cadical_prefix
        r, _ = run(["c++", "-O3", "-std=c++17", f"-I{prefix}/include", str(CPP),
                    f"-L{prefix}/lib", "-lcadical", "-o", str(binary)])
        if r.returncode:
            raise SystemExit(r.stderr)
        inst = work / "instance.txt"
        r, _ = run([py, str(GEN), "instance", args.cls, str(inst)])
        cmd = [str(binary), "--instance", str(inst), "--out", str(work / "raw.sep"),
               "--up", "--nodes", str(args.nodes), "--log-every", "0"]
        if args.normalise:
            sbp = work / "sbp.cnf"
            run([py, str(GEN), "sbp", args.cls, str(sbp), "--sort-orbits"])
            cmd += ["--extra", str(sbp)]
        r, t = run(cmd)
        need(r, '"UNSAT"', "search")
        record["search"] = json.loads(r.stdout.strip().splitlines()[-1]) | {"wall_s": round(t, 1)}
        seps = work / "raw.sep"

    rounds = []
    for rnd in range(args.rounds):
        cnf = work / f"r{rnd}.cnf"
        r, _ = run([py, str(GEN), "cnf", args.cls, str(seps), str(cnf)] + gen_flags)
        count = json.loads(r.stdout)["separator_clauses"]
        proof = work / f"r{rnd}.drat"
        r, t_sat = run(["cadical", "-q", str(cnf), str(proof)])
        need(r, "s UNSATISFIABLE", "cadical")
        core = work / f"r{rnd}.core"
        r, t_chk = run([args.drat_trim, str(cnf), str(proof), "-c", str(core), "-w"])
        need(r, "s VERIFIED", "drat-trim core")
        nxt = work / f"r{rnd + 1}.sep"
        r, _ = run([py, str(GEN), "core", args.cls, str(seps), str(core), str(nxt)])
        kept = json.loads(r.stdout)["kept"]
        rounds.append({"separators": count, "kept": kept, "cadical_s": round(t_sat, 1),
                       "drat_trim_s": round(t_chk, 1)})
        print(json.dumps(rounds[-1]), flush=True)
        seps = nxt
        if kept == count:
            break
    record["trim_rounds"] = rounds

    final_cnf = work / "final.cnf"
    r, _ = run([py, str(AUDIT), args.cls, str(seps), "--write-cnf", str(final_cnf)] + audit_flags)
    need(r, "SEMANTICS VERIFIED", "audit --write-cnf")
    raw = work / "final.drat"
    r, t_sat = run(["cadical", "-q", *args.final_flags.split(), str(final_cnf), str(raw)])
    need(r, "s UNSATISFIABLE", "final cadical")
    if args.no_proof_output:
        proof = raw
        r, t_chk = run([args.drat_trim, str(final_cnf), str(raw), "-w"])
        need(r, "s VERIFIED", "drat-trim")
    else:
        proof = work / "core-lemmas.drat"
        r, _ = run([args.drat_trim, str(final_cnf), str(raw), "-C", "-l", str(proof), "-w"])
        need(r, "s VERIFIED", "drat-trim lemma extraction")
        r, t_chk = run([args.drat_trim, str(final_cnf), str(proof), "-i"])
        need(r, "s VERIFIED", "drat-trim on core lemmas")

    stem = args.outdir / args.cls
    sep_bytes = seps.read_bytes()
    preset = 9 | lzma.PRESET_EXTREME
    Path(f"{stem}.separators.txt.xz").write_bytes(lzma.compress(sep_bytes, preset=preset))
    if not args.no_proof_output:
        Path(f"{stem}.drat.xz").write_bytes(lzma.compress(proof.read_bytes(), preset=preset))
    record.update(
        {
            "final_separators": sep_bytes.count(b"\n"),
            "cnf_sha256": sha256_file(final_cnf),
            "cnf_bytes": final_cnf.stat().st_size,
            "separators_sha256": sha256_bytes(sep_bytes),
            "proof": "raw CaDiCaL proof, not stored" if args.no_proof_output
            else "drat-trim core lemmas, binary DRAT",
            "proof_sha256": sha256_file(proof),
            "proof_bytes": proof.stat().st_size,
            "final_cadical_s": round(t_sat, 1),
            "drat_trim_s": round(t_chk, 1),
            "drat_trim_summary": [ln.strip() for ln in r.stdout.splitlines()
                                  if "core" in ln or ln.startswith("s ")],
        }
    )
    Path(f"{stem}.build.json").write_text(json.dumps(record, indent=2) + "\n", encoding="ascii")
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
