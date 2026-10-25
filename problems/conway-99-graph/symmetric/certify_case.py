#!/usr/bin/env python3
"""Solve one case and certify an UNSAT answer (local; needs cadical, drat-trim).

  python3 certify_case.py CASE --build DIR [--limit SECONDS] [--keep] [--out DIR]
  (drat-trim from PATH, or set DRAT_TRIM=/path/to/drat-trim)

Steps: write the CNF with srg_sym_encode.py; check it byte for byte with the
independent srg_sym_audit.py; run CaDiCaL with a binary DRAT proof; on UNSAT
run drat-trim (core-first backward check) writing the core lemmas as a binary
DRAT proof; re-check that core proof with drat-trim, which also writes the
clause core; store the core proof and the clause indices of the clause core
(both xz-compressed) for verify_certificates.py.
A SAT answer is decoded and checked as a graph immediately (that would be a
srg(99,14,1,2) and must be reported).  The summary is written to
results/CASE.json and the (abridged) tool output to logs/CASE.log, below --out
(default: this directory).  Exit status 0 means UNSAT with both drat-trim runs
verified; 1 an audit mismatch; 2 anything else (UNKNOWN, SAT, not verified).
"""
import argparse
import hashlib
import json
import lzma
import os
import platform
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
DRAT_TRIM = os.environ.get("DRAT_TRIM", "drat-trim")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def clause_indices(cnf, core_cnf):
    """0-based indices (in file order) of the clauses of cnf listed in core_cnf."""
    want = set()
    with open(core_cnf) as f:
        for line in f:
            if line[:1] not in ("p", "c") and line.strip():
                want.add(tuple(sorted(int(t) for t in line.split()[:-1])))
    idx = []
    with open(cnf) as f:
        next(f)
        for i, line in enumerate(f):
            key = tuple(sorted(int(t) for t in line.split()[:-1]))
            if key in want:
                idx.append(i)
                want.discard(key)
    if want:
        raise ValueError("clause core is not a subset of the CNF")
    return idx


def run(cmd, log, timeout=None):
    t = time.time()
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    dt = time.time() - t
    log.write("$ %s\n" % " ".join(cmd))
    out = (r.stdout + r.stderr).splitlines()
    keep = [l for l in out if not l.startswith("v ")]
    if len(keep) > 80:
        keep = keep[:20] + ["[... %d lines omitted ...]" % (len(keep) - 60)] + keep[-40:]
    log.write("\n".join(keep) + "\n# exit %d, wall %.1fs\n\n" % (r.returncode, dt))
    log.flush()
    return r, dt


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("case")
    ap.add_argument("--build", required=True)
    ap.add_argument("--limit", type=int, default=5400)
    ap.add_argument("--solver", default="cadical")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--out", default=HERE)
    args = ap.parse_args()
    os.makedirs(args.build, exist_ok=True)
    os.makedirs(os.path.join(args.out, "logs"), exist_ok=True)
    os.makedirs(os.path.join(args.out, "results"), exist_ok=True)
    c = args.case
    cnf = os.path.join(args.build, c + ".cnf")
    proof = os.path.join(args.build, c + ".drat")
    core = os.path.join(args.build, c + ".core.drat")
    res = {"case": c, "date": time.strftime("%Y-%m-%d"),
           "machine": platform.machine() + " " + platform.system(),
           "limit_s": args.limit}
    with open(os.path.join(args.out, "logs", c + ".log"), "w") as log:
        r, _ = run([sys.executable, os.path.join(HERE, "srg_sym_encode.py"), "cnf", c,
                    "-o", cnf], log)
        res["encode"] = r.stdout.strip()
        res["cnf_sha256"] = sha256(cnf)
        r, _ = run([sys.executable, os.path.join(HERE, "srg_sym_audit.py"), c, cnf], log)
        res["audit_file_identical"] = "identical" in r.stdout
        if not res["audit_file_identical"]:
            print("audit mismatch for", c)
            return 1
        ver = subprocess.run([args.solver, "--version"], capture_output=True,
                             text=True).stdout.strip()
        res["solver"] = "%s %s" % (args.solver, ver)
        if args.solver == "cadical":
            cmd = ["cadical", "-t", str(args.limit), cnf, proof]
        else:
            cmd = ["kissat", "--time=%d" % args.limit, cnf, proof]
        r, dt = run(cmd, log)
        res["solver_wall_s"] = round(dt, 1)
        for line in r.stdout.splitlines():
            if "total process time" in line or line.startswith("c process-time"):
                res["solver_cpu_line"] = " ".join(line.split()[1:])
        res["solver_exit"] = r.returncode
        if r.returncode == 10:
            res["answer"] = "SAT"
            model = os.path.join(args.build, c + ".model")
            with open(model, "w") as f:
                f.write(r.stdout)
            d = subprocess.run([sys.executable, os.path.join(HERE, "srg_sym_encode.py"),
                                "decode", c, model], capture_output=True, text=True)
            res["decode"] = d.stdout.strip()
            print("SAT ANSWER for %s: %s" % (c, d.stdout.strip()))
        elif r.returncode == 20:
            res["answer"] = "UNSAT"
            res["proof_bytes"] = os.path.getsize(proof)
            r, dt = run([DRAT_TRIM, cnf, proof, "-i", "-l", core, "-C"], log)
            res["drat_trim_wall_s"] = round(dt, 1)
            res["drat_trim_verified"] = ("s VERIFIED" in r.stdout and r.returncode == 0)
            if res["drat_trim_verified"]:
                ccore = os.path.join(args.build, c + ".clause-core.cnf")
                r, dt = run([DRAT_TRIM, cnf, core, "-i", "-c", ccore], log)
                res["core_recheck_verified"] = ("s VERIFIED" in r.stdout and r.returncode == 0)
                res["core_recheck_wall_s"] = round(dt, 1)
                res["core_bytes"] = os.path.getsize(core)
                res["core_sha256"] = sha256(core)
                subprocess.run(["xz", "-9", "-k", "-f", core], check=True)
                res["core_xz_bytes"] = os.path.getsize(core + ".xz")
                idx = clause_indices(cnf, ccore)
                text = ("\n".join(map(str, idx)) + "\n").encode()
                with lzma.open(os.path.join(args.build, c + ".clause-core.txt.xz"), "wb",
                               preset=9) as f:
                    f.write(text)
                res["clause_core_size"] = len(idx)
                res["clause_core_sha256"] = hashlib.sha256(text).hexdigest()
            if not args.keep:
                os.unlink(proof)
        else:
            res["answer"] = "UNKNOWN"
            if os.path.exists(proof):
                os.unlink(proof)
        if not args.keep and os.path.exists(cnf):
            os.unlink(cnf)
    with open(os.path.join(args.out, "results", c + ".json"), "w") as f:
        json.dump(res, f, indent=1)
        f.write("\n")
    print(json.dumps(res))
    ok = res.get("drat_trim_verified") and res.get("core_recheck_verified")
    print("CERTIFIED UNSAT" if ok else "NOT CERTIFIED (%s)" % res.get("answer"))
    return 0 if ok else 2


if __name__ == "__main__":
    sys.exit(main())
