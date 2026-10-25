#!/usr/bin/env python3
"""Re-check the committed DRAT certificates (needs drat-trim on PATH).

For every case of cases.json that records a certificate (or only the cases
named on the command line) this script
  1. re-derives the CNF from the group data with srg_sym_audit.py (which does
     not import the encoder) and checks its SHA-256 against cases.json;
  2. selects the clauses listed (as 0-based clause indices) in
     certs/<case>.clause-core.txt.xz, i.e. a sub-formula of that CNF;
  3. runs `drat-trim SUB.cnf certs/<case>.core.drat -i` (binary proof) and
     requires "s VERIFIED".
A sub-formula of the audited CNF that is unsatisfiable makes the whole CNF
unsatisfiable.  The clause core and the core lemmas come from drat-trim
(`-c`, `-l`) runs on the full CNF; certify_case.py records those runs.

Usage: python3 verify_certificates.py [--full] [CASE ...]
  --full   check the proof against the whole CNF instead (slower)
Environment: DRAT_TRIM overrides the drat-trim executable.
"""
import hashlib
import json
import lzma
import os
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from srg_sym_audit import derive_dimacs, generators  # noqa: E402

DRAT_TRIM = os.environ.get("DRAT_TRIM", "drat-trim")


def unxz(path):
    with lzma.open(os.path.join(HERE, path)) as f:
        return f.read()


def check(case, tmp, full):
    name, cert = case["name"], case["certificate"]
    data, _, _ = derive_dimacs(case, generators(case))
    if hashlib.sha256(data).hexdigest() != case["cnf_sha256"]:
        return "CNF hash differs from cases.json"
    proof_bytes = unxz(cert["path"])
    if hashlib.sha256(proof_bytes).hexdigest() != cert["sha256"]:
        return "proof hash differs from cases.json"
    idx_bytes = unxz(cert["clause_core"])
    if hashlib.sha256(idx_bytes).hexdigest() != cert["clause_core_sha256"]:
        return "clause-core hash differs from cases.json"
    cnf = os.path.join(tmp, name + ".cnf")
    if full:
        formula = data
    else:
        lines = data.split(b"\n")
        nvars = int(lines[0].split()[2])
        body = lines[1:-1]
        idx = [int(t) for t in idx_bytes.split()]
        if any(i < 0 or i >= len(body) for i in idx) or len(set(idx)) != len(idx):
            return "bad clause index"
        formula = (b"p cnf %d %d\n" % (nvars, len(idx))
                   + b"".join(body[i] + b"\n" for i in idx))
    with open(cnf, "wb") as f:
        f.write(formula)
    proof = os.path.join(tmp, name + ".drat")
    with open(proof, "wb") as f:
        f.write(proof_bytes)
    r = subprocess.run([DRAT_TRIM, cnf, proof, "-i", "-w"], capture_output=True,
                       text=True)
    os.unlink(cnf)
    os.unlink(proof)
    ok = r.returncode == 0 and any(
        line.strip() == "s VERIFIED" for line in r.stdout.splitlines())
    return None if ok else "drat-trim did not verify"


def main(argv):
    full = "--full" in argv
    argv = [a for a in argv if a != "--full"]
    with open(os.path.join(HERE, "cases.json")) as f:
        cases = {c["name"]: c for c in json.load(f)["cases"]}
    names = argv or [n for n, c in cases.items() if "certificate" in c]
    bad = 0
    with tempfile.TemporaryDirectory() as tmp:
        for name in names:
            t0 = time.time()
            if "certificate" not in cases[name]:
                err = "no certificate recorded"
            else:
                err = check(cases[name], tmp, full)
            bad += err is not None
            print("%s %s: %s (%.1fs)" % ("FAIL" if err else "PASS", name,
                                          err or "drat-trim s VERIFIED", time.time() - t0),
                  flush=True)
    print("CERTIFICATES %s (%d cases%s)" % ("OK" if not bad else "FAILED", len(names),
                                            ", full CNF" if full else ""))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
