#!/usr/bin/env python3
"""Prove A395412 nonvanishing witnesses with PARI/GP ECPP certificates.

Local-only (needs PARI/GP 2.19 or later with ECPP).  The recorded run over
85 <= n <= 478 used about 24400 s of PARI CPU time, 2.5 h wall with four jobs
on a heavily loaded Apple M5 Max.  For every n in [--from, --to] one
single-threaded gp process runs ``a395412_witness`` from a395412_ecpp.gp: it
takes the least squarefree d < p_n whose candidate P_n/d + d passes BPSW,
proves that candidate prime with ``primecert`` and accepts the certificate only
if ``primecertisvalid`` succeeds on the file written to --cert-dir.  BPSW only
selects d; the ECPP certificate is the proof.

Rows are merged into --output (n already present there is skipped, so an
interrupted or budget-limited run can be resumed or extended).  The proved
range is the contiguous block of rows starting at the smallest n.  With
--expect, the witnesses are compared with an existing data file (this
directory's ecpp_witnesses.json, or the older result.json).  The certificates
can be re-checked without PARI by ``verify_witnesses.py --cert-dir``.
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import math
import platform
import shutil
import subprocess
import sys
import time
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from pathlib import Path

HERE = Path(__file__).resolve().parent
GP_SCRIPT = HERE / "a395412_ecpp.gp"
COLUMNS = [
    "n", "p_n", "d", "candidate_bits", "candidate_decimal_sha256", "ecpp_steps",
    "certificate_sha256", "primecert_cpu_s", "check_cpu_s", "wall_s",
]


def first_primes(count: int) -> list[int]:
    limit = 32
    while True:
        sieve = bytearray([1]) * (limit + 1)
        sieve[0:2] = b"\x00\x00"
        for i in range(2, math.isqrt(limit) + 1):
            if sieve[i]:
                sieve[i * i::i] = bytearray(len(range(i * i, limit + 1, i)))
        primes = [i for i in range(limit + 1) if sieve[i]]
        if len(primes) >= count:
            return primes[:count]
        limit *= 2


def run_gp(gp: str, stack: str, n: int, cert_dir: Path) -> dict:
    final = cert_dir / f"a395412_n{n}.cert"
    part = cert_dir / f"a395412_n{n}.cert.part"
    script = f'read("{GP_SCRIPT}"); a395412_witness({n}, "{part}");\n'
    for attempt in range(3):  # a gp process killed from outside is simply rerun
        part.unlink(missing_ok=True)
        started = time.time()
        proc = subprocess.run(
            [gp, "-q", "-f", "-D", "nbthreads=1", "-D", "parisizemax=8G", "-s", stack],
            input=script, text=True, capture_output=True,
        )
        wall = time.time() - started
        lines = [ln.split() for ln in proc.stdout.splitlines() if ln.startswith("A395412")]
        if proc.returncode == 0 and lines:
            break
        print(f"n={n}: gp exited with code {proc.returncode} and no result "
              f"(attempt {attempt + 1}); {proc.stderr.strip()[-300:]}", flush=True)
    if len(lines) != 1 or lines[0][0] not in ("A395412", "A395412-ZERO"):
        raise RuntimeError(f"n={n}: unexpected gp output\n{proc.stdout[-800:]}{proc.stderr[-800:]}")
    if lines[0][0] == "A395412-ZERO":
        return {"n": n, "zero": True, "wall_s": round(wall, 2)}
    _, n_out, p, d, bits, steps, cert_ms, check_ms, skipped = lines[0]
    if int(n_out) != n or int(skipped) != 0:
        raise RuntimeError(f"n={n}: unexpected gp line {lines[0]}")
    part.replace(final)
    return {
        "n": n,
        "p_n": int(p),
        "d": int(d),
        "candidate_bits": int(bits),
        "ecpp_steps": int(steps),
        "certificate_sha256": hashlib.sha256(final.read_bytes()).hexdigest(),
        "primecert_cpu_s": round(int(cert_ms) / 1000, 2),
        "check_cpu_s": round(int(check_ms) / 1000, 2),
        "wall_s": round(wall, 2),
    }


def add_candidate_digest(row: dict, primes: list[int]) -> None:
    n, d = row["n"], row["d"]
    if primes[n - 1] != row["p_n"] or not 1 <= d < row["p_n"]:
        raise RuntimeError(f"n={n}: inconsistent p_n or d")
    value = math.prod(primes[:n]) // d + d
    if value.bit_length() != row["candidate_bits"]:
        raise RuntimeError(f"n={n}: bit length differs between PARI and Python")
    row["candidate_decimal_sha256"] = hashlib.sha256(str(value).encode("ascii")).hexdigest()


def proved_range(rows: list[list]) -> list[int] | None:
    ns = sorted(r[0] for r in rows)
    if not ns:
        return None
    hi = ns[0]
    for n in ns[1:]:
        if n != hi + 1:
            break
        hi = n
    return [ns[0], hi]


def save(path: Path, data: dict) -> None:
    data["rows"].sort(key=lambda r: r[0])
    data["proved_nonzero_range"] = proved_range(data["rows"])
    head = {k: v for k, v in data.items() if k != "rows"}
    text = json.dumps(head, indent=2)[:-2] + ',\n  "rows": [\n'
    text += ",\n".join("    " + json.dumps(r) for r in data["rows"]) + "\n  ]\n}\n"
    tmp = path.with_suffix(".tmp")
    tmp.write_text(text, encoding="ascii")
    tmp.replace(path)


def load_expected(path: Path) -> dict[int, tuple]:
    data = json.loads(path.read_text())
    if "rows" in data:
        cols = data["columns"]
        return {r[0]: (r[cols.index("d")], r[cols.index("candidate_bits")],
                       r[cols.index("candidate_decimal_sha256")],
                       r[cols.index("certificate_sha256")]) for r in data["rows"]}
    old = data["proved_witnesses"] + data["bpsw_screened_witnesses"]
    return {r["n"]: (r["d"], r["candidate_bits"], r["candidate_decimal_sha256"], None)
            for r in old}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--from", dest="lo", type=int, default=85)
    ap.add_argument("--to", dest="hi", type=int, default=400)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--gp", default="gp")
    ap.add_argument("--stack", default="512M")
    ap.add_argument("--cert-dir", type=Path, default=HERE / "build" / "certificates")
    ap.add_argument("--output", type=Path, default=HERE / "build" / "ecpp_witnesses.json")
    ap.add_argument("--budget-minutes", type=float, default=None,
                    help="start no new n once the next one is unlikely to finish in time")
    ap.add_argument("--expect", type=Path, default=None)
    args = ap.parse_args()

    sys.set_int_max_str_digits(0)
    gp = shutil.which(args.gp)
    if gp is None:
        ap.error("PARI/GP not found; pass --gp PATH")
    version = subprocess.run([gp, "--version-short"], text=True, capture_output=True).stdout
    args.cert_dir.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if args.output.exists():
        data = json.loads(args.output.read_text())
    else:
        data = {
            "problem": "OEIS A395412",
            "claim": "a(n) > 0 for every n in proved_nonzero_range",
            "witness_rule": ("least squarefree d < p_n whose candidate P_n/d + d passes BPSW "
                             "(PARI ispseudoprime); primality is proved by an ECPP certificate "
                             "accepted by primecertisvalid"),
            "certificate_format": ("one ECPP step [N_i, t_i, s_i, a_i, [x_i, y_i]] per line, "
                                   "as written by PARI; GP: primecertisvalid(readvec(file))"),
            "columns": COLUMNS,
            "runs": [],
            "zero_candidates": [],
            "rows": [],
        }
    done = {r[0] for r in data["rows"]}
    todo = [n for n in range(args.lo, args.hi + 1) if n not in done]
    primes = first_primes(args.hi)
    run = {
        "from": args.lo, "to_requested": args.hi, "jobs": args.jobs,
        "budget_minutes": args.budget_minutes,
        "pari_gp_version": version.strip(), "gp_flags": "-D nbthreads=1",
        "machine": f"{platform.machine()} {platform.system()} {platform.release()}",
        "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
    }
    started = time.time()
    last_wall = 0.0
    completed: list[dict] = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        pending = {}
        queue = list(todo)
        while queue or pending:
            budget_left = (args.budget_minutes is None
                           or time.time() - started + 1.3 * last_wall < 60 * args.budget_minutes)
            while queue and len(pending) < args.jobs and budget_left:
                n = queue.pop(0)
                pending[pool.submit(run_gp, gp, args.stack, n, args.cert_dir)] = n
            if not pending:
                break
            finished, _ = wait(pending, return_when=FIRST_COMPLETED)
            for fut in finished:
                n = pending.pop(fut)
                row = fut.result()
                if row.get("zero"):
                    data["zero_candidates"].append(row)
                    print(f"n={n}: NO BPSW-probable-prime candidate", flush=True)
                    continue
                add_candidate_digest(row, primes)
                last_wall = max(last_wall, row["wall_s"])
                completed.append(row)
                data["rows"].append([row[c] for c in COLUMNS])
                save(args.output, data)
                print(f"n={n} d={row['d']} bits={row['candidate_bits']} "
                      f"steps={row['ecpp_steps']} cert={row['primecert_cpu_s']}s "
                      f"wall={row['wall_s']}s elapsed={time.time() - started:.0f}s", flush=True)
    run["completed"] = len(completed)
    run["completed_range"] = proved_range([[r["n"]] for r in completed])
    run["wall_s"] = round(time.time() - started, 1)
    run["cpu_s"] = round(sum(r["primecert_cpu_s"] + r["check_cpu_s"] for r in completed), 1)
    data["runs"].append(run)
    save(args.output, data)
    print(json.dumps(run, indent=2))

    status = 0
    if args.expect:
        expected = load_expected(args.expect)
        same_cert = compared = 0
        for row in data["rows"]:
            r = dict(zip(COLUMNS, row))
            if r["n"] not in expected:
                continue
            compared += 1
            d, bits, digest, cert = expected[r["n"]]
            if (r["d"], r["candidate_bits"], r["candidate_decimal_sha256"]) != (d, bits, digest):
                print(f"MISMATCH n={r['n']}: got d={r['d']}, expected d={d}")
                status = 1
            same_cert += cert == r["certificate_sha256"]
        print(f"compared {compared} witnesses with {args.expect.name}: "
              f"{'all equal' if status == 0 else 'MISMATCHES'}; "
              f"identical certificates: {same_cert}")
    return 1 if data["zero_candidates"] else status


if __name__ == "__main__":
    sys.exit(main())
