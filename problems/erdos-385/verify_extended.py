#!/usr/bin/env python3
"""Verify the exact Erdős 385 classification through 10^11.

Two independent multithreaded C++ programs produced the committed logs:

* ``allint_segments.cpp`` sieves every integer, writing the primes in
  decreasing order so that the smallest prime overwrites last, and evaluates
  F(n) directly over all composites.  Each index segment is processed
  independently after an explicit warm-up.
* ``odd_carry.cpp`` sieves odd integers only, keeping the first (smallest)
  prime that reaches an entry, and uses the parity reduction for even and odd
  indices.  It performs one exact scan from m = 3, carrying the running
  maximum through the whole range.

Each log has one JSON record per index segment (k*10^9, (k+1)*10^9].  A record
holds the equality cases F(n) = n, the minimum slack F(n) - n and where it
occurs, the last n with slack <= t for 18 thresholds t, the exact sum of the
slacks, and the wrapping 64-bit sum over n of splitmix64((n << 20) + F(n) - n),
a fingerprint of the full sequence F(n).

Default (CI) mode:

1. check the committed logs' SHA-256 values against ``extended_result.json``;
2. check both headers, contiguous coverage of [6, 10^11], and that the two
   implementations agree on every segment record;
3. recombine the records and compare them with ``extended_result.json``;
   segment 0, which is [6, 10^9], must also match ``billion_result.json``;
4. check every equality case against the Lean theorem
   ``even_and_prime_pred_of_F_eq``: n is even and n - 1 is prime;
5. compile both programs, recompute the first and last segments with each of
   them, and require records identical to the committed ones; also compare
   both programs with a trial-division evaluation of the definition on
   [6, 30000].

``--full`` recomputes every segment with both programs instead of only the
first and last ones.  That takes several CPU-minutes and is not CI-feasible.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import subprocess
import tempfile
from pathlib import Path

from sympy import isprime

HERE = Path(__file__).resolve().parent
RESULT = HERE / "extended_result.json"
BILLION = HERE / "billion_result.json"
PROGRAMS = ("allint_segments", "odd_carry")
THRESHOLDS = [0, 1, 2, 3, 5, 10, 20, 50, 100, 200, 500, 1000,
              2000, 5000, 10000, 20000, 50000, 100000]
MASK64 = (1 << 64) - 1


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_log(text: str, program: str, n_lo: int, n_hi: int, seg: int) -> list[dict]:
    lines = text.splitlines()
    header = json.loads(lines[0])
    expected_header = {"program": program, "n_lo": n_lo, "n_hi": n_hi, "seg": seg,
                       "thresholds": THRESHOLDS}
    if header != expected_header:
        raise AssertionError(f"{program}: unexpected header {header}")
    records = [json.loads(line) for line in lines[1:]]
    next_lo = n_lo
    for rec in records:
        k = rec["k"]
        if rec["lo"] != max(n_lo, k * seg + 1) or rec["hi"] != min(n_hi, (k + 1) * seg):
            raise AssertionError(f"{program}: segment {k} has wrong bounds")
        if rec["lo"] != next_lo or rec["count"] != rec["hi"] - rec["lo"] + 1:
            raise AssertionError(f"{program}: segments do not tile [{n_lo}, {n_hi}]")
        next_lo = rec["hi"] + 1
        if len(rec["last_at_most"]) != len(THRESHOLDS):
            raise AssertionError(f"{program}: segment {k} has the wrong threshold count")
    if next_lo != n_hi + 1:
        raise AssertionError(f"{program}: log does not reach {n_hi}")
    return records


def combine(records: list[dict]) -> dict:
    equalities = [n for rec in records for n in rec["equalities"]]
    if equalities != sorted(set(equalities)):
        raise AssertionError("equality cases are not strictly increasing")
    last = {str(t): max(rec["last_at_most"][j] for rec in records)
            for j, t in enumerate(THRESHOLDS)}
    return {
        "equality_case_count": len(equalities),
        "equality_cases": equalities,
        "last_equality": equalities[-1],
        "last_n_with_slack_at_most": last,
        "sum_slack": sum(rec["sum_slack"] for rec in records),
        "fingerprint": format(sum(int(rec["hash"], 16) for rec in records) & MASK64, "016x"),
    }


def min_slack_over(records: list[dict], lower: int, upper: int) -> dict:
    inside = [rec for rec in records if lower <= rec["lo"] and rec["hi"] <= upper]
    if not inside or inside[0]["lo"] != lower or inside[-1]["hi"] != upper:
        raise AssertionError(f"range [{lower}, {upper}] is not a union of segments")
    best = min(inside, key=lambda rec: (rec["min_slack"], rec["min_slack_n"]))
    return {"lower": lower, "upper": upper, "min_slack": best["min_slack"],
            "at": best["min_slack_n"]}


def splitmix(z: int) -> int:
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK64
    return z ^ (z >> 31)


def reference_records(n_lo: int, n_hi: int, seg: int) -> list[dict]:
    """Segment records straight from the definition, by trial division."""

    def least_prime_factor(m: int) -> int:
        d = 2
        while d * d <= m:
            if m % d == 0:
                return d
            d += 1
        return m

    best = 0  # max of m + p(m) over composite m < n
    records: dict[int, dict] = {}
    for m in range(2, n_hi):
        p = least_prime_factor(m)
        if p != m:
            best = max(best, m + p)
        n = m + 1
        if n < n_lo:
            continue
        s = best - n
        k = (n - 1) // seg
        rec = records.setdefault(k, {
            "k": k, "lo": max(n_lo, k * seg + 1), "hi": min(n_hi, (k + 1) * seg),
            "count": 0, "equalities": [], "min_slack": None, "min_slack_n": 0,
            "sum_slack": 0, "hash": 0, "last_at_most": [0] * len(THRESHOLDS)})
        rec["count"] += 1
        rec["sum_slack"] += s
        rec["hash"] = (rec["hash"] + splitmix((n << 20) + s)) & MASK64
        if rec["min_slack"] is None or s < rec["min_slack"]:
            rec["min_slack"], rec["min_slack_n"] = s, n
        if s == 0:
            rec["equalities"].append(n)
        for j, t in enumerate(THRESHOLDS):
            if s <= t:
                rec["last_at_most"][j] = n
    for rec in records.values():
        rec["hash"] = format(rec["hash"], "016x")
    return [records[k] for k in sorted(records)]


def compile_programs(tmpdir: Path) -> dict[str, Path]:
    binaries = {}
    for name in PROGRAMS:
        out = tmpdir / name
        subprocess.run(["g++", "-O3", "-std=c++17", "-pthread", str(HERE / f"{name}.cpp"),
                        "-o", str(out)], check=True, capture_output=True, text=True,
                       timeout=300)
        binaries[name] = out
    return binaries


def run_program(binary: Path, n_lo: int, n_hi: int, seg: int, threads: int) -> str:
    return subprocess.run([str(binary), str(n_lo), str(n_hi), str(seg), str(threads)],
                          check=True, capture_output=True, text=True).stdout


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--full", action="store_true",
                        help="recompute all segments with both programs (slow)")
    parser.add_argument("--threads", type=int, default=min(4, os.cpu_count() or 1))
    args = parser.parse_args()

    expected = json.loads(RESULT.read_text(encoding="utf-8"))
    limit, seg = expected["limit"], expected["segment_size"]
    if expected["thresholds"] != THRESHOLDS:
        raise AssertionError("threshold list mismatch")

    # 1-2. Committed logs: integrity, coverage, and agreement of both programs.
    logs = {}
    for name in PROGRAMS:
        entry = expected["logs"][name]
        path = HERE / entry["path"]
        if sha256(path) != entry["sha256"]:
            raise AssertionError(f"{path.name}: SHA-256 mismatch")
        logs[name] = parse_log(path.read_text(encoding="utf-8"), name, 6, limit, seg)
    if logs["allint_segments"] != logs["odd_carry"]:
        raise AssertionError("the two implementations disagree on a segment record")
    records = logs["allint_segments"]
    if len(records) != expected["segment_count"]:
        raise AssertionError("segment count mismatch")

    # 3. Recombination and consistency with the earlier 10^9 certificate.
    combined = combine(records)
    for key, value in combined.items():
        if expected[key] != value:
            raise AssertionError(f"extended_result.json disagrees on {key}")
    if expected["strict_interval"] != {"lower": combined["last_equality"] + 1, "upper": limit}:
        raise AssertionError("strict interval mismatch")
    for rng in expected["min_slack_by_range"]:
        if min_slack_over(records, rng["lower"], rng["upper"]) != rng:
            raise AssertionError(f"min-slack summary mismatch on {rng}")
    billion = json.loads(BILLION.read_text(encoding="utf-8"))
    first = records[0]
    if (first["lo"], first["hi"]) != (6, billion["limit"]):
        raise AssertionError("segment 0 is not [6, 10^9]")
    if first["equalities"] != billion["equality_cases"]:
        raise AssertionError("segment 0 disagrees with billion_result.json equality cases")
    old_thresholds = {str(t): first["last_at_most"][j] for j, t in enumerate(THRESHOLDS[:12])}
    if old_thresholds != billion["last_n_with_slack_at_most"]:
        raise AssertionError("segment 0 disagrees with billion_result.json thresholds")

    # 4. Lean necessary condition for equality cases.
    for n in combined["equality_cases"]:
        if n % 2 != 0 or not isprime(n - 1):
            raise AssertionError(f"equality case {n} violates the Lean necessary condition")

    # 5. Recompute with both programs.
    if args.full:
        jobs = [(name, 6, limit) for name in PROGRAMS]
    else:
        last = records[-1]
        jobs = [(name, lo, hi) for name in PROGRAMS
                for lo, hi in ((6, first["hi"]), (last["lo"], last["hi"]))]
    by_k = {rec["k"]: rec for rec in records}
    with tempfile.TemporaryDirectory(prefix="erdos385-ext-") as tmp:
        binaries = compile_programs(Path(tmp))
        threads = args.threads if args.full else 1
        workers = 1 if args.full else max(1, args.threads)
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
            futures = {pool.submit(run_program, binaries[name], lo, hi, seg, threads):
                       (name, lo, hi) for name, lo, hi in jobs}
            for future, (name, lo, hi) in futures.items():
                fresh = parse_log(future.result(), name, lo, hi, seg)
                for rec in fresh:
                    if rec != by_k[rec["k"]]:
                        raise AssertionError(f"{name}: recomputed segment {rec['k']} differs")
        reference = reference_records(6, 30000, 10000)
        for name in PROGRAMS:
            small = parse_log(run_program(binaries[name], 6, 30000, 10000, 1), name, 6,
                              30000, 10000)
            if small != reference:
                raise AssertionError(f"{name}: disagrees with trial division on [6, 30000]")

    print(json.dumps({
        "result": "classification verified by two independent implementations",
        "limit": limit,
        "segments_recomputed": "all" if args.full else [records[0]["k"], records[-1]["k"]],
        "equality_case_count": combined["equality_case_count"],
        "last_equality": combined["last_equality"],
        "strict_interval": expected["strict_interval"],
        "last_n_with_slack_at_most": combined["last_n_with_slack_at_most"],
    }, indent=2))


if __name__ == "__main__":
    main()
