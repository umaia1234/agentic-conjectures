#!/usr/bin/env python3
"""Audit A354747 candidate exponents with explicit base-2 Fermat witnesses.

Input is one exponent per line.  Each K*3^m-1 is tested twice by OpenPFGW,
at its default FFT length and at the next larger FFT length.  A matching,
non-1 RES64 from the two runs is a reproducible base-2 Fermat-compositeness
check; full output is retained if a run is anomalous.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import pathlib
import re
import subprocess
import tempfile
import time

K = 201886
COMPOSITE_RE = re.compile(r"is composite: RES64: \[([0-9A-F]+)\]")


def one_run(pfgw: str, exponent: int, larger_fft: bool) -> tuple[int, str, str]:
    expression = f"-q{K}*3^{exponent}-1"
    args = [pfgw, "-f0", "-b2"]
    if larger_fft:
        args.append("-a1")
    args.append(expression)
    with tempfile.TemporaryDirectory(prefix=f"a354747_m{exponent}_") as work:
        result = subprocess.run(
            args,
            cwd=work,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
    matches = COMPOSITE_RE.findall(result.stdout)
    residue = matches[-1] if matches else ""
    return result.returncode, residue, result.stdout


def audit_one(pfgw: str, exponent: int) -> tuple[int, str, float, str]:
    start = time.monotonic()
    rc0, residue0, out0 = one_run(pfgw, exponent, False)
    rc1, residue1, out1 = one_run(pfgw, exponent, True)
    elapsed = time.monotonic() - start
    if rc0 == 1 and rc1 == 1 and residue0 and residue0 == residue1:
        return exponent, residue0, elapsed, ""
    diagnostic = f"default:\n{out0}\nnext FFT:\n{out1}"
    return exponent, "ANOMALY", elapsed, diagnostic


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("exponents", type=pathlib.Path)
    parser.add_argument("--pfgw", default="/tmp/pfgw.25adjA/pfgw64")
    parser.add_argument("--workers", type=int, default=12)
    args = parser.parse_args()

    values = sorted({int(line) for line in args.exponents.read_text().splitlines()})
    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        jobs = [pool.submit(audit_one, args.pfgw, exponent) for exponent in values]
        for job in concurrent.futures.as_completed(jobs):
            results.append(job.result())

    anomalies = 0
    print("m\tbase2_RES64\tseconds")
    for exponent, residue, elapsed, diagnostic in sorted(results):
        print(f"{exponent}\t{residue}\t{elapsed:.6f}")
        if diagnostic:
            anomalies += 1
            print(diagnostic)
    print(f"SUMMARY tested={len(values)} anomalies={anomalies}")
    raise SystemExit(1 if anomalies else 0)


if __name__ == "__main__":
    main()
