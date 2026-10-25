#!/usr/bin/env python3
"""Cross-check the structured counter against the full sieve run.

Recomputes T(n) and pi(n) with tau_count at every checkpoint n recorded in logs/sieve_1e12.log
(1433 values <= 10^12: powers of ten, random values and values around segment boundaries) and at
N = 10^12, and compares them with the values printed by colton_sieve.

Usage: python3 crosscheck_sieve_log.py PATH_TO_tau_count [LOG]
"""
import os
import subprocess
import sys
import tempfile


def main() -> int:
    if len(sys.argv) not in (2, 3):
        print(__doc__)
        return 2
    log = sys.argv[2] if len(sys.argv) == 3 else "logs/sieve_1e12.log"
    want = {}
    for line in open(log):
        f = line.split()
        if line.startswith("CKPT"):
            fld = dict(kv.split("=") for kv in f[1:])
            want[int(fld["n"])] = (int(fld["T"]), int(fld["pi"]))
        elif line.startswith("N = "):  # N = <N>  T(N) = <T>  pi(N) = <pi>
            want[int(f[2])] = (int(f[5]), int(f[8]))
    with tempfile.TemporaryDirectory() as tmp:
        xfile = os.path.join(tmp, "xs.txt")
        with open(xfile, "w") as fh:
            fh.write("\n".join(map(str, sorted(want))) + "\n")
        out = subprocess.run([sys.argv[1], "-f", xfile], capture_output=True, text=True,
                             check=True).stdout
    got = {}
    for line in out.splitlines():
        fld = dict(kv.split("=") for kv in line.split())
        got[int(fld["x"])] = (int(fld["T"]), int(fld["pi"]))
    bad = [n for n in want if got.get(n) != want[n]]
    for n in bad[:10]:
        print(f"MISMATCH at n={n}: sieve {want[n]}, tau_count {got.get(n)}")
    print(f"{len(want)} checkpoints n <= {max(want)}: {len(bad)} mismatches")
    print("CROSSCHECK OK" if want and not bad else "CROSSCHECK FAILED")
    return 0 if want and not bad else 1


if __name__ == "__main__":
    sys.exit(main())
