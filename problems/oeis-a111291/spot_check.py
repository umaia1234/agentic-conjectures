#!/usr/bin/env python3
"""Spot checks of tau_count far beyond the full sieve run.

For intervals [L, N] around 10^13, 7.42*10^13 (Zelinsky's threshold), 10^14 and 10^15
(L - 1 = center - 10^9 rounded down to the sieve's segment size, N = center + 10^9), colton_sieve in
interval mode gives T(n) - T(L-1) and pi(n) - pi(L-1) at checkpoints n (the center, N and three
random points); compare with tau_count(n) - tau_count(L-1).

Usage: python3 spot_check.py PATH_TO_colton_sieve PATH_TO_tau_count [threads]
"""
import os
import random
import subprocess
import sys
import tempfile

SEG = 1 << 21  # segment size of colton_sieve


def run(cmd):
    return subprocess.run(cmd, capture_output=True, text=True, check=True).stdout


def main() -> int:
    if len(sys.argv) not in (3, 4):
        print(__doc__)
        return 2
    sieve, counter = sys.argv[1], sys.argv[2]
    threads = sys.argv[3] if len(sys.argv) == 4 else "3"
    rng = random.Random(7)
    allok = True
    with tempfile.TemporaryDirectory() as tmp:
        ckfile = os.path.join(tmp, "cks.txt")
        for center in (10**13, 74200000000000, 10**14, 10**15):
            L = (center - 10**9) // SEG * SEG
            N = center + 10**9
            cks = sorted({center, N} | {rng.randrange(L, N + 1) for _ in range(3)})
            with open(ckfile, "w") as f:
                f.write("\n".join(map(str, cks)) + "\n")
            sv = {}
            for line in run([sieve, str(N), threads, ckfile, str(L)]).splitlines():
                if line.startswith("DCKPT"):
                    fld = dict(kv.split("=") for kv in line.split()[1:])
                    sv[int(fld["n"])] = (int(fld["dT"]), int(fld["dpi"]))
            t = {}
            for line in run([counter, str(L - 1)] + [str(c) for c in cks]).splitlines():
                fld = dict(kv.split("=") for kv in line.split())
                t[int(fld["x"])] = (int(fld["T"]), int(fld["pi"]))
            for n in cks:
                d = (t[n][0] - t[L - 1][0], t[n][1] - t[L - 1][1])
                ok = d == sv.get(n)
                allok &= ok
                print(f"[{L}, {N}] n={n}: sieve dT={sv[n][0]} dpi={sv[n][1]}; "
                      f"tau_count dT={d[0]} dpi={d[1]} {'OK' if ok else 'MISMATCH'}", flush=True)
    print("SPOT CHECKS", "ALL OK" if allok else "FAILED")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
