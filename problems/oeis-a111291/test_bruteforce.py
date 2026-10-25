#!/usr/bin/env python3
"""Brute-force regression tests for colton_sieve and tau_count (needs numpy; not run in CI).

Computes tau(k) for every k <= N = 2*10^7 with a divisor sieve, hence T(x) and pi(x), and checks
  * colton_sieve N with 1 and 3 threads: T and pi at about 450 checkpoints (random values and
    values around segment boundaries), the verdict line, and every printed TAIL minimum of
    2T(p) - pi(p) over primes p;
  * tau_count: T(x) and pi(x) at about 8000 values of x <= N (every x <= 5000, 3000 random
    values, 2^k and 2^k +- 1, and multiples of p^2 around the primes 61 and 67 where the counter
    switches from its explicit to its generic layer).

Usage: python3 test_bruteforce.py PATH_TO_colton_sieve PATH_TO_tau_count
"""
import os
import random
import subprocess
import sys
import tempfile

import numpy as np

N = 20_000_000
SEG = 1 << 21  # segment size of colton_sieve


def run(cmd):
    return subprocess.run(cmd, capture_output=True, text=True, check=True).stdout


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__)
        return 2
    sieve, counter = sys.argv[1], sys.argv[2]
    tau = np.zeros(N + 1, dtype=np.int32)
    for d in range(1, N + 1):
        tau[d::d] += 1
    n = np.arange(N + 1)
    isref = np.zeros(N + 1, dtype=bool)
    isref[1:] = n[1:] % tau[1:] == 0
    isp = np.zeros(N + 1, dtype=bool)
    isp[2:] = tau[2:] == 2
    T = np.cumsum(isref)
    P = np.cumsum(isp)
    primes = np.nonzero(isp)[0]
    gap = 2 * T - P
    rng = random.Random(2026)
    ok = True

    with tempfile.TemporaryDirectory() as tmp:
        cks = {rng.randrange(1, N + 1) for _ in range(400)}
        cks |= {k * SEG + o for k in range(1, N // SEG + 1) for o in (-2, -1, 0, 1, 2)}
        cks = sorted(c for c in cks if 1 <= c <= N)
        ckfile = os.path.join(tmp, "cks.txt")
        with open(ckfile, "w") as f:
            f.write("\n".join(map(str, cks)) + "\n")
        for threads in (1, 3):
            out = run([sieve, str(N), str(threads), ckfile])
            seen = bad = 0
            for line in out.splitlines():
                if line.startswith("CKPT"):
                    fld = dict(kv.split("=") for kv in line.split()[1:])
                    c = int(fld["n"])
                    seen += 1
                    if (int(fld["T"]), int(fld["pi"])) != (T[c], P[c]):
                        bad += 1
                        print("MISMATCH", line, T[c], P[c])
                elif line.startswith("TAIL"):
                    start = int(line.split()[2].rstrip(":"))
                    val = int(line.split("= ")[1].split()[0])
                    at = int(line.split("p=")[-1].split(";")[0])
                    sel = primes[primes >= start]
                    if (gap[sel].min(), sel[np.argmin(gap[sel])]) != (val, at):
                        bad += 1
                        print("TAIL MISMATCH", line)
            verdict = f"RESULT: VERIFIED pi(n) <= 2T(n) for all n <= {N}"
            if verdict not in out or gap[primes].min() < 0:
                bad += 1
            print(f"colton_sieve {N} with {threads} thread(s): {seen} checkpoints, "
                  f"{out.count('TAIL')} TAIL lines, {bad} mismatches")
            ok &= bad == 0 and seen >= len(cks)

        xs = set(range(1, 5001)) | {rng.randrange(1, N + 1) for _ in range(3000)}
        for k in range(1, 25):
            xs |= {2**k - 1, 2**k, 2**k + 1}
        for p in (59, 61, 67, 71, 101, 1009, 3001):
            for m in (1, 4, 8, 36):
                xs |= {m * p * p - 1, m * p * p, m * p * p + 1}
        xs = sorted(x for x in xs if 1 <= x <= N)
        xfile = os.path.join(tmp, "xs.txt")
        with open(xfile, "w") as f:
            f.write("\n".join(map(str, xs)) + "\n")
        out = run([counter, "-f", xfile])
        seen = bad = 0
        for line in out.splitlines():
            fld = dict(kv.split("=") for kv in line.split())
            x = int(fld["x"])
            seen += 1
            if (int(fld["T"]), int(fld["pi"])) != (T[x], P[x]):
                bad += 1
                print("MISMATCH", line, T[x], P[x])
        print(f"tau_count: {seen} values of x in [1, {N}], {bad} mismatches")
        ok &= bad == 0 and seen == len(xs)

    print("ALL TESTS PASSED" if ok else "TESTS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
