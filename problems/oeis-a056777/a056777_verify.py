#!/usr/bin/env python3
"""CI-feasible re-check of the A056777 exhaustive search (Python + sympy + g++ only).

1. Builds a056777_search.cpp (implementation 1) and a056777_sums.cpp with g++.
2. Runs implementation 1 on [1, --brute] with small blocks and segments and compares every
   block line (composite hits, prime hits, exact sums of phi and sigma, hash) with a
   pure-Python smallest-prime-factor recurrence written here (a third implementation).
3. Runs implementation 1 on [1, --limit] and checks that its composite hits are exactly the
   values p(p+8), p, p+2, p+6, p+8 prime, up to --limit; every hit is re-checked with sympy's
   totient and divisor_sigma, and the run's totals with the closed forms of a056777_sums.
4. Audits the committed logs in logs/: the main-run blocks tile [1, N] with no gap or overlap,
   their composite hits are exactly the prime-quadruple values up to N (each re-checked with
   sympy), the per-run totals match the DONE lines, the running totals of sum(phi) and
   sum(sigma) match the closed forms at every run boundary, and every block of the
   implementation-2 log is identical to the corresponding main-run block.
   It also checks that a056777_hits.txt lists exactly those hits.
5. Optionally (--independent X, needs numpy and numba) reruns implementation 2 on [1, X] and
   compares every block with the committed main-run logs.

Usage: python3 a056777_verify.py [--limit 1000000000] [--brute 1000000] [--threads 2]
                                 [--skip-logs] [--independent X]
"""
import argparse
import math
import re
import subprocess
import sys
import tempfile
from pathlib import Path

from sympy import divisor_sigma, isprime, totient

HERE = Path(__file__).resolve().parent
LOGS = HERE / "logs"
MAIN_LOGS = ["main_1e11.log", "main_1e12_part1.log", "main_1e12_part2.log",
             "main_1e12_part3.log"]
INDEP_LOGS = ["independent_1e11.log"]
HASH_C = 0x9E3779B97F4A7C15
MASK = (1 << 64) - 1
BLOCK_RE = re.compile(r"BLOCK (\d+) lo=(\d+) hi=(\d+) hits=(\d+) primehits=(\d+) "
                      r"sumphi=(\d+) sumsigma=(\d+) hash=([0-9a-f]{16})")
DONE_RE = re.compile(r"DONE start=(\d+) end=(\d+) hits=(\d+) primehits=(\d+) "
                     r"sumphi=(\d+) sumsigma=(\d+) hash=([0-9a-f]{16})")
HIT_RE = re.compile(r"HIT (\d+) phi=(\d+) sigma=(\d+) phi12=(\d+) sigma12=(\d+)")

failures = []


def check(cond, msg):
    if not cond:
        failures.append(msg)
        print("FAIL:", msg)


def parse(text):
    blocks, hits, done = [], [], None
    for line in text.splitlines():
        if m := BLOCK_RE.match(line):
            k, lo, hi, nh, nph, sp, ss = (int(g) for g in m.groups()[:7])
            blocks.append((k, lo, hi, nh, nph, sp, ss, int(m.group(8), 16)))
        elif m := HIT_RE.match(line):
            hits.append(tuple(int(g) for g in m.groups()))
        elif m := DONE_RE.match(line):
            done = tuple(int(g) for g in m.groups()[:6]) + (int(m.group(7), 16),)
    return sorted(blocks, key=lambda b: b[1]), sorted(hits), done


def quadruple_values(limit):
    """{p(p+8) <= limit : p, p+2, p+6, p+8 all prime}, by a plain sieve."""
    top = math.isqrt(limit) + 9
    sieve = bytearray([1]) * (top + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, math.isqrt(top) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(range(i * i, top + 1, i)))
    return sorted(p * (p + 8) for p in range(2, top - 7)
                  if sieve[p] and sieve[p + 2] and sieve[p + 6] and sieve[p + 8]
                  and p * (p + 8) <= limit)


def check_hits_sympy(hits):
    for n, ph, sg, ph12, sg12 in hits:
        check((totient(n), divisor_sigma(n), totient(n + 12), divisor_sigma(n + 12))
              == (ph, sg, ph12, sg12), f"sympy disagrees with HIT {n}")
        check(ph12 == ph + 12 and sg12 == sg + 12 and n > 1 and not isprime(n),
              f"HIT {n} is not a composite solution")


def reference_blocks(end, block):
    """Pure-Python phi/sigma via the smallest-prime-factor recurrence; same block format."""
    top = end + 12
    spf = list(range(top + 1))
    for i in range(2, math.isqrt(top) + 1):
        if spf[i] == i:
            for j in range(i * i, top + 1, i):
                if spf[j] == j:
                    spf[j] = i
    phi = [0, 1] + [0] * (top - 1)
    sig = [0, 1] + [0] * (top - 1)
    for m in range(2, top + 1):
        p, k, pe = spf[m], m, 1
        while k % p == 0:
            k //= p
            pe *= p
        phi[m] = phi[k] * (pe - pe // p)
        sig[m] = sig[k] * ((pe * p - 1) // (p - 1))
    out = []
    for kb in range((end - 1) // block + 1):
        lo, hi = kb * block + 1, min(end, (kb + 1) * block)
        nh = nph = sp = ss = h = 0
        for n in range(lo, hi + 1):
            sp += phi[n]
            ss += sig[n]
            h = (h + ((phi[n] * HASH_C + sig[n]) & MASK) * (2 * n + 1)) & MASK
            if phi[n + 12] == phi[n] + 12 and sig[n + 12] == sig[n] + 12:
                if phi[n] == n - 1:
                    nph += 1
                else:
                    nh += 1
        out.append((kb, lo, hi, nh, nph, sp, ss, h))
    return out


def closed_forms(sums_bin, xs):
    out = subprocess.run([str(sums_bin)] + [str(x) for x in xs], check=True,
                         capture_output=True, text=True).stdout
    res = {}
    for line in out.splitlines():
        kind, x, v = line.split()
        res[(kind, int(x))] = int(v)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=10**9)
    ap.add_argument("--brute", type=int, default=10**6)
    ap.add_argument("--threads", type=int, default=2)
    ap.add_argument("--skip-logs", action="store_true")
    ap.add_argument("--independent", type=int, metavar="X")
    a = ap.parse_args()

    with tempfile.TemporaryDirectory() as td:
        search, sums = Path(td) / "a056777_search", Path(td) / "a056777_sums"
        for src, out in (("a056777_search.cpp", search), ("a056777_sums.cpp", sums)):
            subprocess.run(["g++", "-O3", "-std=c++17", "-pthread", "-o", str(out),
                            str(HERE / src)], check=True)

        # 2. block-by-block agreement with the pure-Python reference
        bb = max(1, a.brute // 8)
        out = subprocess.run([str(search), "--start", "1", "--end", str(a.brute), "--block",
                              str(bb), "--seg", "1000", "--threads", str(a.threads)],
                             check=True, capture_output=True, text=True).stdout
        got, _, _ = parse(out)
        ref = reference_blocks(a.brute, bb)
        check(got == ref, f"implementation 1 differs from the reference on [1, {a.brute}]")
        print(f"[2] {len(ref)} blocks on [1, {a.brute}] identical to the pure-Python reference")

        # 3. small exhaustive run versus the prime-quadruple prediction and the closed forms
        out = subprocess.run([str(search), "--start", "1", "--end", str(a.limit),
                              "--threads", str(a.threads)],
                             check=True, capture_output=True, text=True).stdout
        _, hits, done = parse(out)
        check_hits_sympy(hits)
        pred = quadruple_values(a.limit)
        check([h[0] for h in hits] == pred, f"hits up to {a.limit} differ from p(p+8) values")
        cf = closed_forms(sums, [a.limit])
        check(done is not None and done[4] == cf[("PHISUM", a.limit)]
              and done[5] == cf[("SIGMASUM", a.limit)], "totals differ from closed forms")
        print(f"[3] n <= {a.limit}: {len(hits)} composite solutions, all p(p+8) from prime "
              f"quadruples and all such values found; totals match closed forms")

        if not a.skip_logs:
            audit_logs(sums)
        if a.independent:
            rerun_independent(a.independent, a.threads)

    if failures:
        print(f"{len(failures)} check(s) FAILED")
        return 1
    print("all checks passed")
    return 0


def main_log_blocks():
    blocks = []
    for name in MAIN_LOGS:
        blocks += parse((LOGS / name).read_text())[0]
    return {(b[1], b[2]): b for b in blocks}


def rerun_independent(x, procs):
    out = subprocess.run([sys.executable, str(HERE / "a056777_independent.py"), "--start", "1",
                          "--end", str(x), "--procs", str(procs)],
                         check=True, capture_output=True, text=True).stdout
    blocks, _, _ = parse(out)
    by_range = main_log_blocks()
    for b in blocks:
        check(by_range.get((b[1], b[2])) == b, f"rerun of implementation 2: block {b[1]}..{b[2]}")
    print(f"[5] implementation 2 rerun on [1, {x}]: {len(blocks)} blocks compared with the logs")


def audit_logs(sums):
    main_blocks, main_hits, bounds = [], [], []
    for name in MAIN_LOGS:
        path = LOGS / name
        check(path.exists(), f"missing log {name}")
        if not path.exists():
            continue
        blocks, hits, done = parse(path.read_text())
        check(done is not None, f"{name}: no DONE line")
        if done is None:
            continue
        start, end = done[0], done[1]
        check(blocks and blocks[0][1] == start and blocks[-1][2] == end,
              f"{name}: blocks do not cover [start, end]")
        check(sum(b[3] for b in blocks) == done[2] == len(hits), f"{name}: hit counts")
        check(sum(b[4] for b in blocks) == done[3], f"{name}: prime-hit counts")
        check(sum(b[5] for b in blocks) == done[4], f"{name}: sum phi")
        check(sum(b[6] for b in blocks) == done[5], f"{name}: sum sigma")
        check(sum(b[7] for b in blocks) & MASK == done[6], f"{name}: hash")
        main_blocks += blocks
        main_hits += hits
        bounds.append(end)
    main_blocks.sort(key=lambda b: b[1])
    check(bool(main_blocks) and main_blocks[0][1] == 1, "main logs do not start at n = 1")
    for x, y in zip(main_blocks, main_blocks[1:]):
        check(y[1] == x[2] + 1, f"gap or overlap between blocks ending {x[2]} and starting {y[1]}")
    N = main_blocks[-1][2] if main_blocks else 0
    main_hits.sort()
    check_hits_sympy(main_hits)
    pred = quadruple_values(N)
    check([h[0] for h in main_hits] == pred, f"logged hits up to {N} differ from p(p+8) values")
    listed = [int(line.split()[0]) for line in (HERE / "a056777_hits.txt").read_text().splitlines()
              if line.strip() and not line.startswith("#")]
    check(listed == pred, "a056777_hits.txt differs from the logged hits")
    # running totals at every run boundary versus the closed forms
    cf = closed_forms(sums, bounds)
    for b in bounds:
        sp = sum(x[5] for x in main_blocks if x[2] <= b)
        ss = sum(x[6] for x in main_blocks if x[2] <= b)
        check(sp == cf[("PHISUM", b)] and ss == cf[("SIGMASUM", b)],
              f"logged totals up to {b} differ from closed forms")
    # implementation 2 versus implementation 1, block by block
    by_range = {(x[1], x[2]): x for x in main_blocks}
    ncmp, top2 = 0, 0
    for name in INDEP_LOGS:
        path = LOGS / name
        check(path.exists(), f"missing log {name}")
        if not path.exists():
            continue
        blocks, hits2, _ = parse(path.read_text())
        check(bool(blocks) and blocks[0][1] == 1
              and all(y[1] == x[2] + 1 for x, y in zip(blocks, blocks[1:])),
              f"{name}: blocks do not tile an initial segment [1, X]")
        for b in blocks:
            check(by_range.get((b[1], b[2])) == b, f"{name}: block {b[1]}..{b[2]} differs")
            ncmp += 1
            top2 = max(top2, b[2])
        check([h for h in main_hits if h[0] <= top2] == hits2, f"{name}: hits differ")
    print(f"[4] logs: {len(main_blocks)} blocks tile [1, {N}]; {len(main_hits)} composite "
          f"solutions = all p(p+8) <= N; totals match closed forms at {bounds}; "
          f"{ncmp} implementation-2 blocks (to {top2}) identical")


if __name__ == "__main__":
    sys.exit(main())
