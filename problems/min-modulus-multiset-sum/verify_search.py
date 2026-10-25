#!/usr/bin/env python3
"""Re-verify the exhaustive search for Conjecture 1 of arXiv:2607.08366.

A set A of n residues mod N is *valid* when the all-ones multiset is the only multiset of size n
drawn from A whose sum is sum(A) mod N.  Conjecture 1 says that no n-set is valid mod N for
N < 2^n - 2^floor(log2 n).

Two programs, written separately, enumerate one normal form per affine orbit x -> u x + v
(u a unit) for every modulus N in a range:

* ``mmsearch.cpp`` (C++, threads): bitset multiset sumsets and an incremental validity test,
  elements added in increasing order;
* ``mmcheck.c`` (C): capped counting tables taken straight from the definition, elements after
  the third added in decreasing order, canonicity recomputed from scratch at every node.

The committed logs in ``logs/`` hold the complete output of both programs for n = 3..9 and
N = n..2^n + 8.  This script

1. parses every committed log and checks that both programs cover every modulus in the range,
   report the same affine orbits of valid sets, that every reported set is valid (recomputed
   here in Python), and that the orbits agree with Conjecture 1: none below the conjectured
   minimum and exactly the orbit of {2^k - 1} at the minimum;
2. recompiles both programs and reruns them for the requested sizes (default n = 3..7),
   requiring the fresh output to match the committed logs;
3. reruns the unreduced brute force ``brute.py`` on small ranges (default n = 3..5), which checks
   the normal-form reduction itself.

Usage (from anywhere):
    python3 verify_search.py                       # CI: logs + recompute n=3..7 + brute force
    python3 verify_search.py --recompute 8         # about 3 minutes
    python3 verify_search.py --recompute 9 --threads 3 --no-brute   # several CPU hours
"""

from __future__ import annotations

import argparse
import subprocess
import sys
import tempfile
import time
from math import gcd
from pathlib import Path

HERE = Path(__file__).resolve().parent
LOGS = HERE / "logs"
SIZES = range(3, 10)  # n covered by the committed logs
BRUTE_RANGES = {3: 16, 4: 24, 5: 30}  # n -> largest N for the brute-force comparison

Orbits = dict[int, set[tuple[int, ...]]]


def min_modulus(n: int) -> int:
    """2^n - 2^floor(log2 n), the conjectured least modulus (``minModulus`` in Lean)."""
    return 2**n - 2 ** (n.bit_length() - 1)


def modulus_range(n: int) -> range:
    return range(n, 2**n + 9)


def canonical(A: tuple[int, ...] | list[int], N: int) -> tuple[int, ...]:
    """Lexicographically smallest sorted image u (A - a), a in A, u a unit mod N."""
    best = None
    for a in A:
        for u in range(1, N):
            if gcd(u, N) != 1:
                continue
            img = sorted(u * (x - a) % N for x in A)
            if best is None or img < best:
                best = img
    assert best is not None
    return tuple(best)


def is_valid(A: tuple[int, ...], N: int) -> bool:
    """Count multisets of size |A| over A with sum sum(A) mod N (capped at 2)."""
    n = len(A)
    cnt = [[0] * N for _ in range(n + 1)]
    cnt[0][0] = 1
    for a in A:
        for j in range(1, n + 1):  # increasing j: a may be used repeatedly
            prev, cur = cnt[j - 1], cnt[j]
            for v in range(N):
                if prev[v]:
                    w = (v + a) % N
                    cur[w] = min(2, cur[w] + prev[v])
    return cnt[n][sum(A) % N] == 1


def parse_mmsearch(text: str, n: int, where: str) -> Orbits:
    orbits: Orbits = {}
    for line in text.splitlines():
        if line.startswith("N="):
            fields = dict(f.split("=", 1) for f in line.split() if "=" in f)
            N = int(fields["N"])
            if N in orbits:
                raise AssertionError(f"{where}: N={N} reported twice")
            if fields["orbits"].endswith("+"):
                raise AssertionError(f"{where}: N={N} solution list truncated")
            orbits[N] = set()
        elif line.startswith("  orbit N="):
            head, values = line.split(":", 1)
            N = int(head.split("=")[1])
            A = tuple(int(v) for v in values.split())
            if len(A) != n or N not in orbits:
                raise AssertionError(f"{where}: malformed orbit line {line!r}")
            orbits[N].add(canonical(A, N))
    return orbits


def parse_mmcheck(text: str, n: int, where: str) -> Orbits:
    orbits: Orbits = {}
    pending: list[tuple[int, tuple[int, ...]]] = []
    for line in text.splitlines():
        if line.startswith("SOL N="):
            parts = line.split()
            N = int(parts[1].split("=")[1])
            A = tuple(int(v) for v in parts[2:])
            if len(A) != n:
                raise AssertionError(f"{where}: malformed SOL line {line!r}")
            pending.append((N, A))
        elif line.startswith("N="):
            fields = dict(f.split("=", 1) for f in line.split() if "=" in f)
            N = int(fields["N"])
            if int(fields["n"]) != n or N in orbits:
                raise AssertionError(f"{where}: unexpected summary line {line!r}")
            if any(M != N for M, _ in pending) or int(fields["found"]) != len(pending):
                raise AssertionError(f"{where}: SOL lines do not match N={N}")
            orbits[N] = {canonical(A, N) for _, A in pending}
            pending = []
    if pending:
        raise AssertionError(f"{where}: SOL lines after the last summary line")
    return orbits


def parse_brute(text: str) -> Orbits:
    orbits: Orbits = {}
    for line in text.splitlines():
        if line.startswith("N="):
            orbits[int(line.split()[0].split("=")[1])] = set()
        elif line.startswith("  orbit N="):
            head, values = line.split(":", 1)
            N = int(head.split("=")[1])
            orbits[N].add(tuple(int(v) for v in values.split()))
    return orbits


def check_logs(n: int) -> Orbits:
    """Cross-check the committed logs of both programs for size n; return the orbits."""
    rng = modulus_range(n)
    a = parse_mmsearch((LOGS / f"mmsearch_n{n}.txt").read_text(), n, f"mmsearch_n{n}.txt")
    b = parse_mmcheck((LOGS / f"mmcheck_n{n}.txt").read_text(), n, f"mmcheck_n{n}.txt")
    for name, orbits in (("mmsearch", a), ("mmcheck", b)):
        if sorted(orbits) != list(rng):
            raise AssertionError(f"n={n}: {name} log does not cover N={rng.start}..{rng.stop - 1}")
    for N in rng:
        if a[N] != b[N]:
            raise AssertionError(f"n={n}, N={N}: programs disagree: {sorted(a[N])} vs {sorted(b[N])}")
        for A in a[N]:
            if not is_valid(A, N):
                raise AssertionError(f"n={n}, N={N}: reported set {A} is not valid")
    m = min_modulus(n)
    extremal = canonical([2**k - 1 for k in range(n)], m)
    below = [N for N in rng if N < m and a[N]]
    if below:
        raise AssertionError(f"n={n}: valid sets below the conjectured minimum at N={below}")
    if a[m] != {extremal}:
        raise AssertionError(f"n={n}: N={m} orbits {sorted(a[m])} are not exactly {extremal}")
    return a


def compile_programs(tmp: Path) -> tuple[Path, Path]:
    search, check = tmp / "mmsearch", tmp / "mmcheck"
    subprocess.run(
        ["g++", "-O3", "-std=c++17", "-pthread", str(HERE / "mmsearch.cpp"), "-o", str(search)],
        check=True,
        timeout=300,
    )
    subprocess.run(
        ["gcc", "-O3", "-std=c11", str(HERE / "mmcheck.c"), "-o", str(check)],
        check=True,
        timeout=300,
    )
    return search, check


def chunks(rng: range, parts: int) -> list[tuple[int, int]]:
    """Split a modulus range into contiguous pieces of roughly equal cost (~N^4)."""
    total = sum(N**4 for N in rng)
    pieces, start, acc = [], rng.start, 0
    for N in rng:
        acc += N**4
        if acc >= total * (len(pieces) + 1) / parts and len(pieces) < parts - 1:
            pieces.append((start, N))
            start = N + 1
    pieces.append((start, rng.stop - 1))
    return [p for p in pieces if p[0] <= p[1]]


def recompute(n: int, exe: tuple[Path, Path], threads: int, expected: Orbits) -> None:
    rng = modulus_range(n)
    lo, hi = rng.start, rng.stop - 1
    t0 = time.perf_counter()
    out = subprocess.run(
        [str(exe[0]), str(n), str(lo), str(hi), str(threads)],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    t1 = time.perf_counter()
    procs = [
        subprocess.Popen([str(exe[1]), str(n), str(a), str(b)], stdout=subprocess.PIPE, text=True)
        for a, b in chunks(rng, threads)
    ]
    outs = [p.communicate()[0] for p in procs]
    if any(p.returncode for p in procs):
        raise AssertionError(f"n={n}: mmcheck failed")
    t2 = time.perf_counter()
    a = parse_mmsearch(out, n, f"mmsearch n={n}")
    b = parse_mmcheck("".join(outs), n, f"mmcheck n={n}")
    for name, orbits in (("mmsearch", a), ("mmcheck", b)):
        if orbits != {N: expected[N] for N in rng}:
            raise AssertionError(f"n={n}: fresh {name} output differs from the committed logs")
    print(f"n={n}: recomputed N={lo}..{hi}; both programs match the logs "
          f"(mmsearch {t1 - t0:.1f}s, mmcheck {t2 - t1:.1f}s wall)")


def brute(n: int, hi: int, expected: Orbits) -> None:
    t0 = time.perf_counter()
    out = subprocess.run(
        [sys.executable, str(HERE / "brute.py"), str(n), str(n), str(hi)],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    orbits = parse_brute(out)
    if orbits != {N: expected[N] for N in range(n, hi + 1)}:
        raise AssertionError(f"n={n}: brute force differs from the searches for N<={hi}")
    print(f"n={n}: brute force over all sets matches for N={n}..{hi} "
          f"({time.perf_counter() - t0:.1f}s)")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--recompute", type=int, nargs="*", default=[3, 4, 5, 6, 7],
                        help="sizes n to recompute with both programs (default 3..7)")
    parser.add_argument("--threads", type=int, default=1)
    parser.add_argument("--no-brute", action="store_true")
    args = parser.parse_args()

    logged = {}
    for n in SIZES:
        logged[n] = check_logs(n)
        valid_at = [N for N in modulus_range(n) if logged[n][N]]
        print(f"n={n}: logs agree for N={n}..{2**n + 8}; no valid set below "
              f"{min_modulus(n)}; valid sets exist exactly at N={valid_at}")
    if args.recompute:
        with tempfile.TemporaryDirectory() as tmp:
            exe = compile_programs(Path(tmp))
            for n in args.recompute:
                recompute(n, exe, args.threads, logged[n])
    if not args.no_brute:
        for n, hi in BRUTE_RANGES.items():
            brute(n, hi, logged[n])
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
