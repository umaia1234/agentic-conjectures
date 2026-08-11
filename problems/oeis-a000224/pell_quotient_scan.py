#!/usr/bin/env python3
"""Explore A000224 through its exact generalized-Pell quotient.

If K = (n^2-1)/(R(R-1)) is integral and y=2R-1, X=2n, then

    X^2 - K*y^2 = 4-K.

For nonsquare K, ``diop_DN`` supplies the finite set of seed solutions and
the fundamental unit generates each orbit.  Square K is handled directly by
factoring (s*y-X)(s*y+X)=s^2-4.  K=4 is excluded analytically: it forces
R=(n+1)/2, which for odd n>1 happens exactly at primes.

This is an exact CAS-assisted search within the stated K and n bounds, but it
is supplementary evidence rather than a proof of the unrestricted conjecture.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import sys
import time
from collections import Counter
from math import isqrt, prod
from pathlib import Path

import sympy
from sympy import factorint
from sympy.solvers.diophantine.diophantine import diop_DN


def prime_power_R(p: int, e: int) -> int:
    if p == 2:
        return 2**e // 6 + 2
    return p ** (e + 1) // (2 * p + 2) + 1


def square_count(n: int) -> tuple[int, dict[int, int]]:
    factors = {int(p): int(e) for p, e in factorint(n).items()}
    return prod(prime_power_R(p, e) for p, e in factors.items()), factors


def positive_divisors(n: int):
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            yield d
            if d * d != n:
                yield n // d


def square_k_candidates(k: int):
    s = isqrt(k)
    assert s * s == k and s >= 3
    target = s * s - 4
    for u in positive_divisors(target):
        v = target // u
        if v <= u:
            continue
        if (v - u) % 2 or (u + v) % (2 * s):
            continue
        x = (v - u) // 2
        y = (u + v) // (2 * s)
        if x > 2 and x % 2 == 0 and y > 0 and y % 2 == 1:
            yield x // 2, (y + 1) // 2


def nonsquare_k_candidates(k: int, max_n: int):
    units = diop_DN(k, 1)
    if not units:
        return
    unit_x, unit_y = map(int, units[0])
    seeds = [(int(x), int(y)) for x, y in diop_DN(k, 4 - k)]

    for seed_x, seed_y in seeds:
        for sign_x in (-1, 1):
            for sign_y in (-1, 1):
                x, y = sign_x * seed_x, sign_y * seed_y
                for _ in range(512):
                    ax, ay = abs(x), abs(y)
                    if ax <= 2 * max_n and ax > 2 and ax % 2 == 0 and ay % 2 == 1:
                        yield ax // 2, (ay + 1) // 2
                    # With equal signs both absolute coordinates now increase
                    # strictly under multiplication by the positive unit.
                    if ax > 2 * max_n and x * y > 0:
                        break
                    x, y = (
                        x * unit_x + y * unit_y * k,
                        x * unit_y + y * unit_x,
                    )
                else:
                    raise RuntimeError(f"orbit guard exhausted for K={k}")


def run(max_k: int, max_n: int) -> dict:
    started = time.perf_counter()
    candidates: set[tuple[int, int, int]] = set()
    by_k: Counter[int] = Counter()
    digest = hashlib.sha256()
    hits = []

    for k in range(1, max_k + 1):
        # K=1 gives (X-Y)(X+Y)=3 and only n=1.  K=4 is the
        # analytically handled infinite degenerate family.
        if k in (1, 4):
            continue
        root = isqrt(k)
        if root * root == k:
            generated = square_k_candidates(k)
        else:
            generated = nonsquare_k_candidates(k, max_n)
        for n, claimed_r in generated:
            if n > max_n:
                continue
            key = (k, n, claimed_r)
            if key in candidates:
                continue
            if n * n - 1 != k * claimed_r * (claimed_r - 1):
                raise AssertionError(f"invalid Pell candidate: {key}")
            candidates.add(key)
            by_k[k] += 1

    for k, n, claimed_r in sorted(candidates):
        actual_r, factors = square_count(n)
        digest.update(f"{k},{n},{claimed_r},{actual_r}\n".encode("ascii"))
        if actual_r == claimed_r:
            hits.append(
                {
                    "K": k,
                    "n": n,
                    "R": actual_r,
                    "factorization": factors,
                }
            )

    return {
        "status": "NO HITS" if not hits else "HIT FOUND",
        "interpretation": (
            "all generalized-Pell candidates in the stated rectangle were "
            "generated and tested against the multiplicative formula for R"
        ),
        "analytic_exception": (
            "K=4 is not enumerated: it forces R=(n+1)/2 and hence n odd prime"
        ),
        "max_K_inclusive": max_k,
        "max_n_inclusive": max_n,
        "distinct_Pell_candidates": len(candidates),
        "largest_candidate_n": max((n for _, n, _ in candidates), default=None),
        "K_values_with_candidates": len(by_k),
        "candidate_stream_sha256": digest.hexdigest(),
        "hits": hits,
        "elapsed_seconds": time.perf_counter() - started,
        "python": sys.version,
        "sympy": sympy.__version__,
        "platform": platform.platform(),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-k", type=int, default=375)
    parser.add_argument("--max-n", type=int, default=10**18)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run(args.max_k, args.max_n)
    rendered = json.dumps(result, indent=2, sort_keys=True)
    print(rendered)
    if args.output:
        args.output.write_text(rendered + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
