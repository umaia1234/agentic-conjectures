#!/usr/bin/env python3
"""Standard-library re-check for OEIS A135508 (McEachen's conjecture).

1. Evaluates the upstream definitions literally with big integers,
     x(0) = 0, x(1) = 1, x(n+1) = 2 x(n) + lcm(x(n), n+1)  (n >= 1),
     a(0) = 0, a(n) = x(n+1) // x(n) - 2 (truncated at 0)   (n >= 1),
   for n <= --literal, and compares with the upstream test values and the
   OEIS DATA line.
2. Re-computes a(1..N) for N = --limit with exponent bookkeeping, using
   a(n) = (n+1)/gcd(x(n), n+1) and x(n+1) = x(n)(a(n)+2) (Lean: a_eq,
   x_succ_eq), checks it against step 1 on the common range, and checks
     C1 every a(n) is 1 or a prime;
     C2 a(p-1) = p for every prime p <= N+1 with p-2 not prime;
     C3 a(p-1) = p  <=>  gcd(x(p-3), p-2) > 1 for primes 5 <= p <= N+1;
     C4 minFac(p-2) | x(p-3) for every prime p <= N+1 with p-2 composite;
     C5 F(r) <= r^2-1 for every prime r with r^2 <= N+1, where
        F(r) = min{n : r | x(n)}.
   It also checks that a(n) = 2 exactly for n = 2*4^k - 1 (the OEIS formula
   "a(2*4^k) = 2" uses an index shifted by one).
3. Prints the fingerprint of a(1..N) and, for N = 10^6, compares it with the
   value printed by a135508_scan.cpp and a135508_scan_numba.py.
4. Checks that the certificate lists in AgenticConjectures/OeisA135508.lean
   are what their docstrings say: smallCerts = [(r, F(r)) : r prime < 211]
   and largePrimes = the primes in [211, 1009), each with F(r) <= 42611.
   (The Lean kernel re-checks every divisibility itself; this only confirms
   that the listed indices are the first-entry indices.)

Usage: python3 a135508_check.py [--limit N] [--literal L]
"""
import argparse
import math
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent.parent / "AgenticConjectures" / "OeisA135508.lean"

# OEIS A135508 DATA line (terms a(1..92)), https://oeis.org/A135508
OEIS_DATA = [
    2, 3, 1, 1, 1, 7, 2, 1, 1, 11, 1, 1, 7, 1, 1, 17, 1, 1, 1, 7, 11, 23, 1, 1, 1, 1, 7, 29, 1, 1,
    2, 11, 17, 7, 1, 37, 1, 1, 1, 41, 7, 1, 11, 1, 23, 47, 1, 1, 1, 17, 1, 53, 1, 1, 1, 1, 29, 59,
    1, 1, 1, 1, 1, 1, 1, 67, 17, 1, 1, 71, 1, 1, 37, 1, 1, 1, 1, 79, 1, 1, 41, 83, 1, 1, 1, 29, 1,
    89, 1, 1, 1, 1,
]
UPSTREAM_TESTS = {0: 0, 1: 2, 2: 3, 3: 1, 4: 1}
FINGERPRINT_1E6 = (792392, 10, 51850660742, 0x040A897747DCB8C2)


def literal_a(limit):
    """a(0..limit) straight from the upstream definitions."""
    xs = [0, 1]
    for n in range(1, limit + 1):
        xn = xs[n]
        xs.append(2 * xn + xn * (n + 1) // math.gcd(xn, n + 1))
    return [0] + [max(xs[n + 1] // xs[n] - 2, 0) for n in range(1, limit + 1)]


def spf_table(m):
    spf = list(range(m + 1))
    for p in range(2, math.isqrt(m) + 1):
        if spf[p] == p:
            for j in range(p * p, m + 1, p):
                if spf[j] == j:
                    spf[j] = p
    return spf


def factor(c, spf):
    out = []
    while c > 1:
        q = spf[c]
        e = 0
        while c % q == 0:
            c //= q
            e += 1
        out.append((q, e))
    return out


def scan(N):
    """Exponent bookkeeping for a(1..N); returns (a list, F dict, report)."""
    spf = spf_table(N + 4)
    is_prime = lambda c: c >= 2 and spf[c] == c  # noqa: E731
    v = {}
    F = {}
    a = [0] * (N + 1)
    fails = {k: 0 for k in ("C1", "C2", "C3", "C4", "C5")}
    nconj = 0
    for n in range(1, N + 1):
        m = n + 1
        fac = factor(m, spf)
        an = 1
        deficient = 0
        for q, e in fac:
            d = e - min(e, v.get(q, 0))
            an *= q ** d
            deficient += d
        a[n] = an
        if deficient >= 2:
            fails["C1"] += 1
        if m >= 4 and m + 2 <= N + 1 and is_prime(m + 2) and not is_prime(m):
            if v.get(fac[0][0], 0) == 0:  # fac[0][0] = minFac(m)
                fails["C4"] += 1
        if is_prime(m):
            p = m
            if not (p >= 4 and is_prime(p - 2)):
                nconj += 1
                if an != p:
                    fails["C2"] += 1
            if p >= 5 and (an == p) != (a[p - 3] != p - 2):
                fails["C3"] += 1
        for q, e in factor(an + 2, spf):
            if v.get(q, 0) == 0:
                F[q] = n + 1
            v[q] = v.get(q, 0) + e
    r = 2
    while r * r <= N + 1:
        if is_prime(r) and not (r in F and F[r] <= r * r - 1):
            fails["C5"] += 1
        r += 1
    return a, F, fails, nconj, is_prime


def fingerprint(a, N):
    h = 0
    for n in range(1, N + 1):
        h = (h * 1000003 + a[n]) % (1 << 64)
    ones = sum(1 for n in range(1, N + 1) if a[n] == 1)
    twos = sum(1 for n in range(1, N + 1) if a[n] == 2)
    return ones, twos, sum(a[1:N + 1]), h


def lean_lists():
    text = LEAN.read_text()
    small = re.search(r"def smallCerts : List \(ℕ × ℕ\) :=\s*\[(.*?)\]\n", text, re.S)
    large = re.search(r"def largePrimes : List ℕ :=\s*\[(.*?)\]\n", text, re.S)
    pairs = [(int(r), int(c)) for r, c in re.findall(r"\((\d+), (\d+)\)", small.group(1))]
    primes = [int(t) for t in re.findall(r"\d+", large.group(1))]
    return pairs, primes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=10**6)
    ap.add_argument("--literal", type=int, default=5000)
    args = ap.parse_args()
    N, L = args.limit, args.literal
    ok = True

    lit = literal_a(max(L, len(OEIS_DATA)))
    t1 = all(lit[k] == v for k, v in UPSTREAM_TESTS.items())
    t2 = lit[1:len(OEIS_DATA) + 1] == OEIS_DATA
    print(f"literal definition: a(0..{len(lit) - 1}) computed; upstream tests {t1}; "
          f"OEIS DATA a(1..{len(OEIS_DATA)}) {t2}")
    ok &= t1 and t2

    a, F, fails, nconj, is_prime = scan(N)
    common = min(N, len(lit) - 1)
    t3 = a[1:common + 1] == lit[1:common + 1]
    print(f"bookkeeping scan to N={N}: agrees with the literal definition on 1..{common}: {t3}")
    ok &= t3
    print(f"primes p<=N+1 with p-2 not prime: {nconj}")
    print(" ".join(f"{k} fails={v}" for k, v in fails.items()))
    ok &= not any(fails.values())

    twos = [n for n in range(1, N + 1) if a[n] == 2]
    t7 = twos == [2 * 4**k - 1 for k in range(40) if 2 * 4**k - 1 <= N]
    print(f"a(n) = 2 exactly at n = 2*4^k - 1 (n <= N): {t7}")
    ok &= t7

    fp = fingerprint(a, N)
    print(f"fingerprint: count_a1={fp[0]} count_a2={fp[1]} sum_a={fp[2]} hash={fp[3]:016x}")
    if N == 10**6:
        t4 = fp == FINGERPRINT_1E6
        print(f"fingerprint equals the C++/numba value for N=10^6: {t4}")
        ok &= t4

    if N >= 42611:
        pairs, primes = lean_lists()
        want_small = [(r, F[r]) for r in range(2, 211) if is_prime(r)]
        want_large = [r for r in range(211, 1009) if is_prime(r)]
        t5 = pairs == want_small
        t6 = primes == want_large and max(F[r] for r in primes) == 42611
        print(f"Lean smallCerts = first-entry indices of the primes < 211: {t5}")
        print(f"Lean largePrimes = primes in [211, 1009), max F = 42611: {t6}")
        ok &= t5 and t6

    print("RESULT", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
