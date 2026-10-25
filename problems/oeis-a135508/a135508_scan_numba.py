#!/usr/bin/env python3
"""Independent second scan for OEIS A135508 (numba; not run in CI).

Written separately from a135508_scan.cpp, with a different sieve and data
layout, to re-check the same claims to the same bound:

* least prime factors come from a linear sieve over odd numbers (uint32);
* exponents v_q(x(n)) are stored exactly (int64) for q < 65536, and only as a
  membership flag for larger primes, whose exponent in any m <= 4e9 is <= 1.

It uses a(n) = (n+1)/gcd(x(n), n+1) and x(n+1) = x(n)*(a(n)+2) (proved in
AgenticConjectures/OeisA135508.lean as a_eq / x_succ_eq) and checks, for
1 <= n <= N:

  C1 every a(n) is 1 or a prime;
  C2 a(p-1) = p for every prime p <= N+1 with p-2 not prime (the conjecture);
  C3 a(p-1) = p  <=>  a(p-3) != p-2, for primes 5 <= p <= N+1;
  C4 minFac(p-2) | x(p-3) for every prime p <= N+1 with p-2 composite;
  C5 F(r) <= r^2-1 for every prime r with r^2 <= N+1, F(r) = min{n : r | x(n)}.

It prints the same fingerprint line as the C++ scanner.

Usage: python3 a135508_scan_numba.py N     (needs numpy and numba)
"""
import sys
import time

import numpy as np
from numba import njit

SMALL = 65536


@njit(cache=False)
def odd_lpf_linear(M):
    """lpf[k] = least prime factor of 2k+1 (k >= 1), by a linear sieve."""
    size = M // 2 + 1
    lpf = np.zeros(size, dtype=np.uint32)
    primes = np.zeros(size // 2 + 16, dtype=np.uint32)
    np_ = 0
    for k in range(1, size):
        i = 2 * k + 1
        if i > M:
            break
        if lpf[k] == 0:
            lpf[k] = i
            primes[np_] = i
            np_ += 1
        li = lpf[k]
        for j in range(np_):
            p = primes[j]
            if p > li or i * p > M:
                break
            lpf[(i * p) >> 1] = p
    return lpf


@njit(cache=False)
def lpf_of(c, lpf):
    if c % 2 == 0:
        return 2
    return np.int64(lpf[c >> 1])


@njit(cache=False)
def prime_q(c, lpf):
    if c < 2:
        return False
    return lpf_of(c, lpf) == c


@njit(cache=False)
def scan(N, lpf):
    vsmall = np.zeros(SMALL, dtype=np.int64)
    member = np.zeros((N + 4) // 2 + 1, dtype=np.bool_)
    first = np.zeros(SMALL, dtype=np.int64)
    fails = np.zeros(6, dtype=np.int64)
    cnt1 = 0
    cnt2 = 0
    sum_a = 0
    h = np.uint64(0)
    mult = np.uint64(1000003)
    nconj = 0
    twin_hits = 0
    a_m1 = 0
    a_m2 = 0
    for n in range(1, N + 1):
        m = n + 1
        c = m
        a = 1
        nf = 0
        smallest_ok = False
        firstq = True
        while c > 1:
            q = lpf_of(c, lpf)
            e = 0
            while c % q == 0:
                c //= q
                e += 1
            if q < SMALL:
                v = vsmall[q]
            else:
                v = 1 if member[q >> 1] else 0
            if firstq:
                smallest_ok = v > 0
                firstq = False
            if e > v:
                for _ in range(e - v):
                    a *= q
                nf += e - v
        if nf >= 2:
            fails[1] += 1
        # C4 at m = p - 2
        if m >= 4 and m + 2 <= N + 1 and prime_q(m + 2, lpf) and not prime_q(m, lpf):
            if not smallest_ok:
                fails[4] += 1
        if prime_q(m, lpf):
            p = m
            pm2_prime = p >= 4 and prime_q(p - 2, lpf)
            if not pm2_prime:
                nconj += 1
                if a != p:
                    fails[2] += 1
            elif a == p:
                twin_hits += 1
            if p >= 5:
                if (a == p) != (a_m2 != p - 2):
                    fails[3] += 1
        if a == 1:
            cnt1 += 1
        if a == 2:
            cnt2 += 1
        sum_a += a
        h = h * mult + np.uint64(a)
        # x(n+1) = x(n) * (a + 2)
        c = a + 2
        while c > 1:
            q = lpf_of(c, lpf)
            e = 0
            while c % q == 0:
                c //= q
                e += 1
            if q < SMALL:
                if vsmall[q] == 0:
                    first[q] = n + 1
                vsmall[q] += e
            else:
                member[q >> 1] = True
        a_m2 = a_m1
        a_m1 = a
    # C5
    r = 2
    nr = 0
    while r * r <= N + 1:
        if prime_q(r, lpf):
            nr += 1
            if first[r] == 0 or first[r] > r * r - 1:
                fails[5] += 1
        r += 1
    return cnt1, cnt2, sum_a, h, nconj, twin_hits, nr, fails


def main():
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    N = int(sys.argv[1])
    if not 10 <= N <= 4_000_000_000:
        print("N must lie in [10, 4000000000]")
        return 2
    t0 = time.time()
    lpf = odd_lpf_linear(N + 4)
    t1 = time.time()
    cnt1, cnt2, sum_a, h, nconj, twin_hits, nr, fails = scan(N, lpf)
    t2 = time.time()
    print(f"N={N}")
    print(f"fingerprint: count_a1={cnt1} count_a2={cnt2} sum_a={sum_a} hash={int(h):016x}")
    print(f"primes p<=N+1 with p-2 not prime: {nconj}")
    print(f"primes p<=N+1 with p-2 prime and a(p-1)=p: {twin_hits}")
    print(f"C5 range: {nr} primes r with r^2<=N+1")
    print(f"C1 fails={fails[1]} C2 fails={fails[2]} C3 fails={fails[3]} "
          f"C4 fails={fails[4]} C5 fails={fails[5]}")
    print(f"timing: sieve {t1 - t0:.1f}s, scan {t2 - t1:.1f}s")
    ok = int(fails.sum()) == 0
    print("RESULT", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
