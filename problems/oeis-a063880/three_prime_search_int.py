#!/usr/bin/env python3
"""Exact search for three-prime cores 2^a q^b r^c of A063880 (implementation 2).

Independent re-implementation of three_prime_search.py using integers only
(cross-multiplication instead of fractions.Fraction) and a different way of
reading off the third prime: the required local ratio of r^c is
    R(r, c) = (k+3)(1+q^b) / (k sigma(q^b)) = 1 + 1/mu,
    mu = k sigma(q^b) / ((k+3)(1+q^b) - k sigma(q^b)) = u_r / t_r,
and u_r/t_r (u = 1+r^c, t = r+...+r^(c-1)) is r + 1/r for c = 2 and lies in
(r-1, r-1+1/r] for c >= 3, decreasing in c.  Candidates c >= 3 are found by
walking c upward until u_r/t_r drops to or below mu.

To test the q-range of THREE_PRIMES.md (k/3 <= q <= (2k+4)/3) instead of
trusting it, this implementation scans the wider window
    max(3, floor(k/3) - 6) <= q <= k + 6.
The b-loop stops by the same mechanism as implementation 1 (mu(b) strictly
increases to mu_inf = kq/d when d = 3q-3-k > 0; once it exceeds the largest
attainable u_r/t_r below mu_inf nothing larger works), but that bound is
computed here by an exact scan over r in [m-2, m+2], m = floor(mu_inf).
"""

from __future__ import annotations

import argparse
import sys
import time


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):  # deterministic < 3.3e24
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def geometric(p: int, lo: int, hi: int) -> int:
    """p^lo + p^(lo+1) + ... + p^hi (empty sum = 0)."""
    total, term = 0, p**lo
    for _ in range(lo, hi + 1):
        total += term
        term *= p
    return total


def top_value_below(num: int, den: int, r: int):
    """Largest u_r/t_r (c >= 2) strictly below num/den, as (u, t), or None."""
    if r < 2:
        return None
    c = 2
    while True:
        u, t = 1 + r**c, geometric(r, 1, c - 1)
        if u * den < num * t:  # u/t < num/den; values decrease in c
            return (u, t)
        if (r - 1) * den >= num:  # limit r-1 already >= num/den: never below
            return None
        c += 1


def stop_bound(K: int, q: int, d: int):
    """(N, D) with N/D >= every attainable u_r/t_r lying below mu_inf = Kq/d."""
    num, den = K * q, d
    m = num // den
    best_n, best_d = num - den, den  # mu_inf - 1 (values below it are irrelevant)
    for r in range(m - 2, m + 3):
        v = top_value_below(num, den, r)
        if v is not None and v[0] * best_d > best_n * v[1]:
            best_n, best_d = v
    return best_n, best_d


def scan_q(K: int, M: int, q: int) -> list[tuple]:
    """All (b, r, c, r_is_prime), r > q, with K sigma(q^b) sigma(r^c) = M u_q u_r.

    For the A063880 equation K = k = 2^(a+1) - 1 and M = k + 3.
    """
    hits = []
    d = (M - K) * (q - 1) - K
    if d == 0:
        raise AssertionError("d = 0: for M = K + 3 this would force 3q = k + 3 even")
    if d > 0:
        sn, sd = stop_bound(K, q, d)
    b = 2
    while True:
        u_q = 1 + q**b
        s_q = geometric(q, 0, b)
        num = K * s_q
        den = M * u_q - K * s_q  # = (M-K)(q+1) + d*(q+...+q^(b-1))
        if den <= 0:
            if d < 0:
                break
            b += 1
            continue
        n0 = num // den
        # c = 2: num/den == (r^2+1)/r with r = n0
        r = n0
        if r > q and num * r == den * (r * r + 1):
            hits.append((b, r, 2))
        # c >= 3: num/den == (1+r^c)/(r+...+r^(c-1)) with r = n0 + 1
        r = n0 + 1
        if r > q:
            c = 3
            while True:
                u, t = 1 + r**c, geometric(r, 1, c - 1)
                lhs, rhs = num * t, den * u
                if lhs == rhs:
                    hits.append((b, r, c))
                    break
                if lhs > rhs:  # u/t fell below num/den; it keeps decreasing
                    break
                if (r - 1) * den >= num:
                    break
                c += 1
        if d > 0 and num * sd > sn * den:  # mu(b) > stop bound
            break
        b += 1
    out = []
    for b, r, c in hits:
        lhs = K * geometric(q, 0, b) * geometric(r, 0, c)
        rhs = M * (1 + q**b) * (1 + r**c)
        assert lhs == rhs
        out.append((b, r, c, is_prime(r)))
    return out


def self_test() -> None:
    """Planted solutions (K, M chosen so that a known (q, b, r, c) solves) are found."""
    from math import gcd
    count = 0
    for q0 in (3, 5, 7, 13, 29, 97):
        for r0 in (q0 + 2, q0 + 4, 2 * q0 + 1, 5 * q0 + 2, q0 * q0 + 4):
            if not is_prime(r0):
                continue
            for b0 in (2, 3, 4, 6):
                for c0 in (2, 3, 5, 7):
                    M = geometric(q0, 0, b0) * geometric(r0, 0, c0)
                    K = (1 + q0**b0) * (1 + r0**c0)
                    g = gcd(M, K)
                    M, K = M // g, K // g
                    if (M - K) * (q0 - 1) - K == 0:
                        continue
                    got = scan_q(K, M, q0)
                    assert (b0, r0, c0, True) in got, (q0, b0, r0, c0, got)
                    count += 1
    print(f"self-test: {count} planted solutions recovered")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--amax", type=int, default=7)
    ap.add_argument("--skip-self-test", action="store_true")
    args = ap.parse_args()
    if not args.skip_self_test:
        self_test()
    t0 = time.time()
    found = []
    for a in range(2, args.amax + 1):
        k = 2 ** (a + 1) - 1
        lo, hi = max(3, k // 3 - 6), k + 6
        nq = 0
        for q in range(lo | 1, hi + 1, 2):
            if not is_prime(q):
                continue
            nq += 1
            for b, r, c, rp in scan_q(k, k + 3, q):
                found.append((a, q, b, r, c, rp))
        print(f"a={a:2d}: q in [{lo}, {hi}], {nq} primes, "
              f"hits so far {found}  [{time.time() - t0:.1f}s]", flush=True)
    prime_hits = [h for h in found if h[5]]
    if prime_hits:
        print("SOLUTIONS FOUND:", prime_hits)
        return 1
    print(f"no three-prime core 2^a q^b r^c with 2 <= a <= {args.amax}"
          + (f" (non-prime r hits: {found})" if found else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
