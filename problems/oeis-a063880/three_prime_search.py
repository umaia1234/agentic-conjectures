#!/usr/bin/env python3
"""Exact search for three-prime powerful cores of A063880 (implementation 1).

A core 2^a q^b r^c (a, b, c >= 2, q < r odd primes) solves sigma = 2 sigma*
iff  k*sigma(q^b)*sigma(r^c) = (k+3)*(1+q^b)*(1+r^c)  with k = 2^(a+1) - 1.
For every 2 <= a <= AMAX this script finds ALL such (q, b, r, c) -- no bound on
q, b, r, c is imposed; the finiteness comes from THREE_PRIMES.md, section 4:

* q (the smaller odd prime) lies in [k/3, (2k+4)/3];
* mu_r := u_r/t_r (u = 1+p^e, t = p+...+p^(e-1)) equals k*sigma_q/W_q with
  W_q = 3(q+1) + d*t_q, d = 3q-3-k; mu_r lies in (r-1, r+1/r], so r and c
  are read off from mu_r;
* if d < 0 only b with W_q > 0 matter (W_q decreases in b); if d > 0, mu(b)
  increases strictly to mu_inf = kq/d, and once mu(b) exceeds s_plus (an
  upper bound for the largest attainable mu_r value below mu_inf) no larger b
  can give a solution.

Arithmetic is exact (fractions.Fraction).  The search also re-checks the other
two three-prime families (no factor 2; 2 and 3 both present) by exact nested
monotone bounds, and runs a self-test on synthetic targets with planted
solutions.  An independent integer-only implementation is
three_prime_search_int.py.  (The Lean module proves all three-prime cases;
both scripts are independent cross-checks of Case A for 2 <= a <= AMAX.)
"""

from __future__ import annotations

import argparse
import sys
import time
from fractions import Fraction
from math import isqrt


def primes_between(lo: int, hi: int) -> list[int]:
    """All primes p with lo <= p <= hi (segmented sieve of Eratosthenes)."""
    lo = max(lo, 2)
    if hi < lo:
        return []
    seg = bytearray([1]) * (hi - lo + 1)
    for p in range(2, isqrt(hi) + 1):
        start = max(p * p, -(-lo // p) * p)
        if start <= hi:
            seg[start - lo :: p] = bytearray(len(range(start, hi + 1, p)))
    return [lo + i for i, v in enumerate(seg) if v]


def t_of(p: int, e: int) -> int:
    """t_p(e) = p + p^2 + ... + p^(e-1)."""
    return (p**e - p) // (p - 1)


def sigma_pp(p: int, e: int) -> int:
    """sigma(p^e) = 1 + p + ... + p^e."""
    return (p ** (e + 1) - 1) // (p - 1)


def ratio(p: int, e: int) -> Fraction:
    """Local ratio R(p, e) = sigma(p^e) / (1 + p^e)."""
    return Fraction(sigma_pp(p, e), 1 + p**e)


def s_plus(K: int, q: int, d: int) -> Fraction:
    """Upper bound for max{u_r/t_r < mu_inf : r >= 2, c >= 2} with mu_inf = K q / d.

    u_r/t_r lies in (r-1, r+1/r], so values in (mu_inf - 1, mu_inf) can only
    come from r in {m-1, m, m+1}, m = floor(mu_inf).  Primality of r is not
    tested (this only enlarges the bound, which keeps the stopping rule valid).
    """
    mu_inf = Fraction(K * q, d)
    m = mu_inf.numerator // mu_inf.denominator
    best = mu_inf - 1
    for r in (m - 1, m, m + 1):
        if r < 2:
            continue
        v = Fraction(r * r + 1, r)  # c = 2, the largest value for this r
        if v < mu_inf:
            best = max(best, v)
            continue
        if r - 1 >= mu_inf:
            continue
        c = 3
        while True:  # values decrease to r-1 < mu_inf, so this terminates
            v = r - 1 + Fraction(r + 1, t_of(r, c))
            if v < mu_inf:
                best = max(best, v)
                break
            c += 1
    return best


def solutions_for_q(K: int, M: int, q: int, stats: dict | None = None) -> list[tuple]:
    """All (b, r, c), b, c >= 2, r > q, with K sigma(q^b) sigma(r^c) = M (1+q^b)(1+r^c).

    Requires M > K > 0 and d = (M-K)(q-1) - K != 0.
    """
    m3 = M - K
    d = m3 * (q - 1) - K
    assert d != 0
    mu_inf = Fraction(K * q, d) if d > 0 else None
    bound = s_plus(K, q, d) if d > 0 else None
    out = []
    b = 2
    while True:
        tq = t_of(q, b)
        uq = 1 + q**b
        W = m3 * uq - K * tq
        assert W == m3 * (q + 1) + d * tq
        if W <= 0:
            if d < 0:
                break  # W_q decreases in b when d < 0
            b += 1
            continue
        mu = Fraction(K * (uq + tq), W)
        if d > 0:
            assert mu < mu_inf
        m0 = mu.numerator // mu.denominator
        r = m0  # c = 2: mu = r + 1/r
        if r > q and mu == Fraction(r * r + 1, r):
            out.append((b, r, 2))
        r = m0 + 1  # c >= 3: mu = r - 1 + (r+1)/t_r with t_r >= r + r^2
        frac = mu - m0
        if r > q and frac > 0:
            tr = Fraction(r + 1) / frac
            if tr.denominator == 1:
                y = (r - 1) * tr.numerator + r  # = r^c iff t_r = t_r(c)
                c = 0
                while y % r == 0:
                    y //= r
                    c += 1
                if y == 1 and c >= 3:
                    out.append((b, r, c))
        if stats is not None:
            stats["steps"] += 1
            stats["max_b"] = max(stats["max_b"], b)
        if d > 0 and mu > bound:
            break
        b += 1
    for b, r, c in out:  # exact re-check of every hit
        assert K * sigma_pp(q, b) * sigma_pp(r, c) == M * (1 + q**b) * (1 + r**c)
    return out


def search_two_odd(a: int, stats: dict) -> list[tuple]:
    """All three-prime cores 2^a q^b r^c (q < r odd primes) for this a."""
    k = 2 ** (a + 1) - 1
    hits = []
    for q in primes_between(max(-(-k // 3), 3), (2 * k + 4) // 3):
        stats["q"] += 1
        for b, r, c in solutions_for_q(k, k + 3, q, stats):
            hits.append((a, q, b, r, c))
    return hits


def nested_solve(primes: list[int], target: Fraction) -> list[tuple]:
    """All exponent tuples (each >= 2) with prod R(p_i, e_i) == target.

    R(p, e) increases strictly in e towards p/(p-1); if all exponents were >= E
    with prod R(p_i, E) > target the product would be too large, so some
    exponent is < E; branch on it.  Exact and exhaustive.
    """
    if len(primes) == 1:
        p = primes[0]
        if target >= Fraction(p, p - 1) or target < ratio(p, 2):
            return []
        e = 2
        while ratio(p, e) < target:
            e += 1
        return [(e,)] if ratio(p, e) == target else []
    lim = Fraction(1)
    low = Fraction(1)
    for p in primes:
        lim *= Fraction(p, p - 1)
        low *= ratio(p, 2)
    if target >= lim or target < low:
        return []
    E = 2
    while True:
        prod = Fraction(1)
        for p in primes:
            prod *= ratio(p, E)
        if prod > target:
            break
        E += 1
    sols = set()
    for i, p in enumerate(primes):
        rest = primes[:i] + primes[i + 1 :]
        for e in range(2, E):
            for s in nested_solve(rest, target / ratio(p, e)):
                sols.add(tuple(list(s[:i]) + [e] + list(s[i:])))
    return sorted(sols)


def check_lean_families() -> None:
    """Re-check the two families excluded in Lean (no 2; both 2 and 3)."""
    # Three odd primes p1 < p2 < p3: prod p/(p-1) > 2 forces {3, 5, r}, r <= 13.
    odd = primes_between(3, 50)
    survivors = []
    for i, p1 in enumerate(odd):
        for j in range(i + 1, len(odd)):
            for l in range(j + 1, len(odd)):
                p2, p3 = odd[j], odd[l]
                if Fraction(p1 * p2 * p3, (p1 - 1) * (p2 - 1) * (p3 - 1)) > 2:
                    survivors.append((p1, p2, p3))
    assert survivors == [(3, 5, 7), (3, 5, 11), (3, 5, 13)], survivors
    # (larger p3 only lowers p3/(p3-1), so the scan up to 50 is enough)
    for _, _, r in survivors:
        assert nested_solve([3, 5, r], Fraction(2)) == [], r
    # 2 and 3 in the core: the third prime r >= 5 must satisfy
    # R(2,a) R(3,b) R(r,c) = 2; R(2,a)R(3,b) < 2 forces (a,b) in {(2,2),(2,3)}.
    pairs = [(a, b) for a in range(2, 8) for b in range(2, 8)
             if ratio(2, a) * ratio(3, b) < 2]
    assert pairs == [(2, 2)], pairs  # (2,3) gives exactly 2, i.e. R(r,c) = 1
    assert ratio(2, 2) * ratio(3, 3) == 2
    # R(r,c) = 100/91 would need 91 sigma(r^c) = 100 (1 + r^c), so r | 9.
    assert 2 / (ratio(2, 2) * ratio(3, 2)) == Fraction(100, 91)
    print("Lean-excluded families re-checked: no 2 -> {3,5,r<=13} all empty; "
          "{2,3,r} empty")


def self_test() -> None:
    """Planted solutions of K sigma_q sigma_r = M u_q u_r must be found."""
    planted = 0
    for q0 in (5, 7, 11, 13, 31, 101):
        for r0 in (q0 + 2, q0 + 6, 3 * q0 + 4, q0 * q0 + 2):
            if any(r0 % p == 0 for p in range(2, isqrt(r0) + 1)):
                continue
            for b0 in (2, 3, 4, 5, 7):
                for c0 in (2, 3, 4, 6):
                    t = ratio(q0, b0) * ratio(r0, c0)
                    K, M = t.denominator, t.numerator
                    if (M - K) * (q0 - 1) - K == 0:
                        continue
                    found = solutions_for_q(K, M, q0)
                    assert (b0, r0, c0) in found, (q0, b0, r0, c0, found)
                    # the facts behind the q-range: X = W_q/t_q > 0, X < Y, XY = KM
                    X = (M - K) * Fraction(1 + q0**b0, t_of(q0, b0)) - K
                    Y = (M - K) * Fraction(1 + r0**c0, t_of(r0, c0)) - K
                    assert 0 < X < Y and X * Y == K * M
                    planted += 1
    print(f"self-test: {planted} planted solutions recovered")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--amax", type=int, default=7, help="search 2 <= a <= AMAX")
    ap.add_argument("--skip-self-test", action="store_true")
    args = ap.parse_args()
    if not args.skip_self_test:
        self_test()
        check_lean_families()
    t0 = time.time()
    total = {"q": 0, "steps": 0, "max_b": 0}
    hits = []
    for a in range(2, args.amax + 1):
        st = {"q": 0, "steps": 0, "max_b": 0}
        h = search_two_odd(a, st)
        hits += h
        for key in ("q", "steps"):
            total[key] += st[key]
        total["max_b"] = max(total["max_b"], st["max_b"])
        print(f"a={a:2d}: primes q={st['q']}, (q,b) steps={st['steps']}, "
              f"max b={st['max_b']}, hits={h}  [{time.time() - t0:.1f}s]", flush=True)
    print(f"total: {total['q']} primes q, {total['steps']} (q,b) steps, "
          f"max b = {total['max_b']}")
    if hits:
        print("SOLUTIONS FOUND:", hits)
        return 1
    print(f"no three-prime core 2^a q^b r^c with 2 <= a <= {args.amax}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
