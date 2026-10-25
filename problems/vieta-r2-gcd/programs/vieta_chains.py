#!/usr/bin/env python3
"""Vieta chains for (a + r)/b + (b + r)/a = k, with a, b positive and k an integer.

Evidence only; the Lean module AgenticConjectures/VietaR2Gcd.lean does not use it.

Part 1 (r = 2, Conjecture 4.2 of arXiv:2605.19083v2). Walks every Vieta chain up to the
height bound and checks that each pair has k in {3, 4, 6} and that 2(a+b)/gcd(a,b)^2 lies in
{1, 5}, {2, 3} or {4, 8} for k = 3, 4, 6, with all six values attained.

Part 2 (1 <= r <= max_r). Finds the reduced solutions (a <= b, b^2 <= a^2 + r a) by a search
that runs past the bound a <= 2r, and checks:
  - k >= 3, and reduced solutions satisfy 2(b - a) <= r, a <= 2r and k <= 2r + 2;
  - the chains through the reduced solutions contain every solution with b <= brute, compared
    with a separate enumeration over divisors (every solution has b | a(a + r));
  - m = r(a + b)/gcd(a, b)^2 is an integer dividing r(k + 2);
  - m is 2-periodic along each chain: the pairs (p_n, p_n+1) and (p_n+2, p_n+3) give the same m.
It then prints, for each (r, k), the values {m(a, b), m(a, ka - r - b)} of the reduced solutions,
which by 2-periodicity are all the values on their chains.

Usage: python3 vieta_chains.py [--height H] [--max-r R] [--brute B]
Exit status 1 on any failed check.
"""

import argparse
import math
import sys

ALLOWED_R2 = {3: {1, 5}, 4: {2, 3}, 6: {4, 8}}


def value(r, a, b):
    """r(a + b)/gcd(a, b)^2, which must be an integer."""
    g = math.gcd(a, b)
    q, rem = divmod(r * (a + b), g * g)
    if rem != 0:
        raise AssertionError(f"r={r}: value of ({a}, {b}) is not an integer")
    return q


def is_solution(r, a, b):
    num = a * a + r * a + b * b + r * b
    return num % (a * b) == 0


def k_of(r, a, b):
    return (a * a + r * a + b * b + r * b) // (a * b)


def reduced_solutions(r, a_max):
    """All (a, b, k) with a <= a_max, a <= b and b^2 <= a^2 + r a."""
    out = []
    for a in range(1, a_max + 1):
        b = a
        while b * b <= a * a + r * a:
            if is_solution(r, a, b):
                out.append((a, b, k_of(r, a, b)))
            b += 1
    return out


def chain(r, k, a, b, height):
    """The terms of the chain through the reduced pair (a, b) that are at most height.

    The chain is the two-sided sequence with p_0 = a, p_1 = b and p_(n+1) = k p_n - r - p_(n-1).
    Away from a reduced pair it increases in both directions, so it is cut where a term
    exceeds height. Returns the list of terms in order.
    """
    forward = [a, b]
    while True:
        nxt = k * forward[-1] - r - forward[-2]
        if nxt > height:
            break
        forward.append(nxt)
    backward = []
    prev, cur = b, a
    while True:
        nxt = k * cur - r - prev
        if nxt > height:
            break
        backward.append(nxt)
        prev, cur = cur, nxt
    return backward[::-1] + forward


def check_chain(r, k, terms, fail):
    pairs = []
    for i in range(len(terms) - 1):
        x, y = terms[i], terms[i + 1]
        if x <= 0 or y <= 0 or not is_solution(r, x, y) or k_of(r, x, y) != k:
            fail(f"r={r} k={k}: ({x}, {y}) is not a solution")
            continue
        pairs.append((min(x, y), max(x, y)))
    ms = [value(r, x, y) for x, y in zip(terms, terms[1:])]
    for i in range(len(ms) - 2):
        if ms[i] != ms[i + 2]:
            fail(f"r={r} k={k}: m not 2-periodic at index {i} of {terms[:6]}...")
    for m in ms:
        if (r * (k + 2)) % m != 0:
            fail(f"r={r} k={k}: m={m} does not divide r(k+2)")
    return pairs, set(ms)


def smallest_prime_factors(limit):
    spf = list(range(limit + 1))
    for p in range(2, int(limit ** 0.5) + 1):
        if spf[p] == p:
            for q in range(p * p, limit + 1, p):
                if spf[q] == q:
                    spf[q] = p
    return spf


def factor(n, spf, into):
    while n > 1:
        p = spf[n]
        into[p] = into.get(p, 0) + 1
        n //= p


def divisors_up_to(fact, bound):
    divs = [1]
    for p, e in fact.items():
        divs = [d * p ** i for d in divs for i in range(e + 1) if d * p ** i <= bound]
    return divs


def brute_solutions(r, bound, spf):
    """All (a, b) with a <= b <= bound, using b | a(a + r)."""
    sols = set()
    for a in range(1, bound + 1):
        fact = {}
        factor(a, spf, fact)
        factor(a + r, spf, fact)
        for b in divisors_up_to(fact, bound):
            if b >= a and is_solution(r, a, b):
                sols.add((a, b))
    return sols


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--height", type=int, default=60, help="r = 2 chains up to 10^height")
    ap.add_argument("--max-r", type=int, default=12)
    ap.add_argument("--brute", type=int, default=3000, help="cross-check bound for b")
    args = ap.parse_args()
    failures = []

    def fail(msg):
        failures.append(msg)
        print("FAIL:", msg)

    # Part 1: r = 2.
    height = 10 ** args.height
    seen = {}
    pair_count = 0
    for a, b, k in reduced_solutions(2, 50):
        pairs, ms = check_chain(2, k, chain(2, k, a, b, height), fail)
        pair_count += len(set(pairs))
        seen.setdefault(k, set()).update(ms)
    print(f"r=2: chains up to 10^{args.height}: {pair_count} solutions (a <= b)")
    for k in sorted(seen):
        print(f"  k={k}: values {sorted(seen[k])}")
    if seen != ALLOWED_R2:
        fail(f"r=2: values {seen} differ from Conjecture 4.2")

    # Part 2: general r.
    spf = smallest_prime_factors(args.brute + args.max_r)
    print(f"general r <= {args.max_r}; chains compared with divisor enumeration for b <= "
          f"{args.brute}")
    for r in range(1, args.max_r + 1):
        a_max = 4 * r + 4
        reduced = reduced_solutions(r, a_max)
        for a, b, k in reduced:
            if not (k >= 3 and 2 * (b - a) <= r and a <= 2 * r and k <= 2 * r + 2):
                fail(f"r={r}: reduced ({a}, {b}) with k={k} breaks a bound")
        chain_sols = set()
        values = {}
        for a, b, k in reduced:
            pairs, ms = check_chain(r, k, chain(r, k, a, b, args.brute), fail)
            chain_sols.update(pairs)
            w = {value(r, a, b), value(r, a, k * a - r - b)}
            if not ms <= w:
                fail(f"r={r} k={k}: chain values {ms} not in {w}")
            values.setdefault(k, set()).update(w)
        brute = brute_solutions(r, args.brute, spf)
        if brute != chain_sols:
            fail(f"r={r}: chains and divisor enumeration differ: {sorted(brute ^ chain_sols)[:5]}")
        for a, b in brute:
            k = k_of(r, a, b)
            if value(r, a, b) not in values.get(k, set()):
                fail(f"r={r}: value of ({a}, {b}) missing from the reduced table")
        table = "; ".join(f"k={k}: {sorted(values[k])}" for k in sorted(values))
        print(f"r={r:2d}: {len(reduced)} reduced, {len(brute)} solutions with b <= {args.brute}; "
              f"{table}")

    print(f"failures: {len(failures)}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
