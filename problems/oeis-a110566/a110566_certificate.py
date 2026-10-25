#!/usr/bin/env python3
"""Exact numerical cross-check for the OEIS A110566 refutation.

The refutation itself is the Lean theorem
``AgenticConjectures.OeisA110566.not_statement``; this script does not replace
it and is not used by it.  It re-checks, with exact integer and rational
arithmetic from the Python standard library only:

1. the ten reduced fractions H_n (n = 2, 6, 7, 8, 21, 22, 23, 66, 67, 68)
   that the Lean proof states explicitly, and their 3-adic valuations;
2. the 90 published OEIS DATA terms a(1..90);
3. for 1 <= n <= --gcd-limit, that the definition a(n) = lcm(1..n)/den(H_n)
   (computed with fractions.Fraction) agrees with the independent formula
   a(n) = gcd(L, L*H_n) of Franz Vrabec (computed with unreduced integers);
4. for 1 <= n <= --limit, with H_n = S/L, L = lcm(1..n) and k = floor(log_3 n):
   v_3(L) = k, v_3(a(n)) = min(v_3(S), v_3(L)) <= 3, the set
   {n : v_3(H_n) > 0} is {2, 7, 22}, and the recursion
   v_3(H_n) = v_3(H_{floor(n/3)}) - 1 holds whenever n >= 3 and
   floor(n/3) is not in {2, 7, 22} (the step lemma of the Lean proof).

Exit status 0 means every check passed.
"""

from __future__ import annotations

import argparse
import math
import sys
import time
from fractions import Fraction

# Reduced fractions H_n = N/D used verbatim in AgenticConjectures/OeisA110566.lean.
# For n = 2, 7, 22 the Lean file writes the numerator as 3 * N'.
LEAN_BASE = {
    2: (3, 2),
    6: (49, 20),
    7: (3 * 121, 140),
    8: (761, 280),
    21: (18858053, 5173168),
    22: (3 * 6364399, 5173168),
    23: (444316699, 118982864),
    66: (209060999005535159677640233, 43787662374178602500420800),
    67: (14050874595745034300902316411, 2933773379069966367528193600),
    68: (14094018321907827923954201611, 2933773379069966367528193600),
}
LEAN_VALUATION = {2: 1, 6: 0, 7: 1, 8: 0, 21: 0, 22: 1, 23: 0, 66: 0, 67: 0, 68: 0}

# OEIS A110566 DATA section (revision #39, terms a(1..90)).
OEIS_DATA = [
    1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 15, 45, 45, 45, 15, 3, 3,
    1, 1, 1, 1, 1, 1, 11, 11, 11, 11, 11, 11, 11, 11, 11, 77, 77, 7, 7, 7, 7, 7, 1, 1,
    1, 1, 1, 3, 3, 3, 3, 3, 3, 3, 3, 3, 9, 9, 9, 27, 27, 27, 9, 9, 9, 3, 3, 3, 3, 3,
    33, 33, 33, 33, 11, 11, 11, 11, 11, 11, 11, 1, 1, 1,
]

J3 = {2, 7, 22}


def v3(x: int) -> int:
    """3-adic valuation of a nonzero integer."""
    if x == 0:
        raise ValueError("v3(0) is undefined")
    x = abs(x)
    count = 0
    while x % 3 == 0:
        x //= 3
        count += 1
    return count


def floor_log3(n: int) -> int:
    k = 0
    while 3 ** (k + 1) <= n:
        k += 1
    return k


def check(condition: bool, message: str) -> None:
    if not condition:
        print("FAIL:", message)
        sys.exit(1)


def check_lean_base() -> None:
    h = Fraction(0)
    for n in range(1, 69):
        h += Fraction(1, n)
        if n in LEAN_BASE:
            num, den = LEAN_BASE[n]
            check(Fraction(num, den) == h, f"H_{n} differs from the Lean constant")
            check(math.gcd(num, den) == 1, f"Lean constant for H_{n} is not reduced")
            val = v3(num) - v3(den)
            check(val == LEAN_VALUATION[n], f"v3(H_{n}) = {val}, expected {LEAN_VALUATION[n]}")
    print("Lean base fractions H_n and their 3-adic valuations: OK (10 values)")


def check_definition(gcd_limit: int) -> None:
    lcm_value = 1
    harmonic = Fraction(0)
    scaled = 0  # lcm(1..n) * H_n as an integer, updated without reduction
    for n in range(1, gcd_limit + 1):
        new_lcm = math.lcm(lcm_value, n)
        scaled = scaled * (new_lcm // lcm_value) + new_lcm // n
        lcm_value = new_lcm
        harmonic += Fraction(1, n)
        check(lcm_value % harmonic.denominator == 0, f"den(H_{n}) does not divide lcm")
        by_definition = lcm_value // harmonic.denominator
        by_gcd = math.gcd(lcm_value, scaled)
        check(by_definition == by_gcd, f"definition and gcd formula differ at n={n}")
        if n <= len(OEIS_DATA):
            check(by_definition == OEIS_DATA[n - 1], f"OEIS DATA mismatch at n={n}")
    print(f"definition = gcd formula for n <= {gcd_limit}; OEIS DATA a(1..90): OK")


def check_valuations(limit: int) -> None:
    lcm_value = 1
    scaled = 0
    val_h = {}
    worst = 0
    positive = []
    for n in range(1, limit + 1):
        new_lcm = math.lcm(lcm_value, n)
        scaled = scaled * (new_lcm // lcm_value) + new_lcm // n
        lcm_value = new_lcm
        k = floor_log3(n)
        vs = v3(scaled)
        vl = v3(lcm_value)
        check(vl == k, f"v3(lcm(1..{n})) = {vl} != floor(log3 n) = {k}")
        val_h[n] = vs - vl
        val_a = min(vs, vl)
        check(val_a <= 3, f"v3(a({n})) = {val_a} > 3")
        check(k + val_h[n] <= 3, f"v3(H_{n}) + floor(log3 n) > 3 at n={n}")
        worst = max(worst, val_a)
        if val_h[n] > 0:
            positive.append(n)
        if n >= 3 and n // 3 not in J3:
            check(val_h[n] == val_h[n // 3] - 1, f"recursion fails at n={n}")
    check(set(positive) == J3, f"{{n <= {limit} : v3(H_n) > 0}} = {positive}")
    print(f"n <= {limit}: max v3(a(n)) = {worst}; v3(H_n) > 0 exactly for n in {positive}; "
          "step recursion OK")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--gcd-limit", type=int, default=3000)
    parser.add_argument("--limit", type=int, default=30000)
    args = parser.parse_args()
    start = time.perf_counter()
    check_lean_base()
    check_definition(max(args.gcd_limit, len(OEIS_DATA)))
    check_valuations(args.limit)
    print(f"all checks passed in {time.perf_counter() - start:.1f} s")


if __name__ == "__main__":
    main()
