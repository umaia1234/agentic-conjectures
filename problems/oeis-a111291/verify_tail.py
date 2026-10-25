#!/usr/bin/env python3
"""Rigorous numerical step of the analytic tail: pi(n) < 2 T(n) for every integer n >= 10^12.

The argument is written out in DETAILS.md ("The analytic tail"). For a set G of p-generators
(integers d with 2 tau(d) | d) it shows, for real x >= max(e^2, 599 max G),

    2 T(x) - pi(x) > f(x) - 2B,  f(x) = x ((2A - 1)/ln x + (A + 2 A1 - 3/2)/ln^2 x),

where A = sum 1/d, A1 = sum (ln d)/d, B = sum pi(P(d)) over d in G and P(d) is the largest prime
factor of d; f is increasing once both coefficients are positive. This script takes G = all
p-generators d <= 28653696 (the set used by Zelinsky, Theorem 8), and

  * re-checks every generator from the factorisation printed by the `generators` program
    (product, primality of the factors, 2 tau(d) | d, and strictly increasing d, so that no
    generator is counted twice), so that program is not trusted;
  * computes B exactly and lower bounds for A and A1 in exact integer arithmetic (fixed point
    with floors, ln d bounded below by k ln 2 + 2 (s + s^3/3 + s^5/5 + s^7/7), d = 2^k z,
    s = (z - 1)/(z + 1), ln 2 bounded below by a partial sum of sum 1/(j 2^j));
  * checks f(10^12) > 2B with ln(10^12) replaced by the upper bound 28 (exp(28) > 10^12 is
    checked with a partial sum of the exponential series), and 10^12 >= 599 max G.

Usage: python3 verify_tail.py PATH_TO_generators_BINARY
"""
import subprocess
import sys
from array import array
from fractions import Fraction
from itertools import accumulate

D = 28653696
X = 10**12
L_HI = 28
S = 1 << 100  # fixed-point scale


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    out = subprocess.run([sys.argv[1], str(D)], capture_output=True, text=True, check=True).stdout

    lim = D // 4  # every prime factor of a generator d <= D is <= d/4
    isprime = bytearray([1]) * (lim + 1)
    isprime[0] = isprime[1] = 0
    for i in range(2, int(lim**0.5) + 1):
        if isprime[i]:
            isprime[i * i :: i] = bytearray(len(range(i * i, lim + 1, i)))
    pi = array("I", accumulate(isprime))

    ln2 = sum(S // (j << j) for j in range(1, 160))  # <= S ln 2
    count = a_fp = a1_fp = B = dmax = 0
    for line in out.splitlines():
        v = list(map(int, line.split()))
        d, fac = v[0], v[1:]
        assert d > dmax, line  # strictly increasing, so every d is counted once
        assert len(fac) >= 2 and len(fac) % 2 == 0, line
        prod, tau, prev = 1, 1, 1
        for q, e in zip(fac[0::2], fac[1::2]):
            assert q > prev and e >= 1 and q <= lim and isprime[q], line
            prod *= q**e
            tau *= e + 1
            prev = q
        assert prod == d and d <= D and d % (2 * tau) == 0, line
        count += 1
        dmax = d
        B += pi[prev]  # prev = largest prime factor P(d)
        a_fp += S // d
        k = d.bit_length() - 1
        u = 1 << k
        s = S * (d - u) // (d + u)
        s2 = s * s // S
        s3 = s * s2 // S
        s5 = s3 * s2 // S
        s7 = s5 * s2 // S
        lnd = k * ln2 + 2 * (s + s3 // 3 + s5 // 5 + s7 // 7)  # <= S ln d
        a1_fp += lnd // d

    A = Fraction(a_fp, S)
    A1 = Fraction(a1_fp, S)
    c1 = 2 * A - 1
    c2 = A + 2 * A1 - Fraction(3, 2)
    exp_lo = sum(Fraction(L_HI**j, 1) / Fraction(_fact(j)) for j in range(0, 120))
    f_lo = X * (c1 / L_HI + c2 / L_HI**2)
    # Every printed bound is rounded down; the verdict below uses the exact fractions.
    print(f"generators d <= {D}: {count} (max {dmax}), strictly increasing")
    print(f"A  >= {_floor_dec(A, 12)}")
    print(f"A1 >= {_floor_dec(A1, 12)}")
    print(f"B   = {B}")
    print(f"exp({L_HI}) >= {_floor_dec(exp_lo, 0)} > X = {X}")
    print(f"f(X) with ln X <= {L_HI}: f(X) >= {_floor_dec(f_lo, 0)}; 2B = {2 * B}; "
          f"ratio >= {_floor_dec(f_lo / (2 * B), 6)}")
    ok = (c1 > 0 and c2 > 0 and exp_lo > X and X >= 599 * dmax and f_lo > 2 * B)
    print(("TAIL VERIFIED" if ok else "TAIL FAILED") + f": pi(n) < 2T(n) for all n >= {X}")
    return 0 if ok else 1


def _floor_dec(q: Fraction, digits: int) -> str:
    """The decimal expansion of q >= 0, truncated (rounded down) to `digits` places."""
    n = q.numerator * 10**digits // q.denominator
    if digits == 0:
        return str(n)
    return f"{n // 10**digits}.{n % 10**digits:0{digits}d}"


def _fact(n: int) -> int:
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r


if __name__ == "__main__":
    sys.exit(main())
