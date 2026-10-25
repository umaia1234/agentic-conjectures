#!/usr/bin/env python3
"""Admissible 9-compressions for Legendre pairs of length L = 9*P invariant under x -> 4x (mod 9).

For a Legendre pair (A, B) of length L with sum 1, the 9-compressions
a_r = sum_{x = r mod 9} A(x), b_r (r in Z/9) satisfy exactly:
  a_r, b_r == L/9 (mod 2), |a_r|, |b_r| <= L/9, sum(a) = sum(b) = 1,
  PAF_a(s) + PAF_b(s) = -2 L/9 for s = 1..8.
If the multiplier group contains an element = 4 or 7 (mod 9), then a and b are constant on the
classes {1,4,7} and {2,5,8}: a = (a0, p, q, a3, p, q, a6, p, q).  This script lists every such a
that has a partner b ("admissible"), using two independent methods that must agree:

  method 1: prefilter by the exact Eisenstein-norm bounds PSD_a(1) = N(a0, a3, a6) <= 2L+2 and
            PSD_a(3) = N(a0+a3+a6, 3p, 3q) <= 2L+2 (N(x,y,z) = x^2+y^2+z^2-xy-yz-zx), then match
            exact PAF vectors through a dictionary;
  method 2: no prefilter; all vectors, PAF computed by a different loop, matching by sorting.

Usage: python3 comp9_pairs.py [P] [out_file]      (default P = 37)
Pure standard library; exact integer arithmetic only.
"""
import sys
from bisect import bisect_left


def norm3(x, y, z):
    return x * x + y * y + z * z - x * y - y * z - z * x


def method1(L):
    q9 = L // 9
    vals = range(-q9, q9 + 1, 2)
    table = {}
    for a0 in vals:
        for a3 in vals:
            for a6 in vals:
                if norm3(a0, a3, a6) > 2 * L + 2:
                    continue
                u = a0 + a3 + a6
                for p in vals:
                    r = 1 - u - 3 * p
                    if r % 3:
                        continue
                    q = r // 3
                    if abs(q) > q9 or (q - q9) % 2:
                        continue
                    if norm3(u, 3 * p, 3 * q) > 2 * L + 2:
                        continue
                    a = (a0, p, q, a3, p, q, a6, p, q)
                    key = tuple(sum(a[i] * a[(i + s) % 9] for i in range(9)) for s in range(1, 9))
                    table.setdefault(key, []).append(a)
    lam = -2 * q9
    adm = set()
    for key, lst in table.items():
        if tuple(lam - v for v in key) in table:
            adm.update(lst)
    return adm


def method2(L):
    q9 = L // 9
    vals = list(range(-q9, q9 + 1, 2))
    recs = []
    for a0 in vals:
        for a3 in vals:
            for a6 in vals:
                for p in vals:
                    r = 1 - (a0 + a3 + a6) - 3 * p
                    if r % 3:
                        continue
                    q = r // 3
                    if q not in vals:
                        continue
                    a = [a0, p, q, a3, p, q, a6, p, q]
                    paf = []
                    for s in range(1, 9):
                        acc = 0
                        for i in range(9):
                            j = i + s
                            if j >= 9:
                                j -= 9
                            acc += a[i] * a[j]
                        paf.append(acc)
                    recs.append((tuple(paf), tuple(a)))
    recs.sort()
    keys = [k for k, _ in recs]
    lam = -2 * q9
    adm = set()
    for k, a in recs:
        w = tuple(lam - v for v in k)
        i = bisect_left(keys, w)
        if i < len(keys) and keys[i] == w:
            adm.add(a)
    return adm


def main():
    P = int(sys.argv[1]) if len(sys.argv) > 1 else 37
    out = sys.argv[2] if len(sys.argv) > 2 else None
    L = 9 * P
    m1 = method1(L)
    m2 = method2(L)
    print(f"L={L}: admissible <4 mod 9>-invariant 9-compressions: method1={len(m1)} method2={len(m2)}")
    if m1 != m2:
        print("MISMATCH between methods")
        sys.exit(1)
    if out:
        with open(out, "w") as f:
            for a in sorted(m1):
                f.write(" ".join(map(str, a)) + "\n")
    print("OK")


if __name__ == "__main__":
    main()
