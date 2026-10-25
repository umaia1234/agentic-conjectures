"""Direct enumeration of all crystal factorizations n = a*b <= X (cross-check, standard library).

Unlike crystal_search.c and crystal_exact.py, this check does not use the classification.  For a
crystal with a <= b put u = (a + 1) / 2 and v = (b + 1) / 2; Proposition 1 of the paper gives
v | (u - 1)^2 (Lean: `isCrystal_iff_uv`).  For every u >= 2 with (2u - 1)^2 <= X and every divisor
v >= u of (u - 1)^2 with (2u - 1)(2v - 1) <= X, the script tests the original definition:
n = ab odd, a, b > 1 and 2(a + 1)(b + 1) | (a + b)^2 + (ab + 1)^2.

It then sorts the crystals into the classes of the two searches, using
k = (a + b)^2 / ((a + 1)(b + 1)) and the chain index j (the number of Vieta descent steps
(x, y) -> ((x - 1)^2 / y, x), x <= y, that reach a pair containing 1), and prints the same summary
lines, so that the outputs can be compared line by line:
F3 = k = 3, F4 = k = 4, F1 = (k >= 5, j = 1), S = (k >= 5, j >= 2).
"""

import argparse
import sys
import time
from math import isqrt


def is_crystal(a, b):
    n = a * b
    return (n % 2 == 1 and a > 1 and b > 1
            and ((a + b) ** 2 + (n + 1) ** 2) % (2 * (a + 1) * (b + 1)) == 0)


def chain_index(u, v):
    """Number of descent steps from {u, v} on (x + y - 1)^2 = kxy to a pair containing 1."""
    x, y = min(u, v), max(u, v)
    j = 0
    while x > 1:
        q, r = divmod((x - 1) ** 2, y)
        if r:
            sys.exit(f"descent fails at {(u, v)}")
        x, y = q, x
        j += 1
    return j


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("X", help="bound: integer or 1eNN")
    args = ap.parse_args()
    X = 10 ** int(args.X[2:]) if args.X.startswith("1e") else int(args.X)
    t0 = time.time()

    umax = (isqrt(X) + 1) // 2           # a = 2u - 1 <= sqrt(X)
    spf = list(range(umax + 1))          # smallest prime factor sieve for u - 1 <= umax
    for p in range(2, isqrt(umax) + 1):
        if spf[p] == p:
            for q in range(p * p, umax + 1, p):
                if spf[q] == q:
                    spf[q] = p

    crystals = []                        # (n, a, b) with a <= b
    for u in range(2, umax + 1):
        a = 2 * u - 1
        if a * a > X:
            break
        vmax = (X // a + 1) // 2         # (2v - 1) a <= X
        m, fac = u - 1, []
        while m > 1:
            p, e = spf[m], 0
            while m % p == 0:
                m //= p
                e += 1
            fac.append((p, 2 * e))       # factorization of (u - 1)^2
        divs = [1]
        for p, e in fac:
            nxt = []
            for d in divs:
                for _ in range(e + 1):
                    if d > vmax:
                        break
                    nxt.append(d)
                    d *= p
            divs = nxt
        for v in divs:
            if v >= u:
                b = 2 * v - 1
                if a * b <= X and is_crystal(a, b):
                    crystals.append((a * b, a, b))

    crystals.sort()
    collisions = sum(1 for i in range(1, len(crystals)) if crystals[i][0] == crystals[i - 1][0])
    for i in range(1, len(crystals)):
        if crystals[i][0] == crystals[i - 1][0]:
            print("COLLISION", crystals[i - 1], crystals[i])

    nF3 = nF4 = nF1 = nS = maxj = fp = 0
    for n, a, b in crystals:
        s2, d = (a + b) ** 2, (a + 1) * (b + 1)
        if s2 % d:
            sys.exit(f"Q not integral at {(a, b)}")
        k = s2 // d
        j = chain_index((a + 1) // 2, (b + 1) // 2)
        if k == 3:
            nF3 += 1
        elif k == 4:
            nF4 += 1
        elif j == 1:
            nF1 += 1
        else:
            nS += 1
            maxj = max(maxj, j)
            fp = (fp + n) % 2 ** 64

    print(f"X={X}")
    print(f"F3 (k=3): {nF3}  F4 (k=4): {nF4}  F1 (k>=5, j=1): {nF1}  S (k>=5, j>=2): {nS}"
          f"  max j: {maxj}")
    print(f"total crystals <= X: {len(crystals)}")
    print(f"S fingerprint (sum of n mod 2^64): {fp}")
    print(f"collisions: {collisions}")
    print(f"seconds: {time.time() - t0:.2f}")
    return 1 if collisions else 0


if __name__ == "__main__":
    sys.exit(main())
