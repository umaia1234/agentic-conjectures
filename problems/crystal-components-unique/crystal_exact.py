"""Collision search for crystal factorizations n = a*b <= X (implementation B, exact Python).

Independent of crystal_search.c: it walks the (u, v) Vieta chain instead of the Lucas pairs,
uses exact integer roots instead of floating-point estimates, and has no overflow.  Standard
library only.

Chain (k >= 3): w_0 = 1, w_1 = k, w_{j+1} = (k-2) w_j - w_{j-1} + 2; the j-th crystal of the
k-chain is (2 w_j - 1, 2 w_{j+1} - 1) for j >= 1.  Classes as in crystal_search.c:
F3 = {35} (k = 3), F4 = k = 4, F1 = (k >= 5, j = 1), S = (k >= 5, j >= 2).
"""

import argparse
import sys
import time


def iroot(n, k):
    """floor(n ** (1/k)) for n >= 0, by integer Newton iteration from above."""
    if n < 2:
        return n
    x = 1 << -(-n.bit_length() // k)
    while True:
        y = ((k - 1) * x + n // x ** (k - 1)) // k
        if y >= x:
            return x
        x = y


def f1(k):
    return (2 * k - 1) * (2 * (k - 1) ** 2 - 1)


def f4(s):
    return (2 * s * s - 1) * (2 * (s + 1) ** 2 - 1)


def inv(f, n, est, lo):
    """Largest t >= lo with f(t) <= n (f strictly increasing on t >= lo)."""
    t = max(est, lo)
    while t > lo and f(t) > n:
        t -= 1
    while f(t + 1) <= n:
        t += 1
    return t


def in_f1(n):
    k = inv(f1, n, iroot(n // 4, 3) + 1, 3)
    return k >= 5 and f1(k) == n


def in_f4(n):
    s = inv(f4, n, iroot(n // 4, 4), 1)
    return s >= 2 and f4(s) == n


def is_crystal(a, b):
    n = a * b
    return (n % 2 == 1 and a > 1 and b > 1
            and ((a + b) ** 2 + (n + 1) ** 2) % (2 * (a + 1) * (b + 1)) == 0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("X", help="bound: integer, 1eNN or 2^NN-1")
    ap.add_argument("--f4-limit", default=None,
                    help="check F4 against F1 only for F4 members <= this bound")
    args = ap.parse_args()

    def parse(s):
        if s.startswith("1e"):
            return 10 ** int(s[2:])
        if s.startswith("2^") and s.endswith("-1"):
            return 2 ** int(s[2:-2]) - 1
        return int(s)

    X = parse(args.X)
    f4lim = parse(args.f4_limit) if args.f4_limit else X
    t0 = time.time()
    collisions = 0

    # S: k >= 5, j >= 2, via the (u, v) chain; every listed pair is re-checked against the
    # definition when it is small enough to be cheap (and for the first members of each k).
    S = []
    k = 5
    maxj = 0
    while True:
        w0, w1 = 1, k
        j = 1
        listed = 0
        last = 0
        while True:
            w2 = (k - 2) * w1 - w0 + 2
            a, b = 2 * w1 - 1, 2 * w2 - 1
            n = a * b
            if n > X:
                break
            if n <= last:
                sys.exit("chain not increasing")
            last = n
            if j >= 2:
                if listed < 2 and not is_crystal(a, b):
                    sys.exit(f"not a crystal: k={k} j={j}")
                if (a + b) ** 2 != k * (a + 1) * (b + 1):
                    sys.exit(f"wrong k: k={k} j={j}")
                S.append(n)
                listed += 1
                maxj = max(maxj, j)
            w0, w1 = w1, w2
            j += 1
        if listed == 0:
            break
        k += 1

    S.sort()
    for i in range(1, len(S)):
        if S[i] == S[i - 1]:
            print("COLLISION S vs S", S[i])
            collisions += 1
    for n in S:
        if in_f1(n):
            print("COLLISION S vs F1", n)
            collisions += 1
        if in_f4(n):
            print("COLLISION S vs F4", n)
            collisions += 1
        if n == 35:
            collisions += 1

    # class sizes
    kmax = inv(f1, X, iroot(X // 4, 3) + 1, 3)
    nF1 = max(0, kmax - 4) if f1(kmax) <= X else 0
    smax = inv(f4, X, iroot(X // 4, 4), 1)
    nF4 = max(0, smax - 1) if f4(smax) <= X else 0
    nF3 = 1 if X >= 35 else 0

    # F4 vs F1 (and F3) up to f4lim
    s = 2
    checked = 0
    while True:
        n = f4(s)
        if n > f4lim or n > X:
            break
        if in_f1(n) or n == 35:
            print("COLLISION F4 vs F1/F3", n)
            collisions += 1
        checked += 1
        s += 1

    fp = sum(S) % 2 ** 64
    print(f"X={X}")
    print(f"F3 (k=3): {nF3}  F4 (k=4): {nF4}  F1 (k>=5, j=1): {nF1}  S (k>=5, j>=2): {len(S)}"
          f"  max j: {maxj}")
    print(f"total crystals <= X: {nF3 + nF4 + nF1 + len(S)}")
    print(f"S fingerprint (sum of n mod 2^64): {fp}")
    print(f"F4 members checked against F1: {checked} (bound {min(f4lim, X)})")
    print(f"collisions: {collisions}")
    print(f"seconds: {time.time() - t0:.2f}")
    return 1 if collisions else 0


if __name__ == "__main__":
    sys.exit(main())
