#!/usr/bin/env python3
"""Brute force: pi(n) <= 2 T(n) for every n <= 10^6, where T(n) = #{1 <= k <= n : tau(k) | k}.

Plain divisor-count sieve, no shared code with the C++ programs. Also prints the n where equality
pi(n) = 2 T(n) holds and checks T(10^6) = 44705, pi(10^6) = 78498 (the first grid point).
"""
import sys

N = 10**6


def main() -> int:
    tau = [0] * (N + 1)
    for d in range(1, N + 1):
        for m in range(d, N + 1, d):
            tau[m] += 1
    T = P = 0
    equal, bad = [], []
    for n in range(1, N + 1):
        if n % tau[n] == 0:
            T += 1
        if tau[n] == 2:
            P += 1
        if P > 2 * T:
            bad.append(n)
        elif P == 2 * T and P > 0:
            equal.append(n)
    print(f"T({N}) = {T}, pi({N}) = {P}")
    print(f"n <= {N} with pi(n) = 2T(n) > 0: {equal}")
    ok = not bad and T == 44705 and P == 78498
    print(("VERIFIED" if ok else f"FAILED {bad[:10]}") + f": pi(n) <= 2T(n) for all n <= {N}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
