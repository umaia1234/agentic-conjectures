"""Brute-force reference for the unique multiset-sum problem (no symmetry reduction).

For each modulus N and size n, enumerates every n-subset A of Z_N that contains 0 (every
valid set has a translate containing 0, and validity is translation invariant), decides
validity straight from the definition by counting multisets of size n over A with sum
sum(A) mod N, and reports the affine orbits (x -> u x + v, u a unit) of the valid sets as
their lexicographically smallest sorted representatives.

Usage: python3 brute.py n Nlo Nhi
"""
import sys
from itertools import combinations
from math import gcd


def count_multisets(A, N, size, target, cap=2):
    """Number of multisets of `size` elements of A with sum = target (mod N), capped."""
    # cnt[j][v]: number of multisets of size j over the elements processed so far
    cnt = [[0] * N for _ in range(size + 1)]
    cnt[0][0] = 1
    for a in A:
        for j in range(1, size + 1):  # unbounded multiplicity: increasing j reuses a
            prev, cur = cnt[j - 1], cnt[j]
            for v in range(N):
                if prev[v]:
                    w = (v + a) % N
                    cur[w] = min(cap, cur[w] + prev[v])
    return cnt[size][target % N]


def is_valid(A, N):
    return count_multisets(A, N, len(A), sum(A)) == 1


def canonical(A, N):
    best = None
    for a in A:
        for u in range(1, N):
            if gcd(u, N) != 1:
                continue
            img = sorted((u * (x - a)) % N for x in A)
            if best is None or img < best:
                best = img
    return tuple(best)


def main():
    n, lo, hi = map(int, sys.argv[1:4])
    for N in range(max(lo, n), hi + 1):
        orbits = set()
        nvalid = 0
        for rest in combinations(range(1, N), n - 1):
            A = (0,) + rest
            if is_valid(A, N):
                nvalid += 1
                orbits.add(canonical(A, N))
        print(f"N={N} valid_with_0={nvalid} orbits={len(orbits)}")
        for o in sorted(orbits):
            print(f"  orbit N={N}: " + " ".join(map(str, o)))


if __name__ == "__main__":
    main()
