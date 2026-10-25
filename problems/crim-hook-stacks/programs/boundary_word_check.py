#!/usr/bin/env python3
"""Check the boundary-word classification of CRIM P-positions against the game.

Claim (Zijian Zeng, "A Boundary-Word Classification of Losing Positions in
CRIM", 2026-08-29, unrefereed).  Let l have distinct part sizes
v_1 > ... > v_k > 0, where v_i occurs a_i times, and put b_i = v_i - v_{i+1}
(v_{k+1} = 0); the boundary word of l is 0^{a_1} 1^{b_1} ... 0^{a_k} 1^{b_k},
of length len(l) + l1.  A pair (a_i, b_i) is A-good if a_i = 1 and b_i is
odd, and B-good if a_i is odd and b_i = 1.  L is the length of the longest
prefix of A-good pairs, R the length of the longest suffix of B-good pairs,
and M = min(k, L + R) (M = 0 for the empty partition).  Then
  l is P  <=>  len(l) + l1 is even and M is even.
Since rank(l) = |len(l) - l1| has the parity of len(l) + l1, the claim
implies conj:main of arXiv:2606.16828.

This program computes P/N exactly with the solver of crim_check.py (same
directory) and compares it with the claim for every partition with |l| <= N.

Usage: python3 programs/boundary_word_check.py --max-n N
Prints one line per n and a summary line; exits 1 on any mismatch.
"""

from __future__ import annotations

import argparse
import sys

from crim_check import solve


def run_pairs(l):
    """The pairs (a_i, b_i) of the boundary word of l."""
    pairs = []
    i = 0
    while i < len(l):
        j = i
        while j < len(l) and l[j] == l[i]:
            j += 1
        below = l[j] if j < len(l) else 0
        pairs.append((j - i, l[i] - below))
        i = j
    return pairs


def end_peeling(l):
    """M = min(k, L + R) for the boundary word of l."""
    pairs = run_pairs(l)
    k = len(pairs)
    left = 0
    while left < k and pairs[left][0] == 1 and pairs[left][1] % 2 == 1:
        left += 1
    right = 0
    while right < k and pairs[k - 1 - right][0] % 2 == 1 and pairs[k - 1 - right][1] == 1:
        right += 1
    return min(k, left + right)


def predicted_p(l):
    length = len(l) + (l[0] if l else 0)
    return length % 2 == 0 and end_peeling(l) % 2 == 0


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--max-n", type=int, required=True,
                        help="check all partitions l with |l| <= N")
    max_n = parser.parse_args().max_n
    if max_n < 0:
        parser.error("--max-n must be >= 0")

    status, total, p_lists = solve(max_n)
    by_size = [[0, 0] for _ in range(max_n + 1)]  # [P-positions, mismatches]
    mismatches = []
    for l, is_p in status.items():
        n = sum(l)
        by_size[n][0] += is_p
        if predicted_p(l) != is_p:
            by_size[n][1] += 1
            mismatches.append(l)

    for n in range(max_n + 1):
        print(f"n={n} partitions={total[n]} P={by_size[n][0]} mismatches={by_size[n][1]}")
    for l in sorted(mismatches)[:20]:
        print(f"MISMATCH: {list(l)} is {'P' if status[l] else 'N'}, M={end_peeling(l)}")
    verdict = "FAIL" if mismatches else "OK"
    print(f"summary: {verdict} N={max_n} partitions={sum(total)} "
          f"P={sum(len(p) for p in p_lists)} mismatches={len(mismatches)}")
    return 1 if mismatches else 0


if __name__ == "__main__":
    sys.exit(main())
