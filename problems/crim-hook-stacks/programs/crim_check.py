#!/usr/bin/env python3
"""Exhaustive CRIM check: P/N positions, conj:main, and conj:bloby for hooks.

Definitions (CRIM; Basic, Gottlieb, Krnc, arXiv:2606.16828).  A position is
a partition l, a weakly decreasing tuple of positive integers; len(l) is the
number of parts (rows) and l1 the largest part (0 for the empty partition).
A move deletes one row (removes one part) or deletes a column j with
1 <= j <= l1 (every part >= j decreases by 1, then zero parts are removed).
Normal play: [] is P; l is P iff every move leads to an N-position.

  rank(l) = |len(l) - l1|;  conj:main: every P-position has even rank.
  Hook G(r, c) = [c, 1^(r-1)].  Durfee length d(l) = greatest d with
  d <= l_d (1-indexed, l_d = 0 past the end).
  General stack, d = d(l), k = len(m), m_1 = 0 if m = []: defined iff
  l_{d+i} = d for 1 <= i <= k and l_d >= d + m_1, and then
  l <| m = [l_1..l_d, l_{d+1}+m_1, ..., l_{d+k}+m_k, l_{d+k+1}, ..., l_R].
  For a hook: H(r, c, m) = [c, 1+m_1, ..., 1+m_k, 1^(r-1-k)], defined iff
  k <= r-1 and m_1 <= c-1.
  conj:bloby: if m and G(r, c) are P and G(r, c) <| m is defined, it is P.

For all partitions with |l| <= N this computes P/N by trying every row and
every column deletion, checks conj:main for every P-position, and, for every
pair (m, G(r, c)) of P-positions with |m| + r + c - 1 <= N, computes the
stack with the general definition, checks that it is defined exactly when
k <= r-1 and m_1 <= c-1, that it then equals H(r, c, m), and that it is P.

Usage: python3 programs/crim_check.py --max-n N
Prints one line per n (partitions, P-positions, bloby pairs checked with
|stack| = n) and a final summary line; exits 1 on any failure.
"""

from __future__ import annotations

import argparse
import sys


def partitions(n):
    """Yield every partition of n once, as a weakly decreasing tuple."""
    if n == 0:
        yield ()
        return
    parts = [n]
    while True:
        yield tuple(parts)
        # Next partition in reverse lexicographic order: lower the last part
        # greater than 1 by one and refill greedily below it.
        ones = 0
        while parts and parts[-1] == 1:
            parts.pop()
            ones += 1
        if not parts:
            return
        top = parts.pop()
        left = top + ones
        while left > 0:
            parts.append(min(top - 1, left))
            left -= parts[-1]


def delete_row(l, i):
    """Position after deleting row i (1-indexed), or None if there is no row i."""
    if not 1 <= i <= len(l):
        return None
    return l[:i - 1] + l[i:]


def delete_column(l, j):
    """Position after deleting column j (1-indexed), or None if illegal."""
    if not (l and 1 <= j <= l[0]):
        return None
    return tuple(q for q in (p - 1 if p >= j else p for p in l) if q > 0)


def moves(l):
    """Yield the position after every move: rows 1..len(l), columns 1..l1."""
    for i in range(1, len(l) + 1):
        yield delete_row(l, i)
    for j in range(1, (l[0] if l else 0) + 1):
        yield delete_column(l, j)


def solve(max_n):
    """Return (status, total, p_lists) for all partitions with |l| <= max_n.

    status[l] is True iff l is a P-position, total[n] is the number of
    partitions of n, and p_lists[n] lists the P-positions of size n.
    """
    status = {}
    total = []
    p_lists = []
    for n in range(max_n + 1):
        count = 0
        p_list = []
        for l in partitions(n):
            count += 1
            is_p = not any(status[child] for child in moves(l))
            status[l] = is_p
            if is_p:
                p_list.append(l)
        total.append(count)
        p_lists.append(p_list)
    return status, total, p_lists


def crim_rank(l):
    return abs(len(l) - (l[0] if l else 0))


def hook(r, c):
    return (c,) + (1,) * (r - 1)


def hook_stack(r, c, m):
    """H(r, c, m) = [c, 1+m_1, ..., 1+m_k, 1^(r-1-k)], or None if undefined."""
    if r < 1 or c < 1 or len(m) > r - 1 or (m and m[0] > c - 1):
        return None
    return (c,) + tuple(1 + p for p in m) + (1,) * (r - 1 - len(m))


def durfee(l):
    """Greatest d with d <= l_d (1-indexed; l_d = 0 past the end)."""
    d = 0
    while d < len(l) and l[d] >= d + 1:
        d += 1
    return d


def stack(l, m):
    """General stack l <| m for nonempty l, or None if it is undefined."""
    d = durfee(l)
    k = len(m)
    m1 = m[0] if m else 0

    def part(i):  # l_i, 1-indexed, 0 past the end
        return l[i - 1] if i <= len(l) else 0

    if any(part(d + i) != d for i in range(1, k + 1)):
        return None
    if part(d) < d + m1:
        return None
    middle = tuple(part(d + i) + m[i - 1] for i in range(1, k + 1))
    return l[:d] + middle + l[d + k:]


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--max-n", type=int, required=True,
                        help="check all partitions l with |l| <= N")
    max_n = parser.parse_args().max_n
    if max_n < 0:
        parser.error("--max-n must be >= 0")

    status, total, p_lists = solve(max_n)
    failures = []

    for p_list in p_lists:
        for l in p_list:
            if crim_rank(l) % 2:
                failures.append(f"conj:main: {list(l)} is P with odd rank {crim_rank(l)}")

    # P-hooks grouped by size r + c - 1.
    p_hooks = [[] for _ in range(max_n + 1)]
    for r in range(1, max_n + 1):
        for c in range(1, max_n + 2 - r):
            if status[hook(r, c)]:
                p_hooks[r + c - 1].append((r, c))

    bloby = [0] * (max_n + 1)
    evaluated = undefined = 0
    for s, p_list in enumerate(p_lists):
        for m in p_list:
            k = len(m)
            m1 = m[0] if m else 0
            for h in range(1, max_n - s + 1):
                for r, c in p_hooks[h]:
                    evaluated += 1
                    st = stack(hook(r, c), m)
                    hook_rule = k <= r - 1 and m1 <= c - 1
                    if (st is not None) != hook_rule:
                        failures.append(f"definedness: G({r},{c}) <| {list(m)} general "
                                        f"{st is not None}, hook rule {hook_rule}")
                        continue
                    if st is None:
                        undefined += 1
                        continue
                    bloby[s + h] += 1
                    if st != hook_stack(r, c, m):
                        failures.append(f"formula: G({r},{c}) <| {list(m)} = {list(st)} "
                                        f"!= H = {list(hook_stack(r, c, m))}")
                    elif not status[st]:
                        failures.append(f"conj:bloby: m={list(m)} and G({r},{c}) are P "
                                        f"but {list(st)} is N")

    for n in range(max_n + 1):
        print(f"n={n} partitions={total[n]} P={len(p_lists[n])} bloby_pairs={bloby[n]}")
    print(f"general stack: {evaluated} pairs (m, G(r,c)) of P-positions with "
          f"|m|+r+c-1 <= {max_n} evaluated, {evaluated - undefined} defined, "
          f"{undefined} undefined")
    for f in failures[:20]:
        print("FAIL:", f)
    verdict = "FAIL" if failures else "OK"
    print(f"summary: {verdict} N={max_n} partitions={sum(total)} "
          f"P={sum(len(p) for p in p_lists)} bloby_pairs={sum(bloby)} "
          f"failures={len(failures)}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
