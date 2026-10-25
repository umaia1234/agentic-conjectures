#!/usr/bin/env python3
"""Test Conjecture L of DETAILS.md (Section 5) on small multisets.

Usage: generalization_check.py MAXVAL MAXLEN

Catch-Up is played on a multiset: a turn at gap d >= 1 removes a sub-multiset A with
sum(A) >= d and sum(A) - max(A) < d; at gap 0 it removes one number (DETAILS.md, Section 2).
For every multiset Q with entries in 1..MAXVAL and 1..MAXLEN elements this script checks
  (a) if Q is complete with even sum, the game on Q is a draw;
  (b) every position (R, d) = (Q, d) with R + {d} complete and sum(R) - d even is not a loss
      for the player to move (Conjecture L).
The solver is a plain memoized turn recursion with no pruning. As a sanity check it first
reproduces the values of Catch-Up({1..N}) for N <= 10. Exit status 0 iff nothing fails.
"""
import sys
from collections import Counter
from functools import lru_cache
from itertools import combinations_with_replacement

sys.setrecursionlimit(10000)

KNOWN = [1, 1, 0, 0, 1, 1, 0, 0, -1, -1]  # Catch-Up({1..N}), N = 1..10, first player's view


def moves(R, d):
    """R: sorted tuple (multiset). Yield (remaining tuple, opponent's gap)."""
    if d == 0:
        seen = set()
        for i, m in enumerate(R):
            if m in seen:
                continue
            seen.add(m)
            yield R[:i] + R[i + 1:], m
        return
    n = len(R)
    out = set()
    vals = list(R)

    # last pick at index j (value m), B from the other indices with d - m <= sum(B) <= d - 1
    def rec(i, s, chosen, j):
        if i == n:
            m = vals[j]
            if d - m <= s <= d - 1:
                rem = tuple(vals[k] for k in range(n) if k not in chosen and k != j)
                out.add((rem, s + m - d))
            return
        if i == j:
            rec(i + 1, s, chosen, j)
            return
        if s + vals[i] <= d - 1:
            rec(i + 1, s + vals[i], chosen | {i}, j)
        rec(i + 1, s, chosen, j)

    for j in range(n):
        rec(0, 0, frozenset(), j)
    yield from out


@lru_cache(maxsize=None)
def V(R, d):
    """Value for the player to move at gap d: 1 win, 0 draw, -1 loss."""
    if not R:
        return -1 if d > 0 else 0
    if sum(R) < d:
        return -1
    best = -1
    for rem, e in moves(R, d):
        v = -V(rem, e)
        if v > best:
            best = v
            if best == 1:
                break
    return best


def complete(ms):
    pre = 0
    for x in sorted(ms):
        if x > pre + 1:
            return False
        pre += x
    return True


def multisets(maxval, maxlen):
    for L in range(1, maxlen + 1):
        yield from combinations_with_replacement(range(1, maxval + 1), L)


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    maxval, maxlen = int(sys.argv[1]), int(sys.argv[2])
    ok = True
    sanity = [V(tuple(range(1, N + 1)), 0) for N in range(1, len(KNOWN) + 1)]
    print("sanity Catch-Up({1..N}), N = 1..10:", sanity, "ok" if sanity == KNOWN else "MISMATCH")
    ok &= sanity == KNOWN

    st, bad = Counter(), []
    for Q in multisets(maxval, maxlen):
        if sum(Q) % 2 or not complete(Q):
            continue
        v = V(Q, 0)
        st[v] += 1
        if v != 0 and len(bad) < 20:
            bad.append(Q)
    print("fresh games on complete even-sum multisets (value: count):", dict(st))
    print("non-draws:", bad)
    ok &= not bad

    st2, bad2 = Counter(), []
    for R in multisets(maxval, maxlen):
        S = sum(R)
        for d in range(0, S + 1):
            if (S - d) % 2 or not complete(list(R) + ([d] if d else [])):
                continue
            v = V(R, d)
            st2[(d > 0, v)] += 1
            if v < 0 and len(bad2) < 20:
                bad2.append((R, d))
    print("Conjecture L positions ((d > 0, value): count):", dict(st2))
    print("total positions:", sum(st2.values()), " losses:", bad2)
    ok &= not bad2
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
