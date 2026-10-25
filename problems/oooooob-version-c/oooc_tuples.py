#!/usr/bin/env python3
"""Outcome solver for Version C of "Generalizing OOOOOOB" over sorted tuples of pile sizes.

Danai, Ellis and Thanatipanonda (arXiv:2605.23213v1), Version C: a move removes one token from
one pile, or one token from each of two distinct non-empty piles; a player with no move loses.
A position is the sorted tuple of its non-empty pile sizes.  P-positions are computed by the
recursion "P iff no option is P", memoized on the tuple.  This file shares no code with
oooc_counts.cpp, which works on packed counts.

Conjecture 3.1 of the paper: if a position has a_i >= 2 piles of size i for 1 <= i <= n and no
other piles, and it is not 1,1,2,2,3,3,3, then it is a P-position iff its total is a multiple
of 3.

usage:
  python3 oooc_tuples.py              the counterexample rows and the n = 7, a_i in [2, 4] box,
                                      compared with the expected values (exit 1 on mismatch)
  python3 oooc_tuples.py --full       also the n = 6, a_i in [2, 8] box (a few minutes)
  python3 oooc_tuples.py box n lo hi  every (a_1..a_n) in [lo, hi]^n
  python3 oooc_tuples.py --version-b  the three Version B positions of the Related note in
                                      DETAILS.md (exit 1 on mismatch)
Standard library only.
"""
import itertools
import sys

sys.setrecursionlimit(10000)

memo = {}


def options(pos):
    """The positions reachable in one move, as sorted tuples without empty piles."""
    out = set()
    sizes = sorted(set(pos))
    for u in sizes:
        # one token from one pile of size u
        rest = list(pos)
        rest.remove(u)
        out.add(tuple(sorted(rest + [u - 1] if u > 1 else rest)))
    for idx, u in enumerate(sizes):
        for v in sizes[idx:]:
            if u == v and pos.count(u) < 2:
                continue
            rest = list(pos)
            rest.remove(u)
            rest.remove(v)
            rest += [x - 1 for x in (u, v) if x > 1]
            out.add(tuple(sorted(rest)))
    return out


def is_p(pos):
    """True iff the sorted tuple pos is a P-position (every option is an N-position)."""
    got = memo.get(pos)
    if got is None:
        got = all(not is_p(q) for q in options(pos))
        memo[pos] = got
    return got


def from_counts(a):
    """The sorted tuple with a[i - 1] piles of size i."""
    return tuple(i + 1 for i, c in enumerate(a) for _ in range(c))


def predicted_p(a):
    return sum(from_counts(a)) % 3 == 0


def is_exception(a):
    return tuple(a) == (2, 2, 3)


def box(n, lo, hi, show=True):
    checked = failed = 0
    fails = []
    for a in itertools.product(range(lo, hi + 1), repeat=n):
        checked += 1
        p = is_p(from_counts(a))
        if not is_exception(a) and p != predicted_p(a):
            failed += 1
            fails.append((a, sum(from_counts(a)), "P" if p else "N"))
            if show:
                print(f"FAIL n={n} a={a} total={sum(from_counts(a))} outcome={'P' if p else 'N'}")
    print(f"box n={n} a_i in [{lo},{hi}]: positions={checked} failures={failed} states={len(memo)}")
    return checked, failed, fails


def rows():
    ok = True
    expected = {(2, 2, 2, 2, 2, 2, 3): (63, False), (2, 2, 2, 2, 2, 2, 4): (70, True),
                (2, 2, 2, 2, 2, 3, 3): (69, False), (2, 2, 2, 2, 2, 3, 4): (76, True),
                (0, 2, 2, 2, 2, 2, 3): (61, True)}
    for a, (tot, p_expected) in expected.items():
        pos = from_counts(a)
        p = is_p(pos)
        wins = sorted(q for q in options(pos) if is_p(q))
        print(f"counts {a} total={sum(pos)} outcome={'P' if p else 'N'} "
              f"moves to P-positions={len(wins)}")
        ok &= p == p_expected and sum(pos) == tot
    # the winning move of the MathDB post: one token from each of the two piles of size 1
    x = from_counts((2, 2, 2, 2, 2, 2, 3))
    ok &= from_counts((0, 2, 2, 2, 2, 2, 3)) in options(x)
    return ok


memo_b = {}


def options_b(pos):
    """Version B of the paper: one token from one pile, or one token from every pile."""
    out = set()
    for u in set(pos):
        rest = list(pos)
        rest.remove(u)
        out.add(tuple(sorted(rest + [u - 1] if u > 1 else rest)))
    if pos:
        out.add(tuple(x - 1 for x in pos if x > 1))
    return out


def is_p_b(pos):
    """True iff the sorted tuple pos is a P-position of Version B."""
    got = memo_b.get(pos)
    if got is None:
        got = all(not is_p_b(q) for q in options_b(pos))
        memo_b[pos] = got
    return got


def version_b():
    """Conjecture 2.2 of the paper (Version B) says that if a_n >= 2n - 4, the outcome depends
    only on the parities of a_1..a_{n-1}.  MathDB post 374892: with n = 7 and a_7 = 10, the first
    two positions have the same parities but different outcomes."""
    ok = True
    for a, p_expected in [((0, 1, 0, 0, 0, 0, 10), True), ((0, 1, 0, 0, 0, 4, 10), False),
                          ((0, 1, 0, 0, 0, 4, 11), True)]:
        p = is_p_b(from_counts(a))
        print(f"Version B counts {a} outcome={'P' if p else 'N'}")
        ok &= p == p_expected
    print("OK: all expected values reproduced" if ok else "MISMATCH with the expected values")
    return ok


def main(argv):
    if len(argv) == 5 and argv[1] == "box":
        n, lo, hi = map(int, argv[2:])
        box(n, lo, hi)
        return 0
    if argv[1:] == ["--version-b"]:
        return 0 if version_b() else 1
    if len(argv) > 2 or (len(argv) == 2 and argv[1] != "--full"):
        print(__doc__)
        return 2
    ok = rows()
    checked, failed, fails = box(7, 2, 4)
    ok &= checked == 2187 and failed == 15
    if len(argv) == 2:
        memo.clear()
        checked, failed, _ = box(6, 2, 8)
        ok &= checked == 117649 and failed == 0
    print("OK: all expected values reproduced" if ok else "MISMATCH with the expected values")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
