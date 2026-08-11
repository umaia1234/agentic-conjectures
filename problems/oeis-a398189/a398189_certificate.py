#!/usr/bin/env python3
"""Executable certificate for problems/oeis-a398189.

Re-checks, over a finite range, the four cases of Luschny's conjectured
2-adic valuation formula for the generalized Schenker sums

    A398187(n, k) = Sum_{j=0..n-k} ((n-k)!/j!) * n^j,   0 <= k <= n,
    A398189(n, k) = v2(A398187(n, k)),

which are proved for ALL (n, k) in the repository's Lean module
`AgenticConjectures/OeisA398189.lean`. This script is a finite sanity
cross-check of that proof (and of the statement's faithfulness against the
OEIS data); it does not replace the proof.

Checks performed (any failure exits nonzero):
  1. Two independent implementations of A398187 agree
     (closed form with factorial division vs. the recurrence
     U_0 = 1, U_m = m*U_{m-1} + n^m, with T(n, k) = U_{n-k}).
  2. The computed triangle of valuations reproduces the 91 DATA terms
     (rows 0..12) published in the OEIS A398189 entry.
  3. All four conjectured cases hold for every 0 <= k <= n <= N_MAX,
     and in the excluded class (n odd, k == 14 mod 16) the valuation
     is always >= 4 (the Lean module's bonus theorem).
  4. The mod-16 reduction used by the Lean proof: for odd n,
     U(n, m) mod 16 depends only on (n mod 16, m mod 16).

Expected runtime: well under a minute (pure Python, no dependencies).
"""
import math
import sys

N_MAX = 220          # triangle rows checked exhaustively in step 3
EQ_MAX = 90          # rows for the two-implementation equality check
PERIOD_MAX = 200     # range for the mod-16 periodicity check

# The DATA section of https://oeis.org/A398189 (rows 0..12, flattened),
# as retrieved on 2026-08-12.
OEIS_DATA = [
    0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 3, 1, 1, 0, 0, 1, 0, 2, 0, 1, 0, 4, 3, 3,
    1, 1, 0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 7, 4, 4, 3, 3, 1, 1, 0, 0, 1, 0, 2,
    0, 1, 0, 3, 0, 1, 0, 8, 7, 7, 4, 4, 3, 3, 1, 1, 0, 0, 1, 0, 2, 0, 1, 0,
    3, 0, 1, 0, 2, 0, 10, 8, 8, 7, 7, 4, 4, 3, 3, 1, 1, 0, 0,
]


def v2(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length() - 1


def T_closed(n: int, k: int) -> int:
    """Implementation 1: the literal OEIS closed form."""
    m = n - k
    return sum(math.factorial(m) // math.factorial(j) * n ** j for j in range(m + 1))


def row_by_recurrence(n: int) -> list[int]:
    """Implementation 2: U_0 = 1, U_m = m*U_{m-1} + n^m; returns
    [T(n, n), T(n, n-1), ..., T(n, 0)] = [U_0, U_1, ..., U_n]."""
    u, out, p = 1, [1], 1
    for m in range(1, n + 1):
        p *= n
        u = m * u + p
        out.append(u)
    return out


def fail(msg: str) -> None:
    print(f"FAIL: {msg}")
    sys.exit(1)


def main() -> None:
    # -- 1. the two implementations agree -------------------------------
    for n in range(EQ_MAX + 1):
        row = row_by_recurrence(n)
        for k in range(n + 1):
            if T_closed(n, k) != row[n - k]:
                fail(f"implementations disagree at (n, k) = ({n}, {k})")
    print(f"[1] closed form == recurrence for all 0 <= k <= n <= {EQ_MAX}")

    # -- 2. reproduce the published OEIS terms --------------------------
    flat = []
    n = 0
    while len(flat) < len(OEIS_DATA):
        row = row_by_recurrence(n)
        flat.extend(v2(row[n - k]) for k in range(n + 1))
        n += 1
    if flat[: len(OEIS_DATA)] != OEIS_DATA:
        fail("computed valuations do not match the OEIS A398189 DATA terms")
    print(f"[2] all {len(OEIS_DATA)} published OEIS terms reproduced (rows 0..{n - 1})")

    # -- 3. the four conjectured cases + excluded-class bound -----------
    checked = excluded = 0
    for n in range(N_MAX + 1):
        row = row_by_recurrence(n)
        for k in range(n + 1):
            t = v2(row[n - k])
            if n % 2 == 0:
                expect = v2(math.factorial(n - k)) if n - k >= 2 else 0
                if t != expect:
                    fail(f"even case fails at (n, k) = ({n}, {k}): {t} != {expect}")
            elif k % 2 == 1:
                if t != 0:
                    fail(f"odd/odd case fails at (n, k) = ({n}, {k}): {t} != 0")
            elif k % 16 != 14:
                if t != v2(k + 2):
                    fail(f"odd/even case fails at (n, k) = ({n}, {k}): {t} != {v2(k + 2)}")
            else:
                excluded += 1
                if t < 4:
                    fail(f"excluded-class bound fails at (n, k) = ({n}, {k}): {t} < 4")
            checked += 1
    print(f"[3] all four cases hold for the {checked} pairs with n <= {N_MAX} "
          f"(incl. v2 >= 4 on the {excluded} excluded-class pairs)")

    # -- 4. the mod-16 reduction behind the Lean proof ------------------
    small = {}
    for n0 in range(16):
        u, tab = 1, [1]
        p = 1
        for m in range(1, 16):
            p = (p * n0) % 16
            u = (m * u + p) % 16
            tab.append(u)
        small[n0] = tab
    for n in range(1, PERIOD_MAX + 1, 2):
        row = row_by_recurrence(n)
        for m in range(n + 1):
            if row[m] % 16 != small[n % 16][m % 16]:
                fail(f"mod-16 reduction fails at (n, m) = ({n}, {m})")
    print(f"[4] mod-16 reduction confirmed for odd n <= {PERIOD_MAX}")

    print("OK: all certificate checks passed")


if __name__ == "__main__":
    main()
