#!/usr/bin/env python3
"""Check the case table of the proof that conj:main implies conj:bloby (hooks).

Definitions as in crim_check.py (same directory), whose P/N table is used:
moves delete a row or a column, H(r, c, m) = [c, 1+m_1, ..., 1+m_k,
1^(r-1-k)], G(r, c) = H(r, c, []).  Rows and columns are 1-indexed in the
current position.

For every P-position m != [] (k = len(m), m_1 = largest part) and r, c >= 2
with r = c (mod 2), k <= r-1, m_1 <= c-1 and |X| <= N, X = H(r, c, m), and
for every move from X, the prescribed reply must be a legal move of the
position after the move, give the shape in brackets, and give a P-position:

  R1   delete row 1 -> delete column 1 [= m]
  C1   delete column 1 -> delete row 1 [= m]
  Rin  delete row i+1, 1 <= i <= k -> H(r-1, c, n), n = m minus part i (N);
       for every move of n to a P-position n':
         row i':    r >= 4: delete row i'+1 [= H(r-2, c, n')]
                    r = 3 (k = 2, n = [a]): delete column 1 [= [c-1, a]]
         column j': delete column j'+1 [= H(r-1, c-1, n')]
  Rleg delete a row k+2..r -> H(r-1, c, m);
         r >= k+3: delete another leg row [= H(r-2, c, m)]
         else c >= m_1+2: delete column c [= H(r-1, c-1, m)]; else impossible
  Cin  delete column j+1, 1 <= j <= m_1 -> H(r, c-1, n), n = m minus column j (N);
       for every move of n to a P-position n':
         column j': c >= 4: delete column j'+1 [= H(r, c-2, n')]
                    c = 3 (n = [1^a]): delete row 1 [= [2^a, 1^(r-1-a)]]
         row i':    delete row i'+1 [= H(r-1, c-1, n')]
  Carm delete a column m_1+2..c -> H(r, c-1, m);
         c >= m_1+3: delete column c-1 [= H(r, c-2, m)]
         else r >= k+2: delete a leg row [= H(r-1, c-1, m)]; else impossible

The position after the first move is also checked against its stated shape.
Counts each case and sub-case; Rin/Cin sub-cases count (move, P-child move)
pairs.  Also checks the base case: G(r, c), r, c >= 1, r + c - 1 <= N, is P
iff r, c >= 2 and r = c (mod 2).

Usage: python3 programs/strategy_check.py --max-n N
Exits 1 on any failure (including any occurrence of an impossible sub-case).
"""

from __future__ import annotations

import argparse
import sys
from collections import Counter

from crim_check import delete_column, delete_row, hook, hook_stack, solve

# (label, printed description); labels with "impossible" must never occur.
CASES = [
    ("R1", "R1  delete row 1; reply column 1"),
    ("C1", "C1  delete column 1; reply row 1"),
    ("Rin", "Rin  delete row i+1 (moves)"),
    ("Rin row r>=4", "  P-child by row i', r >= 4; reply row i'+1"),
    ("Rin row r=3", "  P-child by row i', r = 3; reply column 1"),
    ("Rin col", "  P-child by column j'; reply column j'+1"),
    ("Rleg", "Rleg  delete a leg row (moves)"),
    ("Rleg r>=k+3", "  r >= k+3; reply another leg row"),
    ("Rleg c>=m1+2", "  r = k+2, c >= m_1+2; reply column c"),
    ("Rleg impossible", "  r = k+2, c = m_1+1 (impossible)"),
    ("Cin", "Cin  delete column j+1 (moves)"),
    ("Cin col c>=4", "  P-child by column j', c >= 4; reply column j'+1"),
    ("Cin col c=3", "  P-child by column j', c = 3; reply row 1"),
    ("Cin row", "  P-child by row i'; reply row i'+1"),
    ("Carm", "Carm  delete an arm column (moves)"),
    ("Carm c>=m1+3", "  c >= m_1+3; reply column c-1"),
    ("Carm r>=k+2", "  c = m_1+2, r >= k+2; reply a leg row"),
    ("Carm impossible", "  c = m_1+2, r = k+1 (impossible)"),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--max-n", type=int, required=True,
                        help="check all stacks X with |X| <= N")
    max_n = parser.parse_args().max_n
    if max_n < 0:
        parser.error("--max-n must be >= 0")

    status, _, p_lists = solve(max_n)
    counts = Counter()
    failures = []

    def fail(message):
        failures.append(message)

    def check_shape(label, position, expected):
        if expected is None or position != expected:
            fail(f"{label}: position {position}, expected {expected}")

    def reply(label, Y, kind, index, expected):
        """Play the reply in Y; it must be legal, give `expected` and be P."""
        counts[label] += 1
        Z = delete_row(Y, index) if kind == "row" else delete_column(Y, index)
        if Z is None:
            fail(f"{label}: {kind} {index} is not a move of {Y}")
        elif expected is None or Z != expected:
            fail(f"{label}: {kind} {index} of {Y} gives {Z}, expected {expected}")
        elif not status[Z]:
            fail(f"{label}: {kind} {index} of {Y} gives the N-position {Z}")

    def p_child_moves(n):
        """Every (kind, index, n') with n' = move of n and n' a P-position."""
        for i in range(1, len(n) + 1):
            child = delete_row(n, i)
            if status[child]:
                yield "row", i, child
        for j in range(1, (n[0] if n else 0) + 1):
            child = delete_column(n, j)
            if status[child]:
                yield "col", j, child

    def check_stack(m, r, c):
        k, m1 = len(m), m[0]
        X = hook_stack(r, c, m)
        if not status[X]:
            fail(f"X = H({r},{c},{m}) = {X} is N")
        for row in range(1, r + 1):
            Y = delete_row(X, row)
            if row == 1:
                reply("R1", Y, "col", 1, m)
            elif row <= k + 1:
                counts["Rin"] += 1
                n = delete_row(m, row - 1)
                check_shape("Rin", Y, hook_stack(r - 1, c, n))
                if status[n]:
                    fail(f"Rin: n = {n} is P")
                for kind, idx, n2 in p_child_moves(n):
                    if kind == "row" and r >= 4:
                        reply("Rin row r>=4", Y, "row", idx + 1, hook_stack(r - 2, c, n2))
                    elif kind == "row" and r == 3:
                        if not (k == 2 and len(n) == 1):
                            fail(f"Rin row r=3: k = {k}, n = {n}")
                        reply("Rin row r=3", Y, "col", 1, (c - 1, n[0]))
                    elif kind == "row":
                        fail(f"Rin row with r = {r}: no reply prescribed")
                    else:
                        reply("Rin col", Y, "col", idx + 1, hook_stack(r - 1, c - 1, n2))
            else:
                counts["Rleg"] += 1
                check_shape("Rleg", Y, hook_stack(r - 1, c, m))
                if r >= k + 3:
                    # The last row of Y = H(r-1, c, m) is a leg row since r-1 >= k+2.
                    reply("Rleg r>=k+3", Y, "row", len(Y), hook_stack(r - 2, c, m))
                elif c >= m1 + 2:
                    reply("Rleg c>=m1+2", Y, "col", c, hook_stack(r - 1, c - 1, m))
                else:
                    counts["Rleg impossible"] += 1
                    fail(f"Rleg impossible case: m = {m}, r = {r}, c = {c}")
        for col in range(1, c + 1):
            Y = delete_column(X, col)
            if col == 1:
                reply("C1", Y, "row", 1, m)
            elif col <= m1 + 1:
                counts["Cin"] += 1
                n = delete_column(m, col - 1)
                check_shape("Cin", Y, hook_stack(r, c - 1, n))
                if status[n]:
                    fail(f"Cin: n = {n} is P")
                for kind, idx, n2 in p_child_moves(n):
                    if kind == "col" and c >= 4:
                        reply("Cin col c>=4", Y, "col", idx + 1, hook_stack(r, c - 2, n2))
                    elif kind == "col" and c == 3:
                        if any(p != 1 for p in n):
                            fail(f"Cin col c=3: n = {n} is not [1^a]")
                        a = len(n)
                        reply("Cin col c=3", Y, "row", 1, (2,) * a + (1,) * (r - 1 - a))
                    elif kind == "col":
                        fail(f"Cin col with c = {c}: no reply prescribed")
                    else:
                        reply("Cin row", Y, "row", idx + 1, hook_stack(r - 1, c - 1, n2))
            else:
                counts["Carm"] += 1
                check_shape("Carm", Y, hook_stack(r, c - 1, m))
                if c >= m1 + 3:
                    reply("Carm c>=m1+3", Y, "col", c - 1, hook_stack(r, c - 2, m))
                elif r >= k + 2:
                    # The last row of Y = H(r, c-1, m) is a leg row since r >= k+2.
                    reply("Carm r>=k+2", Y, "row", len(Y), hook_stack(r - 1, c - 1, m))
                else:
                    counts["Carm impossible"] += 1
                    fail(f"Carm impossible case: m = {m}, r = {r}, c = {c}")

    stacks = [0] * (max_n + 1)
    for s, p_list in enumerate(p_lists):
        for m in p_list:
            if not m:
                continue
            k, m1 = len(m), m[0]
            for r in range(max(2, k + 1), max_n + 1):
                c_min = max(2, m1 + 1)
                if s + r + c_min - 1 > max_n:
                    break
                if (c_min - r) % 2:
                    c_min += 1
                for c in range(c_min, max_n - s - r + 2, 2):
                    stacks[s + r + c - 1] += 1
                    check_stack(m, r, c)

    hooks = 0
    for r in range(1, max_n + 1):
        for c in range(1, max_n + 2 - r):
            hooks += 1
            if status[hook(r, c)] != (r >= 2 and c >= 2 and (r - c) % 2 == 0):
                fail(f"base case: G({r},{c}) is {'P' if status[hook(r, c)] else 'N'}")

    for n in range(max_n + 1):
        print(f"n={n} stacks={stacks[n]}")
    print("case counts (moves from X; Rin/Cin sub-cases count (move, P-child move) pairs):")
    for label, text in CASES:
        print(f"  {text:<52} {counts[label]}")
    print(f"base case: {hooks} hooks G(r,c) with r + c - 1 <= {max_n} checked")
    for f in failures[:20]:
        print("FAIL:", f)
    verdict = "FAIL" if failures else "OK"
    replies = sum(counts[label] for label, _ in CASES
                  if label not in ("Rin", "Rleg", "Cin", "Carm") and "impossible" not in label)
    print(f"summary: {verdict} N={max_n} stacks={sum(stacks)} replies={replies} "
          f"hooks={hooks} failures={len(failures)}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
