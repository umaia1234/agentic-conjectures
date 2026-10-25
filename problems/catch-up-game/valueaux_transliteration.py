#!/usr/bin/env python3
"""Term-for-term Python transliteration of the formal-conjectures `valueAux` (Catch-Up).

Usage: valueaux_transliteration.py NMAX            value(Icc 1 N) for N = 1..NMAX
       valueaux_transliteration.py --positions n   valueAux R 0 D false for every R subset of
                                                   {1..n} (printed as a bit mask) and D <= n

`best` is the literal left fold of the upstream `Outcome.best` lambda. Memoization on
(remaining, s_me, s_opp, isFirstMove) does not change any value. Slow by design: it is the
reference the C++ solvers are checked against on small inputs.
"""
import sys
from functools import lru_cache

WIN, LOSS, DRAW = "win", "loss", "draw"


def neg(o):
    return {WIN: LOSS, LOSS: WIN, DRAW: DRAW}[o]


def step(acc, o):
    # fun | .win, _ => .win | _, .win => .win | .draw, _ => .draw | _, .draw => .draw | _, _ => .loss
    if acc == WIN:
        return WIN
    if o == WIN:
        return WIN
    if acc == DRAW:
        return DRAW
    if o == DRAW:
        return DRAW
    return LOSS


def best(os):
    acc = LOSS
    for o in os:
        acc = step(acc, o)
    return acc


@lru_cache(maxsize=None)
def value_aux(remaining, s_me, s_opp, is_first_move):
    """remaining: frozenset of naturals."""
    if len(remaining) == 0:
        if s_me > s_opp:
            return WIN
        elif s_opp > s_me:
            return LOSS
        else:
            return DRAW
    if s_me + sum(remaining) < s_opp:
        return LOSS
    outcomes = []
    for x in sorted(remaining):  # `remaining.attach.toList`: order is irrelevant for `best`
        s_me2 = s_me + x
        remaining2 = remaining - {x}
        if is_first_move:
            outcomes.append(neg(value_aux(remaining2, s_opp, s_me2, False)))
        elif s_me2 >= s_opp:
            outcomes.append(neg(value_aux(remaining2, s_opp, s_me2, False)))
        else:
            outcomes.append(value_aux(remaining2, s_me2, s_opp, False))
    return best(outcomes)


def value(S):
    return value_aux(frozenset(S), 0, 0, True)


def main():
    sys.setrecursionlimit(100000)
    if len(sys.argv) == 3 and sys.argv[1] == "--positions":
        n = int(sys.argv[2])
        for mask in range(1 << n):
            R = frozenset(i + 1 for i in range(n) if mask >> i & 1)
            for D in range(n + 1):
                # s_me = 0, s_opp = D represents the gap D (valueAux depends on the gap only)
                print(mask, D, value_aux(R, 0, D, False))
    elif len(sys.argv) == 2:
        for N in range(1, int(sys.argv[1]) + 1):
            print(f"N={N} T={N * (N + 1) // 2} value={value(range(1, N + 1))}", flush=True)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
