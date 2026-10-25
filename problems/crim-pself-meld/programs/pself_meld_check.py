#!/usr/bin/env python3
"""Exhaustive CRIM checks for the thick-hook meld conjecture and conj:pself.

Source: Ina Basic, Eric Gottlieb, Matjaz Krnc, "CRIM: A Natural Game on
Integer Partitions", arXiv:2606.16828.  This program is evidence only.  It
is independent of the Lean proofs and of the programs in
problems/crim-hook-stacks.

Definitions.  A partition l is a weakly decreasing tuple of positive
integers; l_i is its i-th part (1-indexed, 0 past the end), len(l) its
number of rows and l_1 its largest part (0 for []).  A move deletes one row,
or deletes one column j (1 <= j <= l_1: every part >= j drops by one and
zero parts disappear).  Every move lowers |l|, so outcomes are computed by
increasing size.  Normal play: [] is P, and l is P iff no move reaches a
P-position.  Misere play: [] is N (the player to move there wins), and a
nonempty l is P iff no move reaches a misere P-position.

  conjugate      l'_k = #{i : l_i >= k}.
  parity self-conjugate (the paper's reading, used for the main check):
                 l_k = l'_k (mod 2) for every k >= 1, both 0 past the end.
                 The weaker reading "for 1 <= k <= min(len(l), l_1)" is
                 tested too.
  meld           mu <> lam = [mu_1 + lam_1, ..., mu_1 + lam_m, mu_1, ..., mu_k].
  thick hook     [c^a, b^(r-a)] with r > a >= 2 and c > b >= 2.
  hook           G(r, c) = [c, 1^(r-1)].
  Durfee length  d(l) = greatest d with d <= l_d.
  stack          with d = d(l), k = len(m), m_1 = 0 for m = []: l <| m is
                 defined iff l_{d+i} = d for 1 <= i <= k and l_d >= d + m_1,
                 and then it is
                 [l_1, ..., l_d, l_{d+1} + m_1, ..., l_{d+k} + m_k, l_{d+k+1}, ...].
  Conway pair    cp(l) = (normal Sprague-Grundy value, misere Grundy value):
                 both are the mex of the options' values, except that the
                 misere value of the terminal position [] is 1.
  run pairs      (a_i, b_i): a_i is the multiplicity of the i-th largest
                 distinct part v_i, and b_i = v_i - v_{i+1} (v_{k+1} = 0).
                 L = number of leading pairs (1, odd), R = number of trailing
                 pairs (odd, 1), M = min(k, L + R).

Checks, for all partitions of size <= N:
  1. Zeng's rule "P iff len(l) + l_1 and M are both even" agrees with the
     computed normal-play outcome.
  2. Meld: the losing thick hooks are those with r = c (mod 2) (thm:thick-hook
     of the paper), the closure of the losing thick hooks under the binary
     meld (every bracketing) contains only P-positions, and the meld is
     associative with unit [] on all triples of partitions of size <= 6.
  3. conj:pself: for each reading of "the stack of odd self-conjugate hooks
     and [1]" the set of such stacks is built with the general stack and
     compared with the parity self-conjugate N-positions.  Readings: hooks
     G(r, r) with r odd ("odd") or with any r ("all"); [1] required as the
     last piece ("ends in [1]") or not ("any"); nesting right (h <| x),
     left (x <| h), or every bracketing (x <| y).  The reading "odd, ends in
     [1]" must match exactly in all three nestings.
  4. Facts used by the Lean proof: for parity self-conjugate l, L = R and
     len(l) + l_1 is even, and if L + R >= k then l is self-conjugate.
  5. With --misere: l is a misere P-position iff exactly one of "l is a
     normal P-position" and "L + R >= k" holds (proved in Lean as
     misereP_iff; checked here independently).
  6. With --hookswap: the Conway pairs agree with the outcomes above, and a
     nonempty l has Conway pair (0, 1) iff it is an even-by-even hook
     [c, 1^(r-1)] with r, c >= 2 even (conj:hookswap).  The paper's own
     cp([]) = (0, 1) is the exception at [], which is printed.

Usage: python3 programs/pself_meld_check.py --max-n N [--misere] [--hookswap]
Prints one line per n and summary lines; exits 1 on any failure.
"""

from __future__ import annotations

import argparse
import sys


def partitions(n, top=None):
    """Yield every partition of n with parts <= top, as a weakly decreasing tuple."""
    if top is None:
        top = n
    if n == 0:
        yield ()
        return
    for v in range(min(n, top), 0, -1):
        for rest in partitions(n - v, v):
            yield (v,) + rest


def moves(l):
    """The distinct positions one move away from l."""
    out = set()
    n = len(l)
    i = 0
    while i < n:
        v = l[i]
        j = i
        while j < n and l[j] == v:
            j += 1
        # Rows i..j-1 all equal v: deleting any one of them gives the same partition.
        out.add(l[:i] + l[i + 1:])
        # A column c with l[j] < c <= v (l[n] = 0) meets exactly rows 0..j-1.
        out.add(tuple(x - 1 for x in l[:j] if x > 1) + l[j:])
        i = j
    return out


def part(l, i):
    return l[i - 1] if 1 <= i <= len(l) else 0


def conjugate(l):
    return tuple(sum(1 for x in l if x >= c) for c in range(1, part(l, 1) + 1))


def pself(l):
    """The paper's reading: l_k = l'_k (mod 2) for every k >= 1 (0 past the end)."""
    lc = conjugate(l)
    return all(part(l, k) % 2 == part(lc, k) % 2
               for k in range(1, max(len(l), len(lc)) + 1))


def pself_weak(l):
    """Weaker reading: only 1 <= k <= min(len(l), l_1) is compared."""
    lc = conjugate(l)
    return all(l[k] % 2 == lc[k] % 2 for k in range(min(len(l), len(lc))))


def run_pairs(l):
    out = []
    n = len(l)
    i = 0
    while i < n:
        j = i
        while j < n and l[j] == l[i]:
            j += 1
        out.append((j - i, l[i] - part(l, j + 1)))
        i = j
    return out


def ends(l):
    """(k, L, R) of the run pairs of l."""
    pr = run_pairs(l)
    k = len(pr)
    left = 0
    while left < k and pr[left][0] == 1 and pr[left][1] % 2 == 1:
        left += 1
    right = 0
    while right < k and pr[k - 1 - right][0] % 2 == 1 and pr[k - 1 - right][1] == 1:
        right += 1
    return k, left, right


def zeng_is_p(l):
    k, left, right = ends(l)
    return (len(l) + part(l, 1)) % 2 == 0 and min(k, left + right) % 2 == 0


def meld(mu, lam):
    return tuple(x + part(mu, 1) for x in lam) + mu


def durfee(l):
    d = 0
    for t in range(1, len(l) + 1):
        if t <= l[t - 1]:
            d = t
    return d


def stack(l, m):
    """The paper's stack l <| m, or None when it is undefined."""
    d = durfee(l)
    k = len(m)
    if all(part(l, d + i) == d for i in range(1, k + 1)) and part(l, d) >= d + part(m, 1):
        return l[:d] + tuple(part(l, d + i) + m[i - 1] for i in range(1, k + 1)) + l[d + k:]
    return None


def hook(r, c):
    return (c,) + (1,) * (r - 1)


def ee_hook(l):
    """l is a hook [c, 1^(r-1)] with r, c >= 2 both even."""
    return (len(l) >= 2 and len(l) % 2 == 0 and l[0] >= 2 and l[0] % 2 == 0
            and all(x == 1 for x in l[1:]))


def mex(values):
    m = 0
    while m in values:
        m += 1
    return m


def stack_closure(pieces, nesting, max_n):
    """All stacks of pieces of total size <= max_n, as {partition: ends in [1]}.

    nesting 'right' adds h <| x, 'left' adds x <| h (h a piece), and 'any'
    adds x <| y for x, y already obtained, which covers every bracketing.
    """
    by_size = {}
    for h in pieces:
        by_size.setdefault(sum(h), {})[h] = h == (1,)
    for s in range(1, max_n + 1):
        for s1 in range(1, s):
            s2 = s - s1
            left = by_size.get(s1, {})
            right = by_size.get(s2, {})
            if nesting == 'right':
                left = {h: h == (1,) for h in pieces if sum(h) == s1}
            if nesting == 'left':
                right = {h: h == (1,) for h in pieces if sum(h) == s2}
            for x in left:
                for y, flag in right.items():
                    z = stack(x, y)
                    if z is not None:
                        assert sum(z) == s
                        cur = by_size.setdefault(s, {})
                        cur[z] = cur.get(z, False) or flag
    out = {}
    for d in by_size.values():
        for z, flag in d.items():
            out[z] = out.get(z, False) or flag
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--max-n', type=int, required=True)
    ap.add_argument('--misere', action='store_true')
    ap.add_argument('--hookswap', action='store_true')
    args = ap.parse_args()
    N = args.max_n
    failures = 0

    def fail(msg):
        nonlocal failures
        failures += 1
        if failures <= 20:
            print('FAIL', msg)

    # Outcomes: bit 1 = normal P, bit 2 = misere P.
    out = {}
    n_part = n_p = n_ps = n_ps_n = n_ps_weak = n_mp = n_cover = 0
    target = set()        # parity self-conjugate N-positions (paper's reading)
    target_weak = set()   # the same with the weaker reading
    cp = {}               # Conway pairs (with --hookswap)
    n_cp01 = n_ee = 0
    for n in range(N + 1):
        c_part = c_p = c_ps = c_mp = 0
        for l in partitions(n):
            opts = moves(l)
            is_p = not any(out[m] & 1 for m in opts)
            is_mp = bool(l) and not any(out[m] & 2 for m in opts)
            out[l] = (1 if is_p else 0) | (2 if is_mp else 0)
            c_part += 1
            c_p += is_p
            c_mp += is_mp
            if args.hookswap:
                sg = mex({cp[m][0] for m in opts})
                msg = mex({cp[m][1] for m in opts}) if l else 1
                cp[l] = (sg, msg)
                if (sg == 0) != is_p or (msg == 0) != is_mp:
                    fail(f'Conway pair {cp[l]} against the outcomes at {l}')
                if l:
                    n_cp01 += cp[l] == (0, 1)
                    n_ee += ee_hook(l)
                    if (cp[l] == (0, 1)) != ee_hook(l):
                        fail(f'conj:hookswap at {l}: Conway pair {cp[l]}')
            if zeng_is_p(l) != is_p:
                fail(f'Zeng rule at {l}')
            k, left, right = ends(l)
            cover = left + right >= k
            n_cover += cover
            if args.misere and is_mp != (is_p != cover):
                fail(f'misere rule at {l}: misere P = {is_mp}, P = {is_p}, cover = {cover}')
            if pself(l):
                c_ps += 1
                if left != right or (len(l) + part(l, 1)) % 2 != 0:
                    fail(f'L = R or even boundary length at pself {l}')
                if cover and conjugate(l) != l:
                    fail(f'pself cover position {l} is not self-conjugate')
                if not is_p:
                    target.add(l)
            if pself_weak(l):
                n_ps_weak += 1
                if not is_p:
                    target_weak.add(l)
        n_part += c_part
        n_p += c_p
        n_ps += c_ps
        n_mp += c_mp
        print(f'n={n} partitions={c_part} P={c_p} misereP={c_mp} pself={c_ps}', flush=True)
    n_ps_n = len(target)

    # 2. Meld of losing thick hooks.
    thick = {}
    for r in range(3, N + 1):
        for a in range(2, r):
            for c in range(3, N + 1):
                for b in range(2, c):
                    if a * c + (r - a) * b > N:
                        break
                    thick[(c,) * a + (b,) * (r - a)] = (r, c)
    n_thick_p = 0
    for h, (r, c) in thick.items():
        if (out[h] & 1 == 1) != ((r - c) % 2 == 0):
            fail(f'thm:thick-hook at {h}')
        n_thick_p += out[h] & 1
    melds = {h for h in thick if out[h] & 1}
    frontier = set(melds)
    while frontier:
        new = set()
        for x in melds:
            for y in frontier:
                for z in (meld(x, y), meld(y, x)):
                    if sum(z) <= N and z not in melds:
                        new.add(z)
        melds |= new
        frontier = new
    for z in melds:
        if not out[z] & 1:
            fail(f'meld of losing thick hooks {z} is N')
    small = [l for n in range(7) for l in partitions(n)]
    n_assoc = 0
    for x in small:
        if meld(x, ()) != x or meld((), x) != x:
            fail(f'meld unit at {x}')
        for y in small:
            for z in small:
                n_assoc += 1
                if meld(meld(x, y), z) != meld(x, meld(y, z)):
                    fail(f'meld associativity at {x}, {y}, {z}')
    print(f'meld: {len(thick)} thick hooks, {n_thick_p} losing; {len(melds)} melds of losing '
          f'thick hooks of size <= {N} ({len(melds) - n_thick_p} with >= 2 pieces), all P; '
          f'{n_assoc} triples associative')

    # 3. conj:pself under each reading.
    readings = {}
    for hooks in ('odd', 'all'):
        pieces = [hook(r, r) for r in range(1, (N + 1) // 2 + 1)
                  if hooks == 'all' or r % 2 == 1]
        for nesting in ('right', 'left', 'any'):
            cl = stack_closure(pieces, nesting, N)
            for base in ('ends in [1]', 'any'):
                s = {z for z, flag in cl.items() if flag or base == 'any'}
                readings[(hooks, base, nesting)] = s
    for (hooks, base, nesting), s in readings.items():
        miss = sorted(target - s, key=lambda z: (sum(z), z))
        extra = sorted(s - target, key=lambda z: (sum(z), z))
        miss_w = target_weak - s
        extra_w = s - target_weak
        line = (f'pself reading hooks={hooks} base={base} nesting={nesting}: {len(s)} stacks; '
                f'paper reading: {len(miss)} N not stacks, {len(extra)} stacks not pself-N; '
                f'weak reading: {len(miss_w)}, {len(extra_w)}')
        if miss or extra:
            line += f'; first: {(miss + extra)[0]}'
        print(line)
        if (hooks, base) == ('odd', 'ends in [1]') and (miss or extra):
            fail(f'conj:pself fails for nesting {nesting}')
    print(f'pself: {n_ps} parity self-conjugate partitions ({n_ps_n} N); weak reading: '
          f'{n_ps_weak} ({len(target_weak)} N)')

    if args.hookswap:
        print(f'hookswap: cp([]) = {cp[()]}; {n_cp01} nonempty positions with Conway pair '
              f'(0, 1) and {n_ee} even-by-even hooks of size <= {N}')

    status = 'OK' if failures == 0 else 'FAILED'
    print(f'summary: {status} N={N} partitions={n_part} P={n_p} misereP={n_mp} cover={n_cover} '
          f'misere_checked={args.misere} hookswap_checked={args.hookswap} failures={failures}')
    return 0 if failures == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
