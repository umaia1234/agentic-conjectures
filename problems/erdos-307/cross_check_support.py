#!/usr/bin/env python3
"""Independent re-implementation of the Erdős #307 exhaustive exclusions.

This script is written separately from ``support_mitm.cpp`` and deliberately
uses different ingredients: quadratic-residue tables instead of Euler's
criterion, row bitsets for the final test, exact ``Fraction`` budgets with the
scale ``2^62`` (ambiguous budget cases are resolved exactly), sorting-based
tables, the opposite half split and a different weight boundary between the
two meet-in-the-middle cases.  The ``brute`` and ``mitm`` modes need numpy and
numba (research environment only); ``fiftynine`` uses only the standard library.

Modes
-----
``fiftynine``
    Re-enumerates every 59-prime union with reciprocal sum at least 2 and
    tests the local Legendre conditions (cross-check of enumerate_59.py).
``brute --K K --keys a,b,...``
    Plain depth-first enumeration of every removal set for support K.  Counts
    all of them (exactly), the key-matched sets for each key size and the
    survivors of the full local test.
``mitm --K K --key CK``
    Meet-in-the-middle enumeration of the key-matched sets for key size CK,
    followed by the full local test.  Its key-matched count and histogram are
    comparable with ``support_mitm.cpp``.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import sys
import time
from fractions import Fraction

try:
    import numpy as np
except ImportError:  # the fiftynine mode needs only the standard library
    np = None

SCALE = 1 << 62
MIN_UNION = 60


def primes_upto(limit: int) -> list[int]:
    flags = [True] * (limit + 1)
    flags[0] = flags[1] = False
    for n in range(2, int(limit ** 0.5) + 1):
        if flags[n]:
            for m in range(n * n, limit + 1, n):
                flags[m] = False
    return [n for n in range(limit + 1) if flags[n]]


def nonresidue_rows(primes: list[int]) -> list[int]:
    """rows[i] = bitmask of j != i with p_j a quadratic non-residue mod p_i (p_i odd)."""
    rows = []
    for i, r in enumerate(primes):
        if r == 2:
            rows.append(0)
            continue
        squares = {(x * x) % r for x in range(1, r)}
        mask = 0
        for j, s in enumerate(primes):
            if j != i and (s % r) not in squares:
                mask |= 1 << j
        rows.append(mask)
    return rows


def passes_local(union: list[int] | tuple[int, ...], index: dict[int, int],
                 rows: list[int]) -> bool:
    bits = 0
    for p in union:
        bits |= 1 << index[p]
    for p in union:
        if p != 2 and bin(rows[index[p]] & bits).count("1") % 2:
            return False
    return True


# ---------------------------------------------------------------------------
# 59-prime unions
# ---------------------------------------------------------------------------

def _subsets_at_most(items: list[int], k: int, limit: Fraction):
    """k-subsets of `items` (ascending primes) with reciprocal sum <= limit."""
    tails = [sum((Fraction(1, p) for p in items[len(items) - r:]), Fraction(0))
             for r in range(k + 1)]

    def rec(pos: int, left: int, acc: Fraction, chosen: list[int]):
        if left == 0:
            yield tuple(chosen)
            return
        for q in range(pos, len(items) - left + 1):
            nacc = acc + Fraction(1, items[q])
            # cheapest completion uses the largest remaining primes
            if nacc + tails[left - 1] > limit:
                continue
            chosen.append(items[q])
            yield from rec(q + 1, left - 1, nacc, chosen)
            chosen.pop()

    yield from rec(0, k, Fraction(0), [])


def _subsets_at_least(pool: list[int], k: int, target: Fraction):
    """k-subsets of `pool` (ascending primes) with reciprocal sum >= target."""
    def rec(pos: int, left: int, acc: Fraction, chosen: list[int]):
        if left == 0:
            if acc >= target:
                yield tuple(chosen)
            return
        for q in range(pos, len(pool) - left + 1):
            # largest completion uses the next smallest primes; it only
            # decreases as q grows, so the loop can stop.
            best = acc + sum((Fraction(1, p) for p in pool[q:q + left]), Fraction(0))
            if best < target:
                break
            chosen.append(pool[q])
            yield from rec(q + 1, left - 1, acc + Fraction(1, pool[q]), chosen)
            chosen.pop()

    yield from rec(0, k, Fraction(0), [])


def mode_fiftynine() -> dict:
    universe = primes_upto(5000)
    base = universe[:59]
    rest = universe[59:]
    two = Fraction(2)
    excess = sum(Fraction(1, p) for p in base) - two
    assert base[-1] == 277 and excess > 0
    # 58 primes never reach 2, and neither do 59 primes avoiding 2.
    assert sum(Fraction(1, p) for p in universe[:58]) < two
    assert sum(Fraction(1, p) for p in universe[1:60]) < two

    def min_loss(k: int) -> Fraction:
        return (sum((Fraction(1, p) for p in base[-k:]), Fraction(0))
                - sum((Fraction(1, p) for p in rest[:k]), Fraction(0)))

    kmax = 0
    while min_loss(kmax + 1) <= excess:
        kmax += 1
    index = {p: i for i, p in enumerate(universe)}
    rows = nonresidue_rows(universe)
    per_k = {}
    candidates = survivors = 0
    for k in range(kmax + 1):
        count_k = 0
        if k == 0:
            count_k = 1
            survivors += passes_local(base, index, rows)
        else:
            max_added = sum((Fraction(1, p) for p in rest[:k]), Fraction(0))
            for removed in _subsets_at_most(base, k, excess + max_added):
                target = sum((Fraction(1, p) for p in removed), Fraction(0)) - excess
                slack = target - sum((Fraction(1, p) for p in rest[:k - 1]), Fraction(0))
                assert slack > 0
                bound = math.floor(1 / slack)  # every added prime is <= bound
                assert bound < universe[-1]
                pool = [p for p in rest if p <= bound]
                kept = [p for p in base if p not in removed]
                for added in _subsets_at_least(pool, k, target):
                    count_k += 1
                    survivors += passes_local(kept + list(added), index, rows)
        per_k[str(k)] = count_k
        candidates += count_k
    return {"mode": "fiftynine", "max_replacements": kmax,
            "reciprocal_feasible_59_sets": candidates,
            "by_replacements": per_k, "survivors": survivors}


# ---------------------------------------------------------------------------
# Shared setup for bounded support
# ---------------------------------------------------------------------------

class Support:
    def __init__(self, K: int):
        primes = primes_upto(2000)
        self.K = K
        self.primes = primes[:K]
        self.next_prime = primes[K]
        delta = sum(Fraction(1, p) for p in self.primes) - 2
        assert delta > 0
        self.delta = delta
        self.budget = math.floor(delta * SCALE)  # exact floor of 2^62 * delta
        self.weights = [SCALE // p for p in self.primes]
        self.maxR = K - MIN_UNION
        rows = nonresidue_rows(self.primes)
        self.rows = rows
        cols = [0] * K
        for i in range(K):
            for j in range(K):
                if (rows[i] >> j) & 1:
                    cols[j] |= 1 << i
        self.cols = cols
        c0 = 0
        for j in range(K):
            c0 ^= cols[j]
        self.c0 = c0
        self.odd = sum(1 << i for i in range(1, K))
        self.removable = [j for j in range(1, K) if self.weights[j] <= self.budget]
        assert self.weights[0] > self.budget  # 2 is never removed

    def exact_feasible(self, removed_mask: int) -> bool:
        s = sum(Fraction(1, self.primes[j]) for j in range(self.K) if (removed_mask >> j) & 1)
        return s <= self.delta

    def full_check(self, removed_mask: int) -> bool:
        union = ((1 << self.K) - 1) & ~removed_mask
        for i in range(1, self.K):
            if (union >> i) & 1 and bin(self.rows[i] & union).count("1") % 2:
                return False
        return True


def split128(x: int) -> tuple[int, int]:
    return x & ((1 << 64) - 1), x >> 64


def _numba():
    import numba
    return numba


# ---------------------------------------------------------------------------
# Brute force
# ---------------------------------------------------------------------------

def build_brute_kernel():
    nb = _numba()

    @nb.njit(cache=True, parallel=True)
    def run(tasks, idx, w, colLo, colHi, budget, maxR, c0Lo, c0Hi, oddLo, oddHi,
            kLo, kHi, nchunks):
        n = idx.shape[0]
        nkeys = kLo.shape[0]
        total = np.zeros(nchunks, np.int64)
        amb = np.zeros(nchunks, np.int64)
        matched = np.zeros((nchunks, nkeys), np.int64)
        surv = np.zeros(nchunks, np.int64)
        ambmask = np.zeros((nchunks, 64, 2), np.uint64)
        survmask = np.zeros((nchunks, 64, 2), np.uint64)
        ntasks = tasks.shape[0]
        for ch in nb.prange(nchunks):
            spos = np.zeros(80, np.int64)
            sw = np.zeros(80, np.int64)
            szl = np.zeros(80, np.uint64)
            szh = np.zeros(80, np.uint64)
            srl = np.zeros(80, np.uint64)
            srh = np.zeros(80, np.uint64)
            ssz = np.zeros(80, np.int64)
            for t in range(ch, ntasks, nchunks):
                # task = list of chosen positions (-1 padded); the node itself is
                # visited and, if `expand`, so is its whole subtree.
                wt = 0
                zl = c0Lo
                zh = c0Hi
                rl = np.uint64(0)
                rh = np.uint64(0)
                sz = 0
                last = -1
                for k in range(tasks.shape[1] - 1):
                    q = tasks[t, k]
                    if q < 0:
                        break
                    j = idx[q]
                    wt += w[q]
                    zl ^= colLo[j]
                    zh ^= colHi[j]
                    if j < 64:
                        rl |= np.uint64(1) << np.uint64(j)
                    else:
                        rh |= np.uint64(1) << np.uint64(j - 64)
                    sz += 1
                    last = q
                expand = tasks[t, tasks.shape[1] - 1]
                depth = 0
                spos[0] = last + 1
                sw[0] = wt
                szl[0] = zl
                szh[0] = zh
                srl[0] = rl
                srh[0] = rh
                ssz[0] = sz
                visit = True
                while depth >= 0:
                    if visit:
                        visit = False
                        cw = sw[depth]
                        czl = szl[depth]
                        czh = szh[depth]
                        crl = srl[depth]
                        crh = srh[depth]
                        csz = ssz[depth]
                        total[ch] += 1
                        if cw + csz > budget:
                            a = amb[ch]
                            if a < 64:
                                ambmask[ch, a, 0] = crl
                                ambmask[ch, a, 1] = crh
                            amb[ch] += 1
                        bl = czl & ~crl
                        bh = czh & ~crh
                        for k in range(nkeys):
                            if (bl & kLo[k]) == 0 and (bh & kHi[k]) == 0:
                                matched[ch, k] += 1
                        if (bl & oddLo) == 0 and (bh & oddHi) == 0:
                            s = surv[ch]
                            if s < 64:
                                survmask[ch, s, 0] = crl
                                survmask[ch, s, 1] = crh
                            surv[ch] += 1
                        if expand == 0:
                            break
                    q = spos[depth]
                    if q >= n or ssz[depth] >= maxR:
                        depth -= 1
                        continue
                    spos[depth] = q + 1
                    nw = sw[depth] + w[q]
                    if nw > budget:
                        continue
                    j = idx[q]
                    d = depth + 1
                    sw[d] = nw
                    szl[d] = szl[depth] ^ colLo[j]
                    szh[d] = szh[depth] ^ colHi[j]
                    if j < 64:
                        srl[d] = srl[depth] | (np.uint64(1) << np.uint64(j))
                        srh[d] = srh[depth]
                    else:
                        srl[d] = srl[depth]
                        srh[d] = srh[depth] | (np.uint64(1) << np.uint64(j - 64))
                    ssz[d] = ssz[depth] + 1
                    spos[d] = q + 1
                    depth = d
                    visit = True
        return total, amb, matched, surv, ambmask, survmask

    return run


def mode_brute(K: int, keys: list[int], threads: int) -> dict:
    sup = Support(K)
    idx = np.array(sup.removable, dtype=np.int64)
    w = np.array([sup.weights[j] for j in sup.removable], dtype=np.int64)
    colLo = np.array([split128(c)[0] for c in sup.cols], dtype=np.uint64)
    colHi = np.array([split128(c)[1] for c in sup.cols], dtype=np.uint64)
    c0Lo, c0Hi = (np.uint64(v) for v in split128(sup.c0))
    oddLo, oddHi = (np.uint64(v) for v in split128(sup.odd))
    kLo = np.array([split128(((1 << (ck + 1)) - 1) & ~1)[0] for ck in keys], dtype=np.uint64)
    kHi = np.array([split128(((1 << (ck + 1)) - 1) & ~1)[1] for ck in keys], dtype=np.uint64)
    # Tasks: the empty set alone, every 1-set alone, and every feasible 2-set
    # together with its subtree.
    n = len(idx)
    task_rows = [[-1, -1, 0]]
    for a in range(n):
        if w[a] <= sup.budget and sup.maxR >= 1:
            task_rows.append([a, -1, 0])
            for b in range(a + 1, n):
                if w[a] + w[b] <= sup.budget and sup.maxR >= 2:
                    task_rows.append([a, b, 1])
    tasks = np.array(task_rows, dtype=np.int64)
    run = build_brute_kernel()
    started = time.time()
    total, amb, matched, surv, ambmask, survmask = run(
        tasks, idx, w, colLo, colHi, np.int64(sup.budget), sup.maxR, c0Lo, c0Hi, oddLo, oddHi,
        kLo, kHi, max(1, threads) * 64)
    elapsed = time.time() - started
    ambiguous = int(amb.sum())
    resolved_infeasible = 0
    if ambiguous:
        if int(amb.max()) > 64:
            raise SystemExit("too many ambiguous budget cases to resolve")
        for ch in range(amb.shape[0]):
            for a in range(int(amb[ch])):
                m = int(ambmask[ch, a, 0]) | (int(ambmask[ch, a, 1]) << 64)
                if not sup.exact_feasible(m):
                    resolved_infeasible += 1
    survivors = int(surv.sum())
    confirmed = 0
    for ch in range(surv.shape[0]):
        for s in range(min(64, int(surv[ch]))):
            m = int(survmask[ch, s, 0]) | (int(survmask[ch, s, 1]) << 64)
            if sup.exact_feasible(m) and sup.full_check(m):
                confirmed += 1
    return {
        "mode": "brute", "K": K, "largest_support_prime": sup.primes[-1],
        "next_prime": sup.next_prime, "max_removed": sup.maxR,
        "removal_sets_budget_superset": int(total.sum()),
        "ambiguous_budget": ambiguous,
        "ambiguous_resolved_infeasible": resolved_infeasible,
        "removal_sets_exact": int(total.sum()) - resolved_infeasible,
        "key_matched": {str(k): int(matched[:, i].sum()) for i, k in enumerate(keys)},
        "survivors": survivors, "confirmed_survivors": confirmed,
        "seconds": round(elapsed, 1),
    }


# ---------------------------------------------------------------------------
# Meet in the middle
# ---------------------------------------------------------------------------

def build_mitm_kernels():
    nb = _numba()


    @nb.njit(cache=True)
    def count_subsets(w, budget, maxR):
        n = w.shape[0]
        pos = np.zeros(40, np.int64)
        ws = np.zeros(40, np.int64)
        cnt = 1
        depth = 0
        pos[0] = 0
        ws[0] = 0
        while depth >= 0:
            q = pos[depth]
            if q >= n or depth >= maxR:
                depth -= 1
                continue
            pos[depth] = q + 1
            nw = ws[depth] + w[q]
            if nw > budget:
                continue
            cnt += 1
            depth += 1
            ws[depth] = nw
            pos[depth] = q + 1
        return cnt

    @nb.njit(cache=True)
    def fill_subsets(w, key, budget, maxR, hb, out):
        # out[i] = (key << hb) | mask over all subsets with weight <= budget
        n = w.shape[0]
        pos = np.zeros(40, np.int64)
        ws = np.zeros(40, np.int64)
        ks = np.zeros(40, np.uint64)
        ms = np.zeros(40, np.uint64)
        out[0] = np.uint64(0)
        cnt = 1
        depth = 0
        while depth >= 0:
            q = pos[depth]
            if q >= n or depth >= maxR:
                depth -= 1
                continue
            pos[depth] = q + 1
            nw = ws[depth] + w[q]
            if nw > budget:
                continue
            d = depth + 1
            ws[d] = nw
            ks[d] = ks[depth] ^ key[q]
            ms[d] = ms[depth] | (np.uint64(1) << np.uint64(q))
            out[cnt] = (ks[d] << np.uint64(hb)) | ms[d]
            cnt += 1
            pos[d] = q + 1
            depth = d
        return cnt

    @nb.njit(cache=True)
    def pair_stats(mask, w, idx, colLo, colHi):
        """Weight, size, XOR of columns and removed bits of one half-subset."""
        wt = 0
        sz = 0
        tl = np.uint64(0)
        th = np.uint64(0)
        rl = np.uint64(0)
        rh = np.uint64(0)
        q = 0
        while mask:
            if mask & np.uint64(1):
                wt += w[q]
                sz += 1
                j = idx[q]
                tl ^= colLo[j]
                th ^= colHi[j]
                if j < 64:
                    rl |= np.uint64(1) << np.uint64(j)
                else:
                    rh |= np.uint64(1) << np.uint64(j - 64)
            mask >>= np.uint64(1)
            q += 1
        return wt, sz, tl, th, rl, rh

    @nb.njit(cache=True, parallel=True)
    def run(tasks, xw, xsz, xkey, xwild, xlo, xhi, xtlo, xthi,
            w0, key0, idx0, ent0, start0, sh0, hb0,
            w1, key1, idx1, ent1, start1, sh1, hb1,
            budget, maxR, c0key, colLo, colHi, oddLo, oddHi, nchunks):
        # Half "a" has arrays *0, half "b" has arrays *1; m = (bx + 1) // 2.
        # case 0: iterate subsets A of half a with w(A) <= m, look up half b.
        # case 1: iterate subsets B of half b with w(B) <= bx - m - 1, look up
        #         half a and keep only entries with w(A) > m.
        matched = np.zeros((nchunks, maxR + 1), np.int64)
        amb = np.zeros(nchunks, np.int64)
        surv = np.zeros(nchunks, np.int64)
        nodes = np.zeros(nchunks, np.int64)
        ntasks = tasks.shape[0]
        for ch in nb.prange(nchunks):
            pos = np.zeros(40, np.int64)
            ws = np.zeros(40, np.int64)
            ks = np.zeros(40, np.uint64)
            ms = np.zeros(40, np.uint64)
            for t in range(ch, ntasks, nchunks):
                xi = tasks[t, 0]
                case = tasks[t, 1]
                first = tasks[t, 2]
                bx = budget - xw[xi]
                m = (bx + 1) // 2
                rx = maxR - xsz[xi]
                if case == 0:
                    itw = w0
                    itkey = key0
                    itidx = idx0
                    tw = w1
                    tidx = idx1
                    ent = ent1
                    start = start1
                    sh = sh1
                    hb = hb1
                    cap = m
                else:
                    itw = w1
                    itkey = key1
                    itidx = idx1
                    tw = w0
                    tidx = idx0
                    ent = ent0
                    start = start0
                    sh = sh0
                    hb = hb0
                    cap = bx - m - 1
                if cap < 0:
                    continue
                n = itw.shape[0]
                mlow = (np.uint64(1) << np.uint64(hb)) - np.uint64(1)
                wild = xwild[xi]
                whigh = wild >> np.uint64(sh)
                if first < 0:
                    ws[0] = 0
                    ks[0] = np.uint64(0)
                    ms[0] = np.uint64(0)
                    pos[0] = n
                    sz0 = 0
                else:
                    if rx < 1 or itw[first] > cap:
                        continue
                    ws[0] = itw[first]
                    ks[0] = itkey[first]
                    ms[0] = np.uint64(1) << np.uint64(first)
                    pos[0] = first + 1
                    sz0 = 1
                depth = 0
                visit = True
                while depth >= 0:
                    if visit:
                        visit = False
                        nodes[ch] += 1
                        need = c0key ^ xkey[xi] ^ ks[depth]
                        nh = need >> np.uint64(sh)
                        s = whigh
                        while True:
                            bk = np.int64(nh ^ s)
                            for e in range(start[bk], start[bk + 1]):
                                if (((ent[e] >> np.uint64(hb)) ^ need) & ~wild) != 0:
                                    continue
                                wb, sb, tl, th, rl, rh = pair_stats(ent[e] & mlow, tw, tidx,
                                                                   colLo, colHi)
                                if case == 1 and wb <= m:
                                    continue
                                wa = ws[depth]
                                sa = sz0 + depth
                                if wa + wb > bx or sa + sb > rx:
                                    continue
                                wa2, sa2, tl2, th2, rl2, rh2 = pair_stats(ms[depth], itw, itidx,
                                                                          colLo, colHi)
                                total_sz = xsz[xi] + sa + sb
                                matched[ch, total_sz] += 1
                                if xw[xi] + wa + wb + total_sz > budget:
                                    amb[ch] += 1
                                rl = rl | rl2 | xlo[xi]
                                rh = rh | rh2 | xhi[xi]
                                zl = xtlo[xi] ^ tl ^ tl2
                                zh = xthi[xi] ^ th ^ th2
                                if (zl & ~rl & oddLo) == 0 and (zh & ~rh & oddHi) == 0:
                                    surv[ch] += 1
                            if s == 0:
                                break
                            s = (s - np.uint64(1)) & whigh
                    q = pos[depth]
                    if q >= n or sz0 + depth >= rx:
                        depth -= 1
                        continue
                    pos[depth] = q + 1
                    nw = ws[depth] + itw[q]
                    if nw > cap:
                        continue
                    d = depth + 1
                    ws[d] = nw
                    ks[d] = ks[depth] ^ itkey[q]
                    ms[d] = ms[depth] | (np.uint64(1) << np.uint64(q))
                    pos[d] = q + 1
                    depth = d
                    visit = True
        return matched, amb, surv, nodes

    return count_subsets, fill_subsets, run


def mode_mitm(K: int, CK: int, threads: int) -> dict:
    nb = _numba()
    sup = Support(K)
    assert 8 <= CK < K - 1
    keybit = {i: CK - i for i in range(1, CK + 1)}  # coordinate -> key bit

    def key_of(mask: int) -> int:
        k = 0
        for i in range(1, CK + 1):
            if (mask >> i) & 1:
                k |= 1 << keybit[i]
        return k

    L = [j for j in sup.removable if j <= CK]
    H = [j for j in sup.removable if j > CK]
    half_a = H[1::2]
    half_b = H[0::2]
    assert len(half_a) <= 30 and len(half_b) <= 30 and CK + 30 <= 64
    count_subsets, fill_subsets, run = build_mitm_kernels()

    def table(half: list[int]):
        w = np.array([sup.weights[j] for j in half], dtype=np.int64)
        key = np.array([key_of(sup.cols[j]) for j in half], dtype=np.uint64)
        hb = len(half)
        n = count_subsets(w, np.int64(sup.budget), sup.maxR)
        ent = np.empty(n, dtype=np.uint64)
        got = fill_subsets(w, key, np.int64(sup.budget), sup.maxR, hb, ent)
        assert got == n
        ent.sort()
        b = max(0, min(CK, int(math.ceil(math.log2(max(n, 2) / 8)))))
        b = min(b, 28)
        b = max(b, CK - 8)
        sh = CK - b
        bounds = (np.arange((1 << b) + 1, dtype=np.uint64) << np.uint64(sh + hb))
        start = np.searchsorted(ent, bounds, side="left").astype(np.int64)
        start[-1] = n
        idx = np.array(half, dtype=np.int64)
        return w, key, idx, ent, start, sh, hb, n

    t0 = time.time()
    tab_a = table(half_a)
    tab_b = table(half_b)
    # X patterns: subsets of L with weight <= budget and size <= maxR
    xs = []

    def gen(pos, chosen, wt):
        xs.append((list(chosen), wt))
        if len(chosen) == sup.maxR:
            return
        for q in range(pos, len(L)):
            nw = wt + sup.weights[L[q]]
            if nw <= sup.budget:
                chosen.append(L[q])
                gen(q + 1, chosen, nw)
                chosen.pop()

    gen(0, [], 0)
    xw = np.array([wt for _, wt in xs], dtype=np.int64)
    xsz = np.array([len(c) for c, _ in xs], dtype=np.int64)
    xmask = [sum(1 << j for j in c) for c, _ in xs]
    xt = []
    for c, _ in xs:
        t = sup.c0
        for j in c:
            t ^= sup.cols[j]
        xt.append(t)
    xkey = np.array([key_of(t ^ sup.c0) for t in xt], dtype=np.uint64)  # key of XOR over X
    xwild = np.array([key_of(m) for m in xmask], dtype=np.uint64)
    xlo = np.array([split128(m)[0] for m in xmask], dtype=np.uint64)
    xhi = np.array([split128(m)[1] for m in xmask], dtype=np.uint64)
    xtlo = np.array([split128(t)[0] for t in xt], dtype=np.uint64)
    xthi = np.array([split128(t)[1] for t in xt], dtype=np.uint64)
    c0key = np.uint64(key_of(sup.c0))
    colLo = np.array([split128(c)[0] for c in sup.cols], dtype=np.uint64)
    colHi = np.array([split128(c)[1] for c in sup.cols], dtype=np.uint64)
    oddLo, oddHi = (np.uint64(v) for v in split128(sup.odd))
    rows = []
    for xi in range(len(xs)):
        for case, half in ((0, half_a), (1, half_b)):
            rows.append((xi, case, -1))
            for q in range(len(half)):
                rows.append((xi, case, q))
    tasks = np.array(rows, dtype=np.int64)
    build_seconds = time.time() - t0
    wa_, ka_, ia_, ea_, sa_, sha, hba, na = tab_a
    wb_, kb_, ib_, eb_, sb_, shb, hbb, nb_ = tab_b
    matched, amb, surv, nodes = run(
        tasks, xw, xsz, xkey, xwild, xlo, xhi, xtlo, xthi,
        wa_, ka_, ia_, ea_, sa_, sha, hba,
        wb_, kb_, ib_, eb_, sb_, shb, hbb,
        np.int64(sup.budget), sup.maxR, c0key, colLo, colHi, oddLo, oddHi,
        max(1, threads) * 64)
    total_matched = matched.sum(axis=0)
    return {
        "mode": "mitm", "K": K, "largest_support_prime": sup.primes[-1],
        "next_prime": sup.next_prime, "max_removed": sup.maxR, "key_coordinates": CK,
        "x_patterns": len(xs), "table_a": int(na), "table_b": int(nb_),
        "iterated_nodes": int(nodes.sum()),
        "key_matched_feasible": int(total_matched.sum()),
        "key_matched_by_removed": {str(i): int(v) for i, v in enumerate(total_matched) if v},
        "ambiguous_budget": int(amb.sum()), "survivors": int(surv.sum()),
        "build_seconds": round(build_seconds, 1),
        "seconds": round(time.time() - t0, 1),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=["fiftynine", "brute", "mitm"])
    parser.add_argument("--K", type=int)
    parser.add_argument("--keys", default="12,16,20,24,30")
    parser.add_argument("--key", type=int, default=30)
    parser.add_argument("--threads", type=int, default=int(os.environ.get("NUMBA_NUM_THREADS", 3)))
    args = parser.parse_args()
    if args.mode == "fiftynine":
        result = mode_fiftynine()
    elif args.mode == "brute":
        result = mode_brute(args.K, [int(k) for k in args.keys.split(",")], args.threads)
    else:
        result = mode_mitm(args.K, args.key, args.threads)
    print(json.dumps(result, sort_keys=True))
    sys.exit(0 if result.get("survivors", 1) == 0 else 3)


if __name__ == "__main__":
    main()
