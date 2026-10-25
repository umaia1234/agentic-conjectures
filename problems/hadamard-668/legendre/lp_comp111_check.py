#!/usr/bin/env python3
"""Independent re-check of lp_comp111.cpp (implementation 2, numpy).

Same mathematical search, written separately: all H-invariant 3-compressions A' of length
M = L/3 of a Legendre pair of length L = 9P (A'(y) = A(y) + A(y+M) + A(y+2M)) whose
P-compression is listed in c_file, with sum(A'^2) <= 2L - 4 - M, admissible 3-compression
(u, v, w), PSD_A'(k) <= 2L + 2 at EVERY k = 1..M-1 (float filter, tolerance 1e-6), then exact
matching of integer PAF vectors at all M shifts:
    PAF_A'(0) + PAF_B'(0) = 2L - 4,   PAF_A'(s) + PAF_B'(s) = -6  (s != 0).
Differences from implementation 1: the allowed values of A'(y) come from the orbits of the
stabiliser of y (mod M) on the fibre {y, y+M, y+2M}; candidates are generated with numpy over
all orbit values and filtered by ALL P column sums residue by residue; the DFT is a dense matrix
product over all frequencies; PAF vectors use np.roll; matching uses a sorted array.

Usage: python3 lp_comp111_check.py L gens c_file
Prints the same counts as lp_comp111 (candidates, after Parseval+3-compression filters, PSD
survivors, distinct PAF vectors, ordered compressed pairs, admissible A').
"""
import itertools
import sys

import numpy as np


def subgroup(gens, mod):
    H, todo = {1}, [1]
    while todo:
        x = todo.pop()
        for g in gens:
            y = x * g % mod
            if y not in H:
                H.add(y)
                todo.append(y)
    return sorted(H)


def main():
    L = int(sys.argv[1])
    gens = [int(t) % L for t in sys.argv[2].split(",")]
    cfile = sys.argv[3]
    M, P = L // 3, L // 9
    H = subgroup(gens, L)
    # orbits of H mod M on Z/M and allowed values via the stabiliser action on the fibre
    seen, orbs, vals = set(), [], []
    for y in range(M):
        if y in seen:
            continue
        o = sorted({h * y % M for h in H})
        seen.update(o)
        orbs.append(o)
        stab = [h for h in H if h * y % M == y]
        fib, parts, done = [y, y + M, y + 2 * M], [], set()
        for x in fib:
            if x not in done:
                ox = {h * x % L for h in stab}
                done |= ox
                parts.append(len(ox))
        vals.append(sorted({sum(s * e for s, e in zip(parts, es))
                            for es in itertools.product([1, -1], repeat=len(parts))}))
    n = len(orbs)
    # column classes = orbits of H mod P on Z/P, ordered by least element (format of c_file)
    cseen, cls = set(), []
    for r in range(P):
        if r not in cseen:
            c = sorted({h * r % P for h in H})
            cseen.update(c)
            cls.append(c)
    targets = []
    for line in open(cfile):
        t = list(map(int, line.split()))
        if t:
            assert len(t) == len(cls)
            full = [0] * P
            for v, c in zip(t, cls):
                for r in c:
                    full[r] = v
            targets.append(full)
    # admissible norms of the 3-compression
    m3 = L // 3
    norm = lambda a, b, c: a * a + b * b + c * c - a * b - b * c - c * a
    trip = [(u, v, 1 - u - v) for u in range(-m3, m3 + 1, 2) for v in range(-m3, m3 + 1, 2)
            if abs(1 - u - v) <= m3 and (1 - u - v - m3) % 2 == 0]
    norms = {norm(*t) for t in trip}
    allowed = np.array(sorted(x for x in norms if 2 * L + 2 - x in norms))
    PARS, LAM, SQMAX = 2 * L - 4, -6, 2 * L - 4 - M
    # orbit index of every y; candidates: orbit value vectors grouped by column class
    oid = np.zeros(M, dtype=np.int64)
    for k, o in enumerate(orbs):
        oid[o] = k
    col_orbs = [[k for k in range(n) if orbs[k][0] % P in c] for c in cls]
    E = np.exp(2j * np.pi * np.outer(np.arange(M), np.arange(1, M)) / M)
    total, exact_ok, survivors = 0, 0, []
    for tgt in targets:
        # per column: value combos on its orbits whose sum over residue r = min(class) matches
        per = []
        for c, ks in zip(cls, col_orbs):
            r = c[0]
            ok = []
            for combo in itertools.product(*[vals[k] for k in ks]):
                s = sum(v * sum(1 for y in orbs[k] if y % P == r) for k, v in zip(ks, combo))
                if s == tgt[r]:
                    ok.append(combo)
            per.append(np.array(ok, dtype=np.int8).reshape(len(ok), len(ks)))
        cnt = 1
        for p in per:
            cnt *= len(p)
        total += cnt
        if cnt == 0:
            continue
        # chunk over the combos of the first column
        rest = list(range(1, len(per)))
        grids = np.array(list(itertools.product(*[range(len(per[j])) for j in rest])), dtype=np.int64)
        for i0 in range(len(per[0])):
            V = np.zeros((len(grids), n), dtype=np.int8)
            V[:, col_orbs[0]] = per[0][i0]
            for a, j in enumerate(rest):
                V[:, col_orbs[j]] = per[j][grids[:, a]]
            S = V[:, oid]  # full sequences, length M
            colsum = S.reshape(len(S), 3, P).sum(axis=1)  # P-compression, residue by residue
            assert (colsum == np.array(tgt)).all() and (S.sum(axis=1) == 1).all()
            u, v, w = S[:, 0::3].sum(1), S[:, 1::3].sum(1), S[:, 2::3].sum(1)
            keep = ((S * S).sum(1) <= SQMAX) & np.isin(norm(u, v, w), allowed)
            S = S[keep]
            exact_ok += len(S)
            D = S @ E
            psd = D.real ** 2 + D.imag ** 2
            survivors.append(S[(psd <= 2 * L + 2 + 1e-6).all(axis=1)])
    S = np.concatenate(survivors).astype(np.int64) if survivors else np.zeros((0, M), dtype=np.int64)
    paf = np.stack([(S * np.roll(S, -s, axis=1)).sum(axis=1) for s in range(M)], axis=1)
    comp = np.concatenate([PARS - paf[:, :1], LAM - paf[:, 1:]], axis=1)
    keys = np.unique(paf, axis=0)
    # membership of each complement in the key set (sorted lexicographic search)
    kset = {tuple(r) for r in keys.tolist()}
    has = np.array([tuple(r) in kset for r in comp.tolist()], dtype=bool)
    from collections import Counter
    mult = Counter(map(tuple, paf.tolist()))
    pairs = sum(mult[tuple(r)] for r, h in zip(comp.tolist(), has) if h)
    print(f"L={L} gens={sys.argv[2]} orbits={n} candidates={total} after_exact_filters={exact_ok} "
          f"psd_survivors={len(S)} distinct_paf={len(keys)} ordered_pairs={pairs} admissible={int(has.sum())}")


if __name__ == "__main__":
    main()
