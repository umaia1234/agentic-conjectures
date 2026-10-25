#!/usr/bin/env python3
"""Exact (integer-only) enumeration of U_m-invariant compressed pairs of length P = 37.

Independent re-check of comp_pairs.cpp for m >= 4.  For a Legendre pair (A, B) of length
L = 9 * 37 = 333 with sum 1, the 37-compressions c, d (c_r = sum_{x = r mod 37} A(x)) satisfy
  c_r, d_r odd, |c_r|, |d_r| <= 9, sum(c) = sum(d) = 1,
  PAF_c(s) + PAF_d(s) = -18 (s != 0),  sum c^2 + sum d^2 = 650.
If the multiplier group of the pair maps onto a group containing the order-m subgroup U_m of
(Z/37)^*, both c and d are constant on the cosets of U_m.  Every member of a pair has
sum c^2 = 650 - sum d^2 <= 650 - 37 = 613 (sum d^2 >= 1 + 36), so it suffices to enumerate all
U_m-invariant c with sum 1 and sum c^2 <= 613 and to match exact PAF vectors computed at EVERY
shift s = 0..36 (no use of the invariance in the key, no floating point).

Output: the admissible c (those with a partner) as "c_0 x_1 ... x_k", cosets ordered by their
least element, which is the format read by lp_column_search.

Usage: python3 comp37_exact.py m [out_file]     (numpy is used when available, else pure Python)
"""
import sys

P, Q = 37, 9
PARS, LAM = 2 * 9 * 37 + 2 - 2 * Q, -2 * Q  # 650, -18


def cosets(m):
    g = 2  # primitive root mod 37
    assert len({pow(g, i, P) for i in range(P - 1)}) == P - 1
    U = sorted({pow(g, (P - 1) // m * i, P) for i in range(m)})
    cos, seen = [], set()
    for r in range(1, P):
        if r not in seen:
            c = sorted({r * u % P for u in U})
            cos.append(c)
            seen.update(c)
    return cos


def vectors(m):
    cos = cosets(m)
    k = len(cos)
    vals = list(range(-Q, Q + 1, 2))
    out = []
    for c0 in vals:
        if (1 - c0) % m:
            continue
        S = (1 - c0) // m
        budget = PARS - (1 + m * k) - c0 * c0  # m * sum x^2 <= budget
        if budget < 0:
            continue
        xs = []

        def rec(i, s, sq):
            rem = k - i
            if rem == 0:
                if s == S:
                    out.append([c0] + xs[:])
                return
            for v in vals:
                s2, sq2 = s + v, sq + v * v
                # remaining rem-1 entries each have square >= 1 and |entry| <= Q
                if m * (sq2 + (rem - 1)) > budget:
                    continue
                if abs(S - s2) > Q * (rem - 1) or (S - s2 - (rem - 1)) % 2:
                    continue
                xs.append(v)
                rec(i + 1, s2, sq2)
                xs.pop()

        rec(0, 0, 0)
    return cos, out


def full_seq(cos, v):
    seq = [0] * P
    seq[0] = v[0]
    for i, c in enumerate(cos):
        for r in c:
            seq[r] = v[1 + i]
    return seq


def pafs(seqs):
    try:
        import numpy as np
    except ImportError:
        np = None
    if np is not None and seqs:
        C = np.array(seqs, dtype=np.int64)
        cols = [(C * np.roll(C, -s, axis=1)).sum(axis=1) for s in range(P)]
        M = np.stack(cols, axis=1)
        return [tuple(int(t) for t in row) for row in M]
    return [tuple(sum(a[i] * a[(i + s) % P] for i in range(P)) for s in range(P)) for a in seqs]


def main():
    m = int(sys.argv[1])
    out = sys.argv[2] if len(sys.argv) > 2 else None
    cos, vecs = vectors(m)
    seqs = [full_seq(cos, v) for v in vecs]
    assert all(sum(s) == 1 for s in seqs)
    keys = pafs(seqs)
    index = {}
    for i, k in enumerate(keys):
        index.setdefault(k, []).append(i)
    adm, pairs = set(), 0
    for i, k in enumerate(keys):
        w = (PARS - k[0],) + tuple(LAM - t for t in k[1:])
        if w in index:
            pairs += len(index[w])
            adm.add(tuple(vecs[i]))
    print(f"m={m} cosets={len(cos)} parseval_feasible_vectors={len(vecs)} "
          f"ordered_pairs={pairs} admissible={len(adm)}")
    if out:
        with open(out, "w") as f:
            for v in sorted(adm):
                f.write(" ".join(map(str, v)) + "\n")


if __name__ == "__main__":
    main()
