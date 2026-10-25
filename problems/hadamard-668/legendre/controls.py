#!/usr/bin/env python3
"""Positive controls for the three search programs (non-vacuous: genuine pairs must be found).

* lp_orbit_search: number of ordered Legendre pairs for (L, H) = (9, 1), (13, 1), (63, <2>),
  (63, <11>) must equal a brute-force count.
* lp_column_search (u3 mode): the same counts for (63, <2>) and (63, <11>) (P = 7).
* lp_comp111: at L = 63 (P = 7, M = 21) the length-21 compression of EVERY brute-force pair in
  C(<2>) and C(<11>) must be reported as admissible.
* lp_lift111 and lp_column_search (a111 mode), run on that admissible list, must find exactly the
  brute-force number of pairs.
The admissible 9-compressions c of length P = 7 constant on the (H mod 7)-orbits (pairs with
PAF_c + PAF_d = -18 off zero and sum c^2 + sum d^2 = 2L - 16) are generated here in the c_file
format "c_0 x_1 ... x_k" (orbits of (Z/7)^* ordered by least element).

Usage: python3 controls.py lp_orbit_search_bin lp_column_search_bin lp_comp111_bin lp_lift111_bin
"""
import itertools
import os
import subprocess
import sys
import tempfile

L, M, P = 63, 21, 7


def paf(a, s):
    n = len(a)
    return sum(a[i] * a[(i + s) % n] for i in range(n))


def brute(Ln, gen):
    H = sorted({pow(gen, k, Ln) for k in range(Ln)})
    orbs, seen = [], set()
    for x in range(Ln):
        if x not in seen:
            o = sorted({h * x % Ln for h in H})
            seen.update(o)
            orbs.append(o)
    keys = {}
    for signs in itertools.product([1, -1], repeat=len(orbs)):
        a = [0] * Ln
        for o, s in zip(orbs, signs):
            for x in o:
                a[x] = s
        if sum(a) == 1:
            keys.setdefault(tuple(paf(a, s) for s in range(1, Ln)), []).append(tuple(a))
    lps = []
    for k, lst in keys.items():
        for b in keys.get(tuple(-2 - v for v in k), []):
            lps.extend((a, b) for a in lst)
    return lps


def pairs_reported(cmd):
    out = subprocess.run(cmd, capture_output=True, text=True, check=True).stdout
    res = [ln for ln in out.splitlines() if ln.startswith("RESULT")][-1]
    print(res)
    return int(res.split("pairs=")[1].split()[0]), res


def run(binary, gen, colsearch, liftbin):
    H = sorted({pow(gen, k, L) for k in range(L)})
    orbs, seen = [], set()
    for x in range(L):
        if x not in seen:
            o = sorted({h * x % L for h in H})
            seen.update(o)
            orbs.append(o)
    seqs = []
    for signs in itertools.product([1, -1], repeat=len(orbs)):
        a = [0] * L
        for o, s in zip(orbs, signs):
            for x in o:
                a[x] = s
        if sum(a) == 1:
            seqs.append(tuple(a))
    keys = {}
    for a in seqs:
        keys.setdefault(tuple(paf(a, s) for s in range(1, L)), []).append(a)
    lps = []
    for k, lst in keys.items():
        comp = tuple(-2 - v for v in k)
        for a in lst:
            for b in keys.get(comp, []):
                lps.append((a, b))
    comp3 = lambda a: tuple(a[y] + a[y + M] + a[y + 2 * M] for y in range(M))
    expected = {comp3(a) for a, _ in lps}
    # admissible P-compressions constant on the (H mod P)-orbits (each entry a sum of 9 signs)
    cls, cseen = [], set()
    for r in range(P):
        if r not in cseen:
            c = sorted({h * r % P for h in H})
            cseen.update(c)
            cls.append(c)
    vals = range(-9, 10, 2)
    pk = {}
    for t in itertools.product(vals, repeat=len(cls)):
        c = [0] * P
        for v, cl in zip(t, cls):
            for r in cl:
                c[r] = v
        if sum(c) == 1:
            pk.setdefault((sum(v * v for v in c),) + tuple(paf(c, s) for s in range(1, P)), []).append(t)
    adm_c = set()
    for k, lst in pk.items():
        if (2 * L - 16 - k[0],) + tuple(-18 - v for v in k[1:]) in pk:
            adm_c.update(lst)
    with tempfile.TemporaryDirectory() as td:
        cf, of = os.path.join(td, "c.txt"), os.path.join(td, "adm.txt")
        with open(cf, "w") as f:
            for c in sorted(adm_c):
                f.write(" ".join(map(str, c)) + "\n")
        out = subprocess.run([binary, str(L), str(gen), cf, of], capture_output=True, text=True, check=True).stdout
        found = {tuple(map(int, line.split())) for line in open(of) if line.strip()}
        got, _ = pairs_reported([colsearch, str(P), str(gen), cf, "u3", "-", "1", "-"])
        if got != len(lps):
            print(f"FAIL: lp_column_search (u3) reports {got} pairs, brute force {len(lps)}")
            sys.exit(1)
        got, _ = pairs_reported([colsearch, str(P), str(gen), cf, "a111", of, "1", "-"])
        if got != len(lps):
            print(f"FAIL: lp_column_search (a111) reports {got} pairs, brute force {len(lps)}")
            sys.exit(1)
        got, _ = pairs_reported([liftbin, str(L), str(gen), of, "1"])
        if got != len(lps):
            print(f"FAIL: lp_lift111 reports {got} pairs, brute force {len(lps)}")
            sys.exit(1)
    print(out.strip().splitlines()[-1])
    print(f"brute force: <{gen}>-invariant Legendre pairs of length {L} (ordered) = {len(lps)}, "
          f"distinct 3-compressions = {len(expected)}, reported admissible = {len(found)}")
    if not lps:
        print("FAIL: no pairs, control is vacuous")
        sys.exit(1)
    if not expected <= found:
        print("FAIL: a compression of a genuine pair was not reported")
        sys.exit(1)


def main():
    orbit_bin, col_bin, comp_bin, lift_bin = sys.argv[1:5]
    for Ln, gen in ((9, 1), (13, 1), (63, 2), (63, 11)):
        want = len(brute(Ln, gen))
        got, _ = pairs_reported([orbit_bin, str(Ln), str(gen), "1"])
        print(f"brute force: ordered Legendre pairs of length {Ln} invariant under <{gen}> = {want}")
        if got != want or want == 0:
            print("FAIL: lp_orbit_search disagrees with brute force (or vacuous control)")
            sys.exit(1)
    for gen in (2, 11):
        run(comp_bin, gen, col_bin, lift_bin)
    print("OK: all positive controls passed")


if __name__ == "__main__":
    main()
