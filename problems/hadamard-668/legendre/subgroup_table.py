#!/usr/bin/env python3
"""Class table for multiplier-invariant Legendre pairs of length 333 (standard library only).

For every subgroup H of G = (Z/333)^* (order 216, G = C6 x C36, 80 subgroups) the class C(H)
consists of the Legendre pairs (A, B) of length 333 with sum(A) = sum(B) = 1 and BOTH A and B
constant on the H-orbits of Z/333.  C(H') is contained in C(H) whenever H <= H'.  This script
recomputes every exact (integer) criterion used in the README and prints the table:

  mod3    H contains h = 2 (mod 3).  Then the 3-compressions satisfy v = w, so
          PSD_A(111) = (u - v)^2 is a square for A and B and 668 = PSD_A(111) + PSD_B(111) would
          be a sum of two squares; 668 = 4 * 167 with 167 = 3 (mod 4) is not.
  mod37   H mod 37 = (Z/37)^*.  Then the 37-compression is (c0, x, ..., x), PSD_A(9k) = (c0 - x)^2
          for 37 not dividing k, and the same contradiction arises.
  sum     no sign vector on the H-orbits has sum 1 (exact DP over orbit sizes).
  T111    no sign vector with sum 1 has an admissible 3-compression (u, v, w): N(u,v,w) and
          668 - N(u,v,w) must both be Eisenstein norms of triples of odd numbers in [-111, 111]
          with sum 1.  Counted by two independent exact methods.
  A37     (only when H mod 9 = <4>) additionally N(a0, a3, a6) and 668 - N(a0, a3, a6) must be
          norms of triples of odd numbers in [-37, 37] (PSD_A(37), as a is constant on
          {1,4,7} and {2,5,8}).
  C(m)    no compressed pair of length 37 is invariant under the order-m subgroup H mod 37
          (m = 4, 12, 36): recomputed by comp_pairs.cpp and comp37_exact.py (see README).
  search  exhaustive meet-in-the-middle searches (lp_orbit_search.cpp and lp_column_search.cpp,
          survivor sets cross-checked), logs in logs/.
  comp111 no H-invariant 3-compressed pair of length 111 (lp_comp111.cpp and
          lp_comp111_check.py agree), logs in logs/.
  lift    exhaustive search over all H-invariant A whose length-111 compression is admissible
          (lp_lift111.cpp and lp_column_search.cpp in a111 mode, identical survivor sets), logs/.
  contains  H contains a subgroup K whose class is already empty (C(H) <= C(K)).
Classes with none of these reasons are reported as OPEN.

Usage: python3 subgroup_table.py
"""
from collections import Counter
from math import gcd

L = 333
# results of the external computations (README, logs/): order of H mod 37 with C(m) empty,
# generators of subgroups excluded by exhaustive search / by the 3-compression search
CM_EMPTY = {4, 12, 36}
SEARCH = {(46,), (28,)}
COMP111 = {(85,), (175,)}
LIFT = {(64,)}


def gen(gs):
    S, todo = {1}, [1]
    while todo:
        x = todo.pop()
        for g in gs:
            y = x * g % L
            if y not in S:
                S.add(y)
                todo.append(y)
    return frozenset(S)


def orbits(H):
    seen, out = set(), []
    for x in range(L):
        if x not in seen:
            o = sorted({h * x % L for h in H})
            seen.update(o)
            out.append(o)
    return out


def norm(a, b, c):
    return a * a + b * b + c * c - a * b - b * c - c * a


def sum_dp(sizes):
    d = {0: 1}
    for s in sizes:
        nd = Counter()
        for k, v in d.items():
            nd[k + s] += v
            nd[k - s] += v
        d = nd
    return d


def main():
    U = [x for x in range(1, L) if gcd(x, L) == 1]
    assert len(U) == 216
    subs = set()
    for a in U:
        for b in U:
            if a <= b:
                subs.add(gen([a, b]))
    subs = sorted(subs, key=lambda s: (len(s), sorted(s)))
    print(f"subgroups of (Z/333)^*: {len(subs)}")
    assert len(subs) == 80

    def mingens(H):
        Hs = sorted(H)
        for a in Hs:
            if gen([a]) == H:
                return (a,)
        for a in Hs:
            for b in Hs:
                if a < b and gen([a, b]) == H:
                    return (a, b)

    # 668 is not a sum of two squares
    assert all(668 - i * i != j * j for i in range(26) for j in range(26))
    # admissible norms
    n111 = set()
    for u in range(-111, 112, 2):
        for v in range(-111, 112, 2):
            w = 1 - u - v
            if abs(w) <= 111 and w % 2:
                n111.add(norm(u, v, w))
    A111 = {x for x in n111 if 668 - x in n111}
    n37 = {norm(a, b, c) for a in range(-37, 38, 2) for b in range(-37, 38, 2) for c in range(-37, 38, 2)}
    A37 = {x for x in n37 if 668 - x in n37}
    print("admissible PSD_A(111) values:", sorted(A111))
    print("admissible PSD_A(37) values (H mod 9 = <4>):", sorted(A37))

    info = {}
    for H in subs:
        orbs = orbits(H)
        g = mingens(H)
        rec = {"H": H, "gens": g, "order": len(H), "n": len(orbs),
               "img9": len({h % 9 for h in H}), "img37": len({h % 37 for h in H})}
        reasons = []
        if any(h % 3 == 2 for h in H):
            reasons.append("mod3")
        else:
            if rec["img37"] == 36:
                reasons.append("mod37")
            if rec["img37"] in CM_EMPTY:
                reasons.append(f"C({rec['img37']})")
            sizes = [len(o) for o in orbs]
            s1 = sum_dp(sizes).get(1, 0)
            rec["sum1"] = s1
            if s1 == 0:
                reasons.append("sum")
            # T111, method 1: 1-D DPs per residue class mod 3, combined over (u, v)
            cls = {0: [], 1: [], 2: []}
            for o in orbs:
                r = {x % 3 for x in o}
                assert len(r) == 1
                cls[r.pop()].append(len(o))
            D = {r: sum_dp(cls[r]) for r in cls}
            t111 = 0
            for u, cu in D[0].items():
                for v, cv in D[1].items():
                    w = 1 - u - v
                    if w in D[2] and norm(u, v, w) in A111:
                        t111 += cu * cv * D[2][w]
            rec["T111"] = t111
            # T111, method 2: one DP over all orbits with state (u, v, w) (small n only)
            if rec["n"] <= 100:
                dp = {(0, 0, 0): 1}
                for o in orbs:
                    wt = [0, 0, 0]
                    for x in o:
                        wt[x % 3] += 1
                    nd = Counter()
                    for (a, b, c), cnt in dp.items():
                        nd[(a + wt[0], b + wt[1], c + wt[2])] += cnt
                        nd[(a - wt[0], b - wt[1], c - wt[2])] += cnt
                    dp = nd
                t2 = sum(cnt for (a, b, c), cnt in dp.items() if a + b + c == 1 and norm(a, b, c) in A111)
                assert t2 == t111, (g, t111, t2)
                rec["T111_checked"] = True
            if s1 and t111 == 0:
                reasons.append("T111")
            if rec["img9"] == 3 and t111:
                # A37: rows 0, 3, 6 (mod 9) separately; v, w as before
                rows = {0: [], 3: [], 6: []}
                for o in orbs:
                    if o[0] % 3 == 0:
                        r9 = {x % 9 for x in o}
                        assert len(r9) == 1
                        rows[r9.pop()].append(len(o))
                R = {r: sum_dp(rows[r]) for r in rows}
                t37 = 0
                for a0, c0 in R[0].items():
                    for a3, c3 in R[3].items():
                        for a6, c6 in R[6].items():
                            if norm(a0, a3, a6) not in A37:
                                continue
                            u = a0 + a3 + a6
                            for v, cv in D[1].items():
                                w = 1 - u - v
                                if w in D[2] and norm(u, v, w) in A111:
                                    t37 += c0 * c3 * c6 * cv * D[2][w]
                rec["T111A37"] = t37
                if t37 == 0:
                    reasons.append("A37")
            if g in SEARCH:
                reasons.append("search")
            if g in COMP111:
                reasons.append("comp111")
            if g in LIFT:
                reasons.append("lift")
        rec["reasons"] = reasons
        info[H] = rec
    # monotonicity: C(H) <= C(K) for K <= H
    for H in subs:
        rec = info[H]
        if not rec["reasons"]:
            for K in subs:
                if K < H and info[K]["reasons"] and "contains" not in info[K]["reasons"][0]:
                    rec["reasons"].append(f"contains <{','.join(map(str, info[K]['gens']))}>")
                    break
            if not rec["reasons"]:
                for K in subs:
                    if K < H and info[K]["reasons"]:
                        rec["reasons"].append(f"contains <{','.join(map(str, info[K]['gens']))}>")
                        break
    nonk3 = [H for H in subs if "mod3" in info[H]["reasons"]]
    print(f"\nsubgroups with an element = 2 (mod 3) (excluded by mod3): {len(nonk3)}")
    k3 = [H for H in subs if H not in nonk3]
    print(f"subgroups of K3 = ker((Z/333)^* -> (Z/3)^*), |K3| = {max(len(H) for H in k3)}: {len(k3)}\n")
    print(f"{'gens':>10} {'|H|':>4} {'orbits':>6} {'H9':>3} {'H37':>4} {'sum=1 vectors':>22} "
          f"{'with T111':>22}  status")
    for H in sorted(k3, key=lambda H: (-len(H), info[H]["n"])):
        r = info[H]
        st = ", ".join(r["reasons"]) if r["reasons"] else "OPEN"
        t = r.get("T111", "")
        if "T111A37" in r:
            t = f"{t} (A37: {r['T111A37']})"
        print(f"{'<' + ','.join(map(str, r['gens'])) + '>':>10} {r['order']:>4} {r['n']:>6} {r['img9']:>3} "
              f"{r['img37']:>4} {r['sum1']:>22} {str(t):>22}  {st}")
    open_ = [info[H] for H in k3 if not info[H]["reasons"]]
    print(f"\nexcluded classes: {80 - len(open_)} of 80; open: {len(open_)}: "
          + " ".join("<" + ",".join(map(str, r["gens"])) + ">" for r in sorted(open_, key=lambda r: r["n"])))


if __name__ == "__main__":
    main()
