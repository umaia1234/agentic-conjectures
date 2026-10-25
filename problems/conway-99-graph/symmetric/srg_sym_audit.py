#!/usr/bin/env python3
"""Independent audit of the symmetric srg CNFs (standard library only).

For each case in cases.json this script re-derives, without importing
srg_sym_encode.py, (1) the permutation group generators from the recorded
group data, (2) their basic invariants (order, fixed points, cycle type, the
action on the matching of Gamma_1 for rooted cases, invariance of the forced
frame), and (3) the complete DIMACS text of the encoding specified in
../README.md ("Encoding specification").  It then compares the SHA-256 of
that text with the hash recorded in cases.json and, if a CNF file is given,
with that file byte for byte.

Usage:
  python3 srg_sym_audit.py                 # all cases, hashes only
  python3 srg_sym_audit.py CASE [CASE.cnf] # one case, optionally vs a file
  python3 srg_sym_audit.py --write CASE OUT.cnf   # emit the audited CNF
"""
import hashlib
import json
import os
import sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))


def frame(k):
    """Rooted frame: returns (v, matching, label_of, forced)."""
    gamma1 = list(range(1, k + 1))
    matching = [frozenset((2 * i - 1, 2 * i)) for i in range(1, k // 2 + 1)]
    edges1 = set(matching)
    nonadj = [frozenset(p) for p in combinations(gamma1, 2)
              if frozenset(p) not in edges1]
    nonadj.sort(key=lambda s: tuple(sorted(s)))
    label_of = {k + 1 + i: s for i, s in enumerate(nonadj)}
    v = 1 + k + len(nonadj)
    forced = {}
    for x in range(v):
        for y in range(x + 1, v):
            if x == 0:
                forced[(x, y)] = int(y <= k)
            elif y <= k:
                forced[(x, y)] = int(frozenset((x, y)) in edges1)
            elif x <= k:
                forced[(x, y)] = int(x in label_of[y])
    return v, matching, label_of, forced


def cycles_to_map(cycles):
    m = {}
    for cyc in cycles:
        for i, x in enumerate(cyc):
            if x in m:
                raise ValueError("repeated point in cycles")
            m[x] = cyc[(i + 1) % len(cyc)]
    return m


def generators(case):
    v = case["v"]
    gens = []
    if case["rooted"]:
        fv, matching, label_of, _ = frame(case["k"])
        assert fv == v, "v does not match the rooted frame"
        inverse = {s: w for w, s in label_of.items()}
        for cycles in case["generators"]:
            m = cycles_to_map(cycles)
            sig = lambda a: m.get(a, a)
            assert all(1 <= a <= case["k"] for a in m), "sigma acts on Gamma_1"
            g = [0] * v
            for a in range(1, case["k"] + 1):
                g[a] = sig(a)
            for w, s in label_of.items():
                g[w] = inverse[frozenset(sig(a) for a in s)]
            gens.append(g)
    else:
        for gen in case["generators"]:
            if isinstance(gen, dict):
                cycles, start = [], 0
                for length, count in gen["cycle_type"]:
                    for _ in range(count):
                        cycles.append(list(range(start, start + length)))
                        start += length
                assert start == v, "cycle type must cover all vertices"
            else:
                cycles = gen
            m = cycles_to_map(cycles)
            gens.append([m.get(x, x) for x in range(v)])
    for g in gens:
        assert sorted(g) == list(range(v)), "not a permutation"
    return gens


def perm_order(g):
    from math import gcd
    order, seen = 1, set()
    for x in range(len(g)):
        if x not in seen:
            n, y = 0, x
            while y not in seen:
                seen.add(y)
                y = g[y]
                n += 1
            order = order * n // gcd(order, n)
    return order


def cycle_type(g):
    seen, lens = set(), []
    for x in range(len(g)):
        if x not in seen:
            n, y = 0, x
            while y not in seen:
                seen.add(y)
                y = g[y]
                n += 1
            lens.append(n)
    out = {}
    for n in lens:
        out[n] = out.get(n, 0) + 1
    return sorted(out.items(), reverse=True)


def group_elements(gens, v):
    ident = tuple(range(v))
    elems = {ident}
    frontier = [ident]
    while frontier:
        nxt = []
        for h in frontier:
            for g in gens:
                c = tuple(g[h[x]] for x in range(v))
                if c not in elems:
                    elems.add(c)
                    nxt.append(c)
        frontier = nxt
        if len(elems) > 100000:
            raise ValueError("group too large for this audit")
    return elems


def pair_action(case, g):
    """Signed cycle structure of a rooted generator on the k/2 matching pairs."""
    k = case["k"]
    pairs = [(2 * i - 1, 2 * i) for i in range(1, k // 2 + 1)]
    where = {}
    for idx, (a, b) in enumerate(pairs):
        where[a] = (idx, 0)
        where[b] = (idx, 1)
    perm = [where[g[a]][0] for a, _ in pairs]
    seen, out = set(), []
    for i in range(len(pairs)):
        if i in seen:
            continue
        cyc, j = [], i
        while j not in seen:
            seen.add(j)
            cyc.append(j)
            j = perm[j]
        flips = 0
        for j in cyc:
            a = pairs[j][0]
            flips += where[g[a]][1]
        out.append("%d%s" % (len(cyc), "-" if flips % 2 else "+"))
    return sorted(out, key=lambda s: (-int(s[:-1]), s[-1]))


def derive_dimacs(case, gens):
    v, k, lam, mu = case["v"], case["k"], case["lambda"], case["mu"]
    elems = group_elements(gens, v)
    # pair orbits by closure under the whole group
    rep = {}
    for x in range(v):
        for y in range(x + 1, v):
            if (x, y) in rep:
                continue
            orb = set()
            for h in elems:
                a, b = h[x], h[y]
                orb.add((a, b) if a < b else (b, a))
            r = min(orb)
            for p in orb:
                rep[p] = r
    reps = sorted(set(rep.values()))
    num = {r: i + 1 for i, r in enumerate(reps)}

    def var(x, y):
        return num[rep[(x, y) if x < y else (y, x)]]

    vrep = sorted({min(h[x] for h in elems) for x in range(v)})
    # inputs of every block, in specification order
    block_inputs = []
    for x in vrep:
        block_inputs.append(([("e", var(x, y)) for y in range(v) if y != x], k))
    for (x, y) in reps:
        row = []
        for z in range(v):
            if z in (x, y):
                continue
            p, q = sorted((var(x, z), var(y, z)))
            row.append(("e", p) if p == q else ("and", (p, q)))
        if mu > lam:
            row.extend([("e", var(x, y))] * (mu - lam))
        if lam > mu:
            row.extend([("ne", var(x, y))] * (lam - mu))
        block_inputs.append((row, max(lam, mu)))
    ands = sorted({val for row, _ in block_inputs for kind, val in row
                   if kind == "and"})
    and_num = {pq: len(reps) + 1 + i for i, pq in enumerate(ands)}
    lines = []
    if case["rooted"]:
        _, _, _, forced = frame(k)
        units = {}
        for (x, y), val in forced.items():
            u = var(x, y)
            assert units.setdefault(u, val) == val, "frame not invariant"
        for u in sorted(units):
            lines.append("%d 0" % (u if units[u] else -u))
    for (p, q) in ands:
        t = and_num[(p, q)]
        lines.append("%d %d 0" % (-t, p))
        lines.append("%d %d 0" % (-t, q))
        lines.append("%d %d %d 0" % (t, -p, -q))
    nxt = len(reps) + len(ands)
    for row, K in block_inputs:
        lit = []
        for kind, val in row:
            if kind == "e":
                lit.append(val)
            elif kind == "ne":
                lit.append(-val)
            else:
                lit.append(and_num[val])
        N = len(lit)
        assert 1 <= K <= N
        # s[i][j] = "at least j of the first i inputs are true", j <= K+1
        s = [[None] * (K + 2) for _ in range(N + 1)]
        for i in range(1, N + 1):
            for j in range(1, min(i, K + 1) + 1):
                nxt += 1
                s[i][j] = nxt
        for i in range(1, N + 1):
            x = lit[i - 1]
            for j in range(1, min(i, K + 1) + 1):
                cur = s[i][j]
                up = s[i - 1][j] if j <= i - 1 else None
                diag = s[i - 1][j - 1] if j >= 2 else None
                if up:
                    lines.append("%d %d 0" % (-up, cur))
                lines.append("%d %d 0" % (-x, cur) if j == 1
                             else "%d %d %d 0" % (-diag, -x, cur))
                lines.append("%d %d %d 0" % (-cur, up, x) if up
                             else "%d %d 0" % (-cur, x))
                if diag:
                    lines.append("%d %d 0" % (-cur, diag))
        lines.append("%d 0" % s[N][K])
        if K + 1 <= N:
            lines.append("%d 0" % -s[N][K + 1])
    text = "p cnf %d %d\n" % (nxt, len(lines)) + "\n".join(lines) + "\n"
    return text.encode(), len(reps), len(elems)


def audit_case(case, cnf_path=None, write=None):
    gens = generators(case)
    v = case["v"]
    report = []
    for idx, g in enumerate(gens):
        fixed = sum(1 for x in range(v) if g[x] == x)
        info = "gen%d order=%d fixed=%d type=%s" % (
            idx, perm_order(g), fixed,
            ".".join("%d^%d" % lc for lc in cycle_type(g)))
        if case["rooted"]:
            info += " pairs=%s" % ",".join(pair_action(case, g))
        report.append(info)
    exp = case.get("expect", {})
    if "orders" in exp:
        assert [perm_order(g) for g in gens] == exp["orders"], "orders differ"
    if "fixed" in exp:
        assert [sum(g[x] == x for x in range(v)) for g in gens] == exp["fixed"], \
            "fixed point counts differ"
    if case["rooted"]:
        _, _, _, forced = frame(case["k"])
        for g in gens:
            for (x, y), val in forced.items():
                a, b = sorted((g[x], g[y]))
                assert forced[(a, b)] == val, "generator moves the frame"
            assert g[0] == 0
        if "pair_actions" in exp:
            got = [",".join(pair_action(case, g)) for g in gens]
            assert got == exp["pair_actions"], "pair actions differ: %s" % got
    data, norb, gorder = derive_dimacs(case, gens)
    if "group_order" in exp:
        assert gorder == exp["group_order"], "group order differs"
    h = hashlib.sha256(data).hexdigest()
    ok = h == case.get("cnf_sha256")
    report.append("group_order=%d pair_orbits=%d sha256=%s %s" % (
        gorder, norb, h, "matches cases.json" if ok else "DIFFERS from cases.json"))
    if cnf_path:
        with open(cnf_path, "rb") as f:
            other = f.read()
        same = other == data
        report.append("file %s: %s" % (cnf_path, "identical" if same else "DIFFERENT"))
        ok = ok and same
    if write:
        with open(write, "wb") as f:
            f.write(data)
        report.append("wrote %s" % write)
    return ok, report


def main(argv):
    with open(os.path.join(HERE, "cases.json")) as f:
        cases = {c["name"]: c for c in json.load(f)["cases"]}
    write = None
    if argv and argv[0] == "--write":
        name, write = argv[1], argv[2]
        targets, cnf = [name], None
    elif argv:
        targets, cnf = [argv[0]], (argv[1] if len(argv) > 1 else None)
    else:
        targets, cnf = list(cases), None
    bad = 0
    for name in targets:
        try:
            ok, report = audit_case(cases[name], cnf, write)
        except AssertionError as exc:
            ok, report = False, ["assertion failed: %s" % exc]
        bad += not ok
        print("%s %s" % ("PASS" if ok else "FAIL", name))
        for line in report:
            print("     " + line)
    print("AUDIT %s (%d cases)" % ("OK" if not bad else "FAILED", len(targets)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
