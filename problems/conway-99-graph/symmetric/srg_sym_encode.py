#!/usr/bin/env python3
"""CNF encoding of a strongly regular graph invariant under a permutation group.

Standard library only.  Encodes "there is an srg(v,k,lam,mu) on the vertex set
{0,...,v-1} that is invariant under every generator", optionally together with
the forced rooted frame of an srg(v,k,1,2) (see ``rooted_frame``).  The exact
variable numbering and clause order are specified in ../README.md ("Encoding
specification"); ``srg_sym_audit.py`` re-derives the same DIMACS bytes with an
independent implementation.

Usage (paths relative to this directory):
  python3 srg_sym_encode.py list
  python3 srg_sym_encode.py cnf CASE -o CASE.cnf     # write DIMACS, print SHA-256
  python3 srg_sym_encode.py hash [CASE ...]          # compare with cases.json
  python3 srg_sym_encode.py decode CASE MODEL        # check a solver model
"""
import argparse
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CASES = os.path.join(HERE, "cases.json")


# --------------------------------------------------------------------------
# Rooted frame of an srg(v,k,1,2)
# --------------------------------------------------------------------------

def rooted_frame(k):
    """Return (v, partner, labels, forced) for the canonical rooted frame.

    Vertex 0 is the root x.  Gamma_1(x) = {1,...,k} with the perfect matching
    {2i-1, 2i}.  Gamma_2(x) = {k+1,...,v-1}; vertex k+1+i is the unique common
    neighbour (other than x) of the i-th non-adjacent pair (a, b), a < b, of
    Gamma_1 in lexicographic order.  ``forced`` maps every pair (x, y), x < y,
    that meets {0} or Gamma_1 to its forced adjacency value.
    """
    if k % 2:
        raise ValueError("k must be even")
    partner = {a: (a + 1 if a % 2 == 1 else a - 1) for a in range(1, k + 1)}
    labels = [(a, b) for a in range(1, k + 1) for b in range(a + 1, k + 1)
              if partner[a] != b]
    v = 1 + k + len(labels)
    forced = {}
    for a in range(1, k + 1):
        forced[(0, a)] = 1
        for b in range(a + 1, k + 1):
            forced[(a, b)] = 1 if partner[a] == b else 0
    for i, (a, b) in enumerate(labels):
        w = k + 1 + i
        forced[(0, w)] = 0
        for c in range(1, k + 1):
            forced[(c, w)] = 1 if c in (a, b) else 0
    return v, partner, labels, forced


def perm_from_cycles(n, cycles):
    g = list(range(n))
    seen = set()
    for cyc in cycles:
        for i, x in enumerate(cyc):
            if not 0 <= x < n or x in seen:
                raise ValueError("bad cycle data")
            seen.add(x)
            g[x] = cyc[(i + 1) % len(cyc)]
    return g


def extend_root_perm(k, cycles):
    """Extend a matching automorphism of Gamma_1 (cycles on 1..k) to all v."""
    v, partner, labels, _ = rooted_frame(k)
    s = perm_from_cycles(k + 1, cycles)
    if s[0] != 0:
        raise ValueError("vertex 0 is the root")
    for a in range(1, k + 1):
        if s[partner[a]] != partner[s[a]]:
            raise ValueError("permutation does not preserve the matching")
    index = {lab: k + 1 + i for i, lab in enumerate(labels)}
    g = list(range(v))
    for a in range(1, k + 1):
        g[a] = s[a]
    for i, (a, b) in enumerate(labels):
        g[k + 1 + i] = index[tuple(sorted((s[a], s[b])))]
    return g


def cycle_type_perm(spec):
    """spec = [[length, count], ...]: consecutive cycles starting at vertex 0."""
    cycles = []
    start = 0
    for length, count in spec:
        for _ in range(count):
            cycles.append(list(range(start, start + length)))
            start += length
    return start, cycles


def case_setup(case):
    """Return (v, k, lam, mu, generators, forced) for a case record."""
    v, k, lam, mu = case["v"], case["k"], case["lambda"], case["mu"]
    gens = []
    forced = {}
    if case["rooted"]:
        if (lam, mu) != (1, 2):
            raise ValueError("rooted frame needs lambda=1, mu=2")
        vv, _, _, forced = rooted_frame(k)
        if vv != v:
            raise ValueError("v inconsistent with rooted frame")
        for cycles in case["generators"]:
            gens.append(extend_root_perm(k, cycles))
    else:
        for gen in case["generators"]:
            if isinstance(gen, dict):
                n, cycles = cycle_type_perm(gen["cycle_type"])
                if n != v:
                    raise ValueError("cycle type does not cover v points")
            else:
                cycles = gen
            gens.append(perm_from_cycles(v, cycles))
    return v, k, lam, mu, gens, forced


# --------------------------------------------------------------------------
# Encoding
# --------------------------------------------------------------------------

def pair_orbits(v, gens):
    """Union-find over unordered pairs; returns orbit id (least pair index)."""
    parent = list(range(v * v))

    def find(a):
        root = a
        while parent[root] != root:
            root = parent[root]
        while parent[a] != root:
            parent[a], a = root, parent[a]
        return root

    for g in gens:
        for x in range(v):
            gx = g[x]
            for y in range(x + 1, v):
                gy = g[y]
                p = x * v + y
                q = gx * v + gy if gx < gy else gy * v + gx
                a, b = find(p), find(q)
                if a < b:
                    parent[b] = a
                elif b < a:
                    parent[a] = b
    orbit = {}
    for x in range(v):
        for y in range(x + 1, v):
            orbit[(x, y)] = find(x * v + y)
    return orbit


def vertex_orbit_reps(v, gens):
    parent = list(range(v))

    def find(a):
        while parent[a] != a:
            a = parent[a]
        return a
    for g in gens:
        for x in range(v):
            a, b = find(x), find(g[x])
            if a < b:
                parent[b] = a
            elif b < a:
                parent[a] = b
    return sorted({find(x) for x in range(v)})


def encode(v, k, lam, mu, gens, forced=None):
    """Return (nvars, clauses, info); see README for the specification."""
    forced = forced or {}
    orbit = pair_orbits(v, gens)
    reps = sorted(set(orbit.values()))
    ovar = {r: i + 1 for i, r in enumerate(reps)}
    m = len(reps)

    def e(x, y):
        return ovar[orbit[(x, y) if x < y else (y, x)]]

    vreps = vertex_orbit_reps(v, gens)
    blocks = []
    for x in vreps:
        blocks.append(([("v", e(x, y)) for y in range(v) if y != x], k))
    need = set()
    for r in reps:
        x, y = divmod(r, v)
        lits = []
        for z in range(v):
            if z == x or z == y:
                continue
            a, b = e(x, z), e(y, z)
            if a == b:
                lits.append(("v", a))
            else:
                key = (a, b) if a < b else (b, a)
                need.add(key)
                lits.append(("t", key))
        exy = e(x, y)
        if lam < mu:
            lits += [("v", exy)] * (mu - lam)
        elif lam > mu:
            lits += [("n", exy)] * (lam - mu)
        blocks.append((lits, max(lam, mu)))
    and_keys = sorted(need)
    tvar = {key: m + 1 + i for i, key in enumerate(and_keys)}
    nvars = m + len(and_keys)

    clauses = []
    fval = {}
    for (x, y), val in forced.items():
        var = e(x, y)
        if fval.get(var, val) != val:
            raise ValueError("generators do not preserve the forced frame")
        fval[var] = val
    for var in sorted(fval):
        clauses.append((var,) if fval[var] else (-var,))
    for key in and_keys:
        t = tvar[key]
        a, b = key
        clauses.append((-t, a))
        clauses.append((-t, b))
        clauses.append((t, -a, -b))

    for items, K in blocks:
        lits = [val if kind == "v" else (-val if kind == "n" else tvar[val])
                for kind, val in items]
        N = len(lits)
        if not 1 <= K <= N:
            raise ValueError("unsupported cardinality bound")
        top = K + 1
        s = {}
        for i in range(1, N + 1):
            for j in range(1, min(i, top) + 1):
                nvars += 1
                s[(i, j)] = nvars
        for i in range(1, N + 1):
            li = lits[i - 1]
            for j in range(1, min(i, top) + 1):
                sij = s[(i, j)]
                same = s.get((i - 1, j))
                low = s.get((i - 1, j - 1))
                if same is not None:
                    clauses.append((-same, sij))
                if j == 1:
                    clauses.append((-li, sij))
                else:
                    clauses.append((-low, -li, sij))
                if same is not None:
                    clauses.append((-sij, same, li))
                else:
                    clauses.append((-sij, li))
                if j >= 2:
                    clauses.append((-sij, low))
        clauses.append((s[(N, K)],))
        if top <= N:
            clauses.append((-s[(N, top)],))
    info = {"orbit": orbit, "ovar": ovar, "m": m, "n_and": len(and_keys),
            "vertex_orbits": len(vreps)}
    return nvars, clauses, info


def dimacs_bytes(nvars, clauses):
    out = ["p cnf %d %d\n" % (nvars, len(clauses))]
    out.extend(" ".join(map(str, c)) + " 0\n" for c in clauses)
    return "".join(out).encode()


def load_cases():
    with open(CASES) as f:
        data = json.load(f)
    return {c["name"]: c for c in data["cases"]}


def build_case(case):
    v, k, lam, mu, gens, forced = case_setup(case)
    nvars, clauses, info = encode(v, k, lam, mu, gens, forced)
    return v, gens, nvars, clauses, info


# --------------------------------------------------------------------------
# Model decoding (any SAT answer must pass this independent graph check)
# --------------------------------------------------------------------------

def read_model(path):
    true = set()
    with open(path) as f:
        for line in f:
            if line.startswith("v "):
                true.update(int(t) for t in line.split()[1:] if int(t) > 0)
    return true


def check_graph(v, k, lam, mu, adj, gens):
    """Return a list of violations (empty iff srg and invariant)."""
    bad = []
    for x in range(v):
        if adj[x][x] or sum(adj[x]) != k:
            bad.append("degree/loop at %d" % x)
        for y in range(v):
            if adj[x][y] != adj[y][x]:
                bad.append("asymmetric %d %d" % (x, y))
    for x in range(v):
        for y in range(x + 1, v):
            c = sum(1 for z in range(v) if adj[x][z] and adj[y][z])
            if c != (lam if adj[x][y] else mu):
                bad.append("pair %d %d has %d common neighbours" % (x, y, c))
    for g in gens:
        for x in range(v):
            for y in range(x + 1, v):
                if adj[x][y] != adj[g[x]][g[y]]:
                    bad.append("not invariant")
                    return bad
    return bad


def decode(case, model_path):
    v, gens, _, _, info = build_case(case)
    true = read_model(model_path)
    adj = [[0] * v for _ in range(v)]
    for (x, y), r in info["orbit"].items():
        if info["ovar"][r] in true:
            adj[x][y] = adj[y][x] = 1
    bad = check_graph(v, case["k"], case["lambda"], case["mu"], adj, gens)
    return adj, bad


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("list")
    p = sub.add_parser("cnf")
    p.add_argument("case")
    p.add_argument("-o", "--output", required=True)
    p = sub.add_parser("hash")
    p.add_argument("case", nargs="*")
    p = sub.add_parser("decode")
    p.add_argument("case")
    p.add_argument("model")
    args = ap.parse_args()
    cases = load_cases()
    if args.cmd == "list":
        for name, c in cases.items():
            print("%-14s %-8s %s" % (name, c.get("result", "?"), c["title"]))
        return 0
    if args.cmd == "cnf":
        _, _, nvars, clauses, info = build_case(cases[args.case])
        data = dimacs_bytes(nvars, clauses)
        with open(args.output, "wb") as f:
            f.write(data)
        print("%s orbits=%d and=%d vars=%d clauses=%d sha256=%s" % (
            args.case, info["m"], info["n_and"], nvars, len(clauses),
            hashlib.sha256(data).hexdigest()))
        return 0
    if args.cmd == "hash":
        bad = 0
        for name in args.case or list(cases):
            _, _, nvars, clauses, _ = build_case(cases[name])
            h = hashlib.sha256(dimacs_bytes(nvars, clauses)).hexdigest()
            want = cases[name].get("cnf_sha256")
            ok = want == h
            bad += not ok
            print("%s %s %s" % ("OK  " if ok else "FAIL", name, h))
        return 1 if bad else 0
    if args.cmd == "decode":
        adj, bad = decode(cases[args.case], args.model)
        if bad:
            print("NOT A VALID GRAPH: %d violations, first: %s" % (len(bad), bad[0]))
            return 1
        print("VALID srg(%d,%d,%d,%d) invariant under the case generators" % (
            len(adj), cases[args.case]["k"], cases[args.case]["lambda"],
            cases[args.case]["mu"]))
        return 0
    return 2


if __name__ == "__main__":
    sys.exit(main())
