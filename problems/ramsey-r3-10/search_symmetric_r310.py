#!/usr/bin/env python3
"""Front end for SAT+CEGAR exclusion of symmetric (3,10)-graphs on 40 vertices.

A *class* is a finite group H acting semiregularly on the 40 vertices, i.e.
with 40/|H| orbits, each a copy of the left-regular action.  Vertex
``j*|H| + i`` is the group element with index ``i`` in orbit ``j``; every
generator of H acts by left multiplication on the index, identically in every
orbit.  A graph is invariant under the action iff its edge set is a union of
H-orbits of vertex pairs, so one Boolean variable per pair orbit suffices.

Variables are the pair orbits numbered 1, 2, ... in increasing order of their
lexicographically least pair ``(u, v)`` with ``u < v``.  The formula consists
of

* all triangle clauses ``-x(uv) -x(uw) -x(vw)`` (literals deduplicated and
  sorted; clauses deduplicated and sorted), then
* optionally the translation-normalisation block (``--normalise``) and the
  orbit-sorting block (``--sort-orbits``) of the normalisation lemma in the
  README, then
* positive clauses ``OR x(ab) over pairs {a,b} of S`` for concrete 10-vertex
  sets ``S`` (independent-set separators), in the order of the separator file.

Subcommands:

* ``instance``   write the input file for the C++ CEGAR back end
  ``cegar_symmetric_r310.cpp``;
* ``sbp``        write the normalisation blocks alone (``--extra`` input of
  the back end);
* ``cnf``        build the final DIMACS formula from a separator file;
* ``core``       shrink a separator file to the clauses in a drat-trim core;
* ``normalizer`` write vertex maps normalising the action (the back end's
  ``--sym`` input: images of separators are extra valid 10-set clauses);
* ``check-sat``  independently check a SAT witness (if the back end ever
  reports one).

The independent semantic audit is ``audit_symmetric_certificate.py``; it
re-implements the group actions and the clause semantics without importing
this file.  Only the Python standard library is used.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import sys
from pathlib import Path

N = 40
TARGET = 10


# ----------------------------------------------------------------------------
# Group classes.  Each generator is left multiplication by a group generator,
# written as a map on element indices 0..m-1.
# ----------------------------------------------------------------------------


def cyclic(m: int) -> list:
    return [lambda i: (i + 1) % m]


def z10_x_z2() -> list:
    # element (a, b) in Z10 x Z2 has index a + 10 b
    return [
        lambda i: (i % 10 + 1) % 10 + 10 * (i // 10),
        lambda i: i % 10 + 10 * (1 - i // 10),
    ]


def dihedral(n: int) -> list:
    # D_n of order 2n: element r^a s^b has index a + n b; s r^a = r^-a s
    return [
        lambda i: (i % n + 1) % n + n * (i // n),
        lambda i: (-(i % n)) % n + n * (1 - i // n),
    ]


def dicyclic5() -> list:
    # Dic5 = <x, y | x^10 = 1, y^2 = x^5, y x y^-1 = x^-1>, x^a y^b -> a + 10 b
    def left_y(i: int) -> int:
        a, b = i % 10, i // 10
        if b == 0:
            return (-a) % 10 + 10
        return (-a + 5) % 10

    return [lambda i: (i % 10 + 1) % 10 + 10 * (i // 10), left_y]


def frobenius20() -> list:
    # AGL(1,5) = {x -> u x + c}; (u, c) with u = 2^t has index 5 t + c.
    # Left multiplication by (u0, c0) sends (u, c) to (u0 u, u0 c + c0).
    def left_translation(i: int) -> int:
        t, c = divmod(i, 5)
        return 5 * t + (c + 1) % 5

    def left_doubling(i: int) -> int:
        t, c = divmod(i, 5)
        return 5 * ((t + 1) % 4) + (2 * c) % 5

    return [left_translation, left_doubling]


def z4_x_z2() -> list:
    # (a, b) -> a + 4 b
    return [
        lambda i: (i % 4 + 1) % 4 + 4 * (i // 4),
        lambda i: i % 4 + 4 * (1 - i // 4),
    ]


def z2_cubed() -> list:
    return [lambda i, bit=bit: i ^ bit for bit in (1, 2, 4)]


def quaternion8() -> list:
    # Q8 = <x, y | x^4 = 1, y^2 = x^2, y x y^-1 = x^-1>, x^a y^b -> a + 4 b
    def left_y(i: int) -> int:
        a, b = i % 4, i // 4
        if b == 0:
            return (-a) % 4 + 4
        return (-a + 2) % 4

    return [lambda i: (i % 4 + 1) % 4 + 4 * (i // 4), left_y]


CLASSES = {
    "c20-2orb": dict(order=20, gens=cyclic(20), group="C20"),
    "c10xc2-2orb": dict(order=20, gens=z10_x_z2(), group="C10 x C2"),
    "d10-2orb": dict(order=20, gens=dihedral(10), group="D10 (dihedral of order 20)"),
    "dic5-2orb": dict(order=20, gens=dicyclic5(), group="Dic5 (dicyclic of order 20)"),
    "f20-2orb": dict(order=20, gens=frobenius20(), group="F20 = AGL(1,5)"),
    "c10-4orb": dict(order=10, gens=cyclic(10), group="C10"),
    "d5-4orb": dict(order=10, gens=dihedral(5), group="D5 (dihedral of order 10)"),
    "c8-5orb": dict(order=8, gens=cyclic(8), group="C8"),
    "c4xc2-5orb": dict(order=8, gens=z4_x_z2(), group="C4 x C2"),
    "c2xc2xc2-5orb": dict(order=8, gens=z2_cubed(), group="C2^3"),
    "d4-5orb": dict(order=8, gens=dihedral(4), group="D4 (dihedral of order 8)"),
    "q8-5orb": dict(order=8, gens=quaternion8(), group="Q8"),
    "c5-8orb": dict(order=5, gens=cyclic(5), group="C5"),
    "c4-10orb": dict(order=4, gens=cyclic(4), group="C4"),
    "c2xc2-10orb": dict(order=4, gens=z2_cubed()[:2], group="C2 x C2"),
    "c2-20orb": dict(order=2, gens=cyclic(2), group="C2"),
}


def generator_permutations(name: str) -> list[tuple[int, ...]]:
    spec = CLASSES[name]
    m = spec["order"]
    if N % m:
        raise ValueError("order must divide 40")
    perms = []
    for gen in spec["gens"]:
        local = [gen(i) for i in range(m)]
        if sorted(local) != list(range(m)):
            raise ValueError(f"{name}: generator is not a permutation")
        perms.append(
            tuple(j * m + local[i] for j in range(N // m) for i in range(m))
        )
    return perms


def group_closure(gens: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    identity = tuple(range(N))
    seen = {identity}
    frontier = [identity]
    while frontier:
        nxt = []
        for p in frontier:
            for g in gens:
                q = tuple(g[p[x]] for x in range(N))
                if q not in seen:
                    seen.add(q)
                    nxt.append(q)
        frontier = nxt
    return sorted(seen)


def pair_orbit_variables(gens: list[tuple[int, ...]]) -> dict[tuple[int, int], int]:
    """Number pair orbits 1, 2, ... by their lexicographically least pair."""
    var: dict[tuple[int, int], int] = {}
    count = 0
    for pair in itertools.combinations(range(N), 2):
        if pair in var:
            continue
        count += 1
        stack = [pair]
        var[pair] = count
        while stack:
            u, v = stack.pop()
            for g in gens:
                a, b = g[u], g[v]
                image = (a, b) if a < b else (b, a)
                if image not in var:
                    var[image] = count
                    stack.append(image)
    return var


def vertex_orbit_representatives(gens: list[tuple[int, ...]]) -> list[int]:
    seen: set[int] = set()
    reps = []
    for v in range(N):
        if v in seen:
            continue
        reps.append(v)
        stack = [v]
        seen.add(v)
        while stack:
            x = stack.pop()
            for g in gens:
                if g[x] not in seen:
                    seen.add(g[x])
                    stack.append(g[x])
    return reps


def triangle_clauses(var: dict[tuple[int, int], int]) -> list[list[int]]:
    clauses = {
        tuple(sorted({-var[(u, v)], -var[(u, w)], -var[(v, w)]}))
        for u, v, w in itertools.combinations(range(N), 3)
    }
    return [list(c) for c in sorted(clauses)]


def separator_clause(var: dict[tuple[int, int], int], witness) -> list[int]:
    return sorted({var[(a, b)] for a, b in itertools.combinations(sorted(witness), 2)})


def read_separators(path: Path) -> list[tuple[int, ...]]:
    result = []
    for line in path.read_text(encoding="ascii").splitlines():
        if line.strip():
            result.append(tuple(map(int, line.split(","))))
    return result


def setup(name: str):
    gens = generator_permutations(name)
    group = group_closure(gens)
    m = CLASSES[name]["order"]
    if len(group) != m:
        raise AssertionError(f"{name}: group order {len(group)} != {m}")
    for v in range(N):
        if len({g[v] for g in group}) != m:
            raise AssertionError(f"{name}: action is not semiregular")
    var = pair_orbit_variables(gens)
    return gens, group, var


def cmd_instance(args) -> None:
    gens, group, var = setup(args.cls)
    reps = vertex_orbit_representatives(gens)
    tri = triangle_clauses(var)
    nvars = max(var.values())
    lines = [f"{N} {nvars} {len(tri)} {len(reps)}", " ".join(map(str, reps))]
    lines.append(
        " ".join(str(var[p]) for p in itertools.combinations(range(N), 2))
    )
    lines.extend(" ".join(map(str, c)) + " 0" for c in tri)
    # normalizer-free symmetry data: the generators themselves (for logging)
    args.output.write_text("\n".join(lines) + "\n", encoding="ascii")
    print(
        json.dumps(
            {
                "class": args.cls,
                "group": CLASSES[args.cls]["group"],
                "group_order": len(group),
                "vertex_orbits": len(reps),
                "variables": nvars,
                "triangle_clauses": len(tri),
            }
        )
    )


def translation_normalisation_clauses(name: str, var) -> list[list[int]]:
    """Clauses  x(v0, (j,d)) -> x(v0, (j,e))  for orbits j >= 1, d != e.

    Sound by the normalisation lemma: right-translating orbit j by a fixed
    element commutes with the (left) action, so any invariant graph is
    isomorphic to an invariant graph in which, for every j >= 1, the set of
    cross offsets D_0j is empty or contains the identity.
    """
    m = CLASSES[name]["order"]
    clauses = set()
    for j in range(1, N // m):
        for i in range(1, m):
            clauses.add((-var[(0, j * m + i)], var[(0, j * m)]))
    return [list(c) for c in sorted(clauses)]


def internal_vectors(name: str, var) -> list[list[int]]:
    """Per orbit j, the internal pair-orbit variables x((j,e),(j,e_i)),
    i = 1..m-1, deduplicated in order of first occurrence, keeping only
    positions whose variable is preserved by every right translation of the
    orbit (for abelian H: all positions).  Right translation conjugates the
    internal connection set, so only these positions are unaffected by the
    translation normalisation; position p means the same element class in
    every orbit."""
    m = CLASSES[name]["order"]
    mult = left_regular_table(name)

    def key(a: int, b: int) -> tuple[int, int]:
        return (a, b) if a < b else (b, a)

    vecs = []
    for j in range(N // m):
        seen, vec = set(), []
        for i in range(1, m):
            x = var[(j * m, j * m + i)]
            if x in seen:
                continue
            seen.add(x)
            stable = all(
                var[key(j * m + mult[0][h], j * m + mult[i][h])] == x for h in range(m)
            )
            if stable:
                vec.append(x)
        vecs.append(vec)
    return vecs


def lex_leq_clauses(a: list[int], b: list[int]) -> list[list[int]]:
    """CNF of a <=_lex b without auxiliary variables: for every position p
    and every common prefix pattern, prefix equal -> (a_p -> b_p)."""
    clauses = []
    for p_ in range(len(a)):
        for pattern in itertools.product((0, 1), repeat=p_):
            clause = []
            for l, bit in enumerate(pattern):
                # literals false exactly when a_l = b_l = bit
                clause += [-a[l], -b[l]] if bit else [a[l], b[l]]
            clause += [-a[p_], b[p_]]
            clauses.append(sorted(set(clause)))
    return clauses


def orbit_sorting_clauses(name: str, var) -> list[list[int]]:
    vecs = internal_vectors(name, var)
    out = []
    for j in range(len(vecs) - 1):
        out.extend(lex_leq_clauses(vecs[j], vecs[j + 1]))
    return out


def cmd_cnf(args) -> None:
    gens, group, var = setup(args.cls)
    tri = triangle_clauses(var)
    seps = read_separators(args.separators)
    nvars = max(var.values())
    seen = set()
    out_clauses = list(tri)
    sbp = translation_normalisation_clauses(args.cls, var) if args.normalise else []
    if args.sort_orbits:
        sbp += orbit_sorting_clauses(args.cls, var)
    out_clauses.extend(sbp)
    for s in seps:
        if len(s) != TARGET or len(set(s)) != TARGET:
            raise ValueError(f"bad separator {s}")
        c = separator_clause(var, s)
        key = tuple(c)
        if key in seen:
            raise ValueError(f"duplicate separator clause for {s}")
        seen.add(key)
        out_clauses.append(c)
    body = [f"p cnf {nvars} {len(out_clauses)}"]
    body.extend(" ".join(map(str, c)) + " 0" for c in out_clauses)
    args.output.write_text("\n".join(body) + "\n", encoding="ascii")
    print(
        json.dumps(
            {
                "class": args.cls,
                "variables": nvars,
                "triangle_clauses": len(tri),
                "normalisation_clauses": len(sbp),
                "separator_clauses": len(seps),
                "total_clauses": len(out_clauses),
                "sha256": hashlib.sha256(args.output.read_bytes()).hexdigest(),
            }
        )
    )


def parse_dimacs_clauses(path: Path) -> list[tuple[int, ...]]:
    clauses = []
    current: list[int] = []
    for line in path.read_text(encoding="ascii").splitlines():
        line = line.strip()
        if not line or line[0] in "cp":
            continue
        for tok in map(int, line.split()):
            if tok == 0:
                clauses.append(tuple(sorted(current)))
                current = []
            else:
                current.append(tok)
    return clauses


def cmd_sbp(args) -> None:
    gens, group, var = setup(args.cls)
    clauses = translation_normalisation_clauses(args.cls, var)
    if args.sort_orbits:
        clauses += orbit_sorting_clauses(args.cls, var)
    args.output.write_text("".join(" ".join(map(str, c)) + " 0\n" for c in clauses), encoding="ascii")
    print(json.dumps({"class": args.cls, "normalisation_clauses": len(clauses)}))


def cmd_core(args) -> None:
    """Keep only separators whose clause occurs in a drat-trim core file."""
    gens, group, var = setup(args.cls)
    core = set(parse_dimacs_clauses(args.core))
    seps = read_separators(args.separators)
    kept = [s for s in seps if tuple(separator_clause(var, s)) in core]
    args.output.write_text(
        "".join(",".join(map(str, s)) + "\n" for s in kept), encoding="ascii"
    )
    print(json.dumps({"input": len(seps), "kept": len(kept)}))


def left_regular_table(name: str) -> list[list[int]]:
    """mult[i][j] = index of e_i * e_j (index 0 is the identity)."""
    m = CLASSES[name]["order"]
    gens = [[gen(i) for i in range(m)] for gen in CLASSES[name]["gens"]]
    perms = {tuple(range(m))}
    frontier = [tuple(range(m))]
    while frontier:
        nxt = []
        for p in frontier:
            for g in gens:
                q = tuple(g[p[x]] for x in range(m))
                if q not in perms:
                    perms.add(q)
                    nxt.append(q)
        frontier = nxt
    by_image = {p[0]: p for p in perms}
    if len(by_image) != m:
        raise AssertionError("left-regular representation is not regular")
    return [list(by_image[i]) for i in range(m)]


def automorphisms(name: str) -> list[list[int]]:
    m = CLASSES[name]["order"]
    mult = left_regular_table(name)
    gen_elems = [gen(0) for gen in CLASSES[name]["gens"]]
    autos = []
    for images in itertools.product(range(m), repeat=len(gen_elems)):
        alpha = {0: 0}
        stack = [0]
        ok = True
        while stack and ok:
            x = stack.pop()
            for g, a in zip(gen_elems, images):
                y, ay = mult[g][x], mult[a][alpha[x]]
                if y in alpha:
                    ok = alpha[y] == ay
                    if not ok:
                        break
                else:
                    alpha[y] = ay
                    stack.append(y)
        if ok and len(alpha) == m and len(set(alpha.values())) == m:
            if all(alpha[mult[x][y]] == mult[alpha[x]][alpha[y]]
                   for x in range(m) for y in range(m)):
                autos.append([alpha[i] for i in range(m)])
    return autos


def cmd_normalizer(args) -> None:
    """Vertex maps (j, x) -> (pi(j), alpha(x) h_j) normalizing the action.

    They are used only to add images of separators (any 10-set yields a valid
    clause), so the choice affects speed, never soundness.
    """
    import random

    m = CLASSES[args.cls]["order"]
    k = N // m
    mult = left_regular_table(args.cls)
    autos = automorphisms(args.cls) if "aut" in args.parts else [list(range(m))]
    pis = list(itertools.permutations(range(k))) if "orbits" in args.parts else [tuple(range(k))]
    if "translations" in args.parts:
        trans = [(0,) + t for t in itertools.product(range(m), repeat=k - 1)]
    else:
        trans = [(0,) * k]
    total = len(autos) * len(pis) * len(trans)
    rng = random.Random(args.seed)
    combos = itertools.product(pis, autos, trans)
    if total > args.max:
        combos = [(rng.choice(pis), rng.choice(autos), tuple(rng.randrange(m) if j else 0 for j in range(k)))
                  for _ in range(args.max)]
    maps = set()
    for pi, alpha, t in combos:
        perm = tuple(pi[j] * m + mult[alpha[x]][t[j]] for j in range(k) for x in range(m))
        if perm != tuple(range(N)):
            maps.add(perm)
    maps = sorted(maps)
    with open(args.output, "w", encoding="ascii") as f:
        f.write(f"{len(maps)}\n")
        for perm in maps:
            f.write(" ".join(map(str, perm)) + "\n")
    print(json.dumps({"class": args.cls, "automorphisms": len(autos), "maps": len(maps), "total_before_sampling": total}))


def cmd_check_sat(args) -> None:
    """Independent check of a reported SAT model: triangle-free and alpha <= 9."""
    gens, group, var = setup(args.cls)
    true_vars = {int(x) for x in args.model.read_text().split() if int(x) > 0}
    adj = [0] * N
    for (u, v), x in var.items():
        if x in true_vars:
            adj[u] |= 1 << v
            adj[v] |= 1 << u
    for u, v in itertools.combinations(range(N), 2):
        if (adj[u] >> v) & 1 and adj[u] & adj[v]:
            raise SystemExit("model has a triangle")
    # exact independence number: branch on a vertex of maximum degree
    best = 0

    def rec(cand: int, size: int) -> None:
        nonlocal best
        if size + cand.bit_count() <= best:
            return
        pick, pick_deg = -1, -1
        rest = cand
        while rest:
            v = (rest & -rest).bit_length() - 1
            rest &= rest - 1
            d = (adj[v] & cand).bit_count()
            if d > pick_deg:
                pick, pick_deg = v, d
        if pick_deg <= 0:
            best = max(best, size + cand.bit_count())
            return
        rec(cand & ~(1 << pick) & ~adj[pick], size + 1)
        rec(cand & ~(1 << pick), size)

    rec((1 << N) - 1, 0)
    print(json.dumps({"triangle_free": True, "alpha": best}))


def main() -> None:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("instance")
    p.add_argument("cls", choices=sorted(CLASSES))
    p.add_argument("output", type=Path)
    p = sub.add_parser("cnf")
    p.add_argument("cls", choices=sorted(CLASSES))
    p.add_argument("separators", type=Path)
    p.add_argument("output", type=Path)
    p.add_argument("--normalise", action="store_true",
                   help="insert the translation-normalisation block after the triangles")
    p.add_argument("--sort-orbits", action="store_true",
                   help="also insert the orbit-sorting block (after the translation block)")
    p = sub.add_parser("sbp")
    p.add_argument("cls", choices=sorted(CLASSES))
    p.add_argument("output", type=Path)
    p.add_argument("--sort-orbits", action="store_true")
    p = sub.add_parser("core")
    p.add_argument("cls", choices=sorted(CLASSES))
    p.add_argument("separators", type=Path)
    p.add_argument("core", type=Path)
    p.add_argument("output", type=Path)
    p = sub.add_parser("normalizer")
    p.add_argument("cls", choices=sorted(CLASSES))
    p.add_argument("output", type=Path)
    p.add_argument("--parts", default="orbits,aut,translations")
    p.add_argument("--max", type=int, default=100000)
    p.add_argument("--seed", type=int, default=1)
    p = sub.add_parser("check-sat")
    p.add_argument("cls", choices=sorted(CLASSES))
    p.add_argument("model", type=Path)
    args = ap.parse_args()
    {"instance": cmd_instance, "cnf": cmd_cnf, "core": cmd_core, "sbp": cmd_sbp,
     "normalizer": cmd_normalizer, "check-sat": cmd_check_sat}[
        args.cmd
    ](args)


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
