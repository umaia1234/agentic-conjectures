#!/usr/bin/env python3
"""Semantic audit of a symmetric-class (3,10) certificate on 40 vertices.

Usage: audit_symmetric_certificate.py CLASS SEPARATORS (--check-cnf F | --write-cnf F)
       [--normalised] [--sorted-orbits] [--expect-sha256 HEX]

CLASS names a finite group H together with its semiregular action on the 40
vertices: vertex ``j*|H| + i`` is the element with index ``i`` in orbit ``j``
and ``g`` acts by left multiplication, ``g.(j, x) = (j, g x)``.  This file
defines every group by its full multiplication law on index tuples and does
not import the search code.  The audit

1. checks the group axioms for the multiplication table, prints isomorphism
   invariants (abelian?, element-order histogram) and compares them with the
   values that identify the named group among all groups of that order;
2. builds the action of *all* |H| elements and checks that it is semiregular
   (no non-identity element fixes a vertex), so there are 40/|H| orbits;
3. computes the H-orbits on the 780 vertex pairs from the full group and
   numbers them 1, 2, ... by their lexicographically least pair;
4. checks that the CNF is exactly (a) the deduplicated, sorted quotient of
   all C(40,3) triangle clauses, optionally followed by (n) the translation
   normalisation block (``--normalised``) and (s) the orbit-sorting block
   (``--sorted-orbits``), followed by (b) one positive clause per line of the
   separator file, equal to the set of pair orbits met by that concrete
   10-vertex set.

Clause (a) holds in every triangle-free H-invariant graph and clause (b) in
every H-invariant graph without an independent 10-set.  Hence a verified
UNSAT proof of the CNF shows that no 40-vertex graph that is triangle-free,
has independence number at most 9 and is invariant under this action exists.

Block (n) consists of the binary clauses ``-x(v0,(j,d)) OR x(v0,(j,e))`` for
every orbit j >= 1 and every d != e, where v0 = (0, e).  It is justified by
the normalisation lemma (README): right translation of a single orbit,
``(j, x) -> (j, x h)``, commutes with the left action, so it maps invariant
graphs to isomorphic invariant graphs and replaces the cross-offset set D_0j
by D_0j h; choosing h = d^-1 for some d in D_0j (when D_0j is nonempty) makes
every block-(n) clause true.  Block (s) lex-orders the internal vectors of
consecutive orbits (see ``orbit_sorting_block``); relabelling orbits also
commutes with the action, and the vectors only use positions that no right
translation changes, so one can first sort the orbits and then translate
orbits 1, 2, ... without unsorting them.  The audit checks both commutation
properties and the position stability mechanically; the lemma itself is a
hand argument written out in the README.  Only the Python standard library
is used.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import itertools
import json
import lzma
from pathlib import Path

N = 40


# Multiplication laws on index tuples; `index` maps a tuple to 0..|H|-1.
def law_cyclic(m):
    elements = [(a,) for a in range(m)]
    return elements, lambda x, y: ((x[0] + y[0]) % m,), lambda x: x[0]


def law_product(m1, m2):
    elements = [(a, b) for b in range(m2) for a in range(m1)]
    return (
        elements,
        lambda x, y: ((x[0] + y[0]) % m1, (x[1] + y[1]) % m2),
        lambda x: x[0] + m1 * x[1],
    )


def law_elementary_abelian(rank):
    elements = [tuple((i >> k) & 1 for k in range(rank)) for i in range(2**rank)]
    return (
        elements,
        lambda x, y: tuple((p + q) % 2 for p, q in zip(x, y)),
        lambda x: sum(bit << k for k, bit in enumerate(x)),
    )


def law_dihedral(n):
    # (a, b) = r^a s^b,  s r = r^-1 s
    elements = [(a, b) for b in range(2) for a in range(n)]
    return (
        elements,
        lambda x, y: ((x[0] + (-1) ** x[1] * y[0]) % n, (x[1] + y[1]) % 2),
        lambda x: x[0] + n * x[1],
    )


def law_dicyclic(n):
    # Dic_n of order 4n: (a, b) = x^a y^b, x^(2n) = 1, y^2 = x^n, y x = x^-1 y
    def mul(x, y):
        a = x[0] + (-1) ** x[1] * y[0]
        b = x[1] + y[1]
        if b == 2:
            a, b = a + n, 0
        return (a % (2 * n), b)

    elements = [(a, b) for b in range(2) for a in range(2 * n)]
    return elements, mul, lambda x: x[0] + 2 * n * x[1]


def law_frobenius20():
    # (t, c) is the affine map z -> 2^t z + c over Z/5; product = composition
    def mul(x, y):
        return ((x[0] + y[0]) % 4, (pow(2, x[0], 5) * y[1] + x[1]) % 5)

    elements = [(t, c) for t in range(4) for c in range(5)]
    return elements, mul, lambda x: 5 * x[0] + x[1]


# name -> (law, expected invariants: abelian, element-order histogram)
CLASSES = {
    "c20-2orb": (law_cyclic(20), True, {1: 1, 2: 1, 4: 2, 5: 4, 10: 4, 20: 8}),
    "c10xc2-2orb": (law_product(10, 2), True, {1: 1, 2: 3, 5: 4, 10: 12}),
    "d10-2orb": (law_dihedral(10), False, {1: 1, 2: 11, 5: 4, 10: 4}),
    "dic5-2orb": (law_dicyclic(5), False, {1: 1, 2: 1, 4: 10, 5: 4, 10: 4}),
    "f20-2orb": (law_frobenius20(), False, {1: 1, 2: 5, 4: 10, 5: 4}),
    "c10-4orb": (law_cyclic(10), True, {1: 1, 2: 1, 5: 4, 10: 4}),
    "d5-4orb": (law_dihedral(5), False, {1: 1, 2: 5, 5: 4}),
    "c8-5orb": (law_cyclic(8), True, {1: 1, 2: 1, 4: 2, 8: 4}),
    "c4xc2-5orb": (law_product(4, 2), True, {1: 1, 2: 3, 4: 4}),
    "c2xc2xc2-5orb": (law_elementary_abelian(3), True, {1: 1, 2: 7}),
    "d4-5orb": (law_dihedral(4), False, {1: 1, 2: 5, 4: 2}),
    "q8-5orb": (law_dicyclic(2), False, {1: 1, 2: 1, 4: 6}),
    "c5-8orb": (law_cyclic(5), True, {1: 1, 5: 4}),
    "c4-10orb": (law_cyclic(4), True, {1: 1, 2: 1, 4: 2}),
    "c2xc2-10orb": (law_elementary_abelian(2), True, {1: 1, 2: 3}),
    "c2-20orb": (law_cyclic(2), True, {1: 1, 2: 1}),
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_action(name: str):
    (elements, mul, index), abelian_expected, orders_expected = CLASSES[name]
    m = len(elements)
    if N % m:
        raise SystemExit("group order does not divide 40")
    if sorted(index(x) for x in elements) != list(range(m)):
        raise SystemExit("index map is not a bijection")
    table = {(x, y): mul(x, y) for x in elements for y in elements}
    eset = set(elements)
    if any(z not in eset for z in table.values()):
        raise SystemExit("multiplication not closed")
    identity = [e for e in elements if all(table[(e, x)] == x == table[(x, e)] for x in elements)]
    if len(identity) != 1:
        raise SystemExit("no unique identity")
    e = identity[0]
    for x, y, z in itertools.product(elements, repeat=3):
        if table[(table[(x, y)], z)] != table[(x, table[(y, z)])]:
            raise SystemExit("multiplication not associative")
    for x in elements:
        if not any(table[(x, y)] == e for y in elements):
            raise SystemExit("missing inverse")
    abelian = all(table[(x, y)] == table[(y, x)] for x in elements for y in elements)
    orders: dict[int, int] = {}
    for x in elements:
        k, p = 1, x
        while p != e:
            p, k = table[(p, x)], k + 1
        orders[k] = orders.get(k, 0) + 1
    if abelian != abelian_expected or orders != orders_expected:
        raise SystemExit(f"group invariants differ: abelian={abelian} orders={orders}")
    # left-regular action on each of the 40/m orbits, for every element g
    perms = []
    for g in elements:
        perm = [0] * N
        for j in range(N // m):
            for x in elements:
                perm[j * m + index(x)] = j * m + index(table[(g, x)])
        perms.append(tuple(perm))
        if g != e and any(perm[v] == v for v in range(N)):
            raise SystemExit("action is not semiregular")
    if len(set(perms)) != m:
        raise SystemExit("action is not faithful")
    if index(e) != 0:
        raise SystemExit("identity must have index 0")
    return perms, abelian, dict(sorted(orders.items()))


def normalisation_block(name: str, perms, var) -> list[tuple[int, ...]]:
    """Block (n), after checking that single-orbit right translations commute
    with the action (the hypothesis of the normalisation lemma)."""
    (elements, mul, index), _, _ = CLASSES[name]
    m = len(elements)
    for j in range(1, N // m):
        for h in elements:
            rho = list(range(N))
            for x in elements:
                rho[j * m + index(x)] = j * m + index(mul(x, h))
            for g in perms:
                if any(g[rho[v]] != rho[g[v]] for v in range(N)):
                    raise SystemExit("orbit translation does not commute with the action")
    block = set()
    for j in range(1, N // m):
        for i in range(1, m):
            block.add(tuple(sorted((-var[(0, j * m + i)], var[(0, j * m)]))))
    return sorted(block)


def orbit_variables(perms) -> dict[tuple[int, int], int]:
    var: dict[tuple[int, int], int] = {}
    count = 0
    for u, v in itertools.combinations(range(N), 2):
        if (u, v) in var:
            continue
        count += 1
        for g in perms:
            a, b = g[u], g[v]
            var[(min(a, b), max(a, b))] = count
    return var


def orbit_sorting_block(name: str, perms, var) -> list[tuple[int, ...]]:
    """Block (s): internal vectors of consecutive orbits are lex-ordered.

    The internal vector of orbit j lists x((j,e),(j,e_i)) for i = 1..m-1,
    keeping first occurrences; it determines the Cayley graph induced on the
    orbit.  For every position p and prefix pattern, the clause forbids the
    configuration  (prefix of both vectors = pattern, a_p = 1, b_p = 0).
    Relabelling orbits, (j, x) -> (pi(j), x), commutes with the action, which
    is the hypothesis of the sorting lemma; it is checked here.
    """
    (elements, mul, index), _, _ = CLASSES[name]
    m = len(elements)
    k = N // m
    for j in range(k - 1):
        swap = list(range(N))
        for i in range(m):
            swap[j * m + i], swap[(j + 1) * m + i] = (j + 1) * m + i, j * m + i
        for g in perms:
            if any(g[swap[v]] != swap[g[v]] for v in range(N)):
                raise SystemExit("orbit relabelling does not commute with the action")
    # keep a position only if every right translation of the orbit preserves
    # its variable (right translation conjugates the internal connection set;
    # for abelian H every position is kept), so the translation normalisation
    # cannot disturb the sorted vectors
    def pair(a: int, b: int) -> tuple[int, int]:
        return (min(a, b), max(a, b))

    by_index = {index(el): el for el in elements}
    vectors = []
    for j in range(k):
        vec: list[int] = []
        considered: list[int] = []
        for i in range(1, m):
            x = var[(j * m, j * m + i)]
            if x in considered:
                continue
            considered.append(x)
            if all(
                var[pair(j * m + index(mul(by_index[0], h)), j * m + index(mul(by_index[i], h)))]
                == x
                for h in elements
            ):
                vec.append(x)
        vectors.append(vec)
    block = []
    for j in range(k - 1):
        a, b = vectors[j], vectors[j + 1]
        for p_ in range(len(a)):
            for pattern in itertools.product((0, 1), repeat=p_):
                config = []
                for l, bit in enumerate(pattern):
                    config += [a[l], b[l]] if bit else [-a[l], -b[l]]
                config += [a[p_], -b[p_]]
                block.append(tuple(sorted({-lit for lit in config})))
    return block


def parse_dimacs(path: Path):
    header = None
    clauses, current = [], []
    for raw in path.read_text(encoding="ascii").splitlines():
        line = raw.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            _, kind, nv, nc = line.split()
            if kind != "cnf" or header is not None:
                raise SystemExit("bad DIMACS header")
            header = (int(nv), int(nc))
            continue
        for tok in map(int, line.split()):
            if tok == 0:
                clauses.append(current)
                current = []
            else:
                current.append(tok)
    if current or header is None or header[1] != len(clauses):
        raise SystemExit("malformed DIMACS file")
    return header[0], clauses


def read_text(path: Path) -> str:
    data = path.read_bytes()
    if path.suffix == ".gz":
        data = gzip.decompress(data)
    elif path.suffix == ".xz":
        data = lzma.decompress(data)
    return data.decode("ascii")


def expected_clauses(args, perms, var):
    """The certificate formula, rebuilt from the semantics alone."""
    triangles = sorted(
        {
            tuple(sorted({-var[(u, v)], -var[(u, w)], -var[(v, w)]}))
            for u, v, w in itertools.combinations(range(N), 3)
        }
    )
    block = normalisation_block(args.cls, perms, var) if args.normalised else []
    sorting = orbit_sorting_block(args.cls, perms, var) if args.sorted_orbits else []
    separators = []
    for number, line in enumerate(read_text(args.separators).splitlines(), 1):
        s = tuple(map(int, line.split(",")))
        if len(s) != 10 or len(set(s)) != 10 or min(s) < 0 or max(s) >= N:
            raise SystemExit(f"separator line {number} is not ten distinct vertices")
        separators.append(
            tuple(sorted({var[(min(a, b), max(a, b))] for a, b in itertools.combinations(s, 2)}))
        )
    return triangles, block, sorting, separators


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("cls", choices=sorted(CLASSES))
    ap.add_argument("separators", type=Path, help="one 10-set per line (optionally .gz or .xz)")
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check-cnf", type=Path, help="check that this DIMACS file is exact")
    mode.add_argument("--write-cnf", type=Path, help="write the exact DIMACS file here")
    ap.add_argument("--normalised", action="store_true",
                    help="translation-normalisation block after the triangles")
    ap.add_argument("--sorted-orbits", action="store_true",
                    help="orbit-sorting block after the normalisation block")
    ap.add_argument("--expect-sha256", metavar="HEX",
                    help="fail unless the DIMACS file has this SHA-256 (e.g. the formula "
                         "whose proof was checked locally)")
    args = ap.parse_args()

    perms, abelian, orders = build_action(args.cls)
    var = orbit_variables(perms)
    if len(var) != N * (N - 1) // 2:
        raise SystemExit("pair orbits do not cover all pairs")
    nvars = max(var.values())
    triangles, block, sorting, separators = expected_clauses(args, perms, var)
    if len(set(separators)) != len(separators):
        raise SystemExit("duplicate separator clauses")
    formula = triangles + block + sorting + separators

    if args.check_cnf:
        variables, clauses = parse_dimacs(args.check_cnf)
        if variables != nvars:
            raise SystemExit(f"expected {nvars} variables, header says {variables}")
        if [tuple(c) for c in clauses] != formula:
            raise SystemExit("DIMACS file differs from the audited formula")
        cnf_path = args.check_cnf
    else:
        body = [f"p cnf {nvars} {len(formula)}"]
        body.extend(" ".join(map(str, c)) + " 0" for c in formula)
        args.write_cnf.write_text("\n".join(body) + "\n", encoding="ascii")
        cnf_path = args.write_cnf
    if args.expect_sha256 and sha256(cnf_path) != args.expect_sha256.lower():
        raise SystemExit(f"CNF SHA-256 {sha256(cnf_path)} differs from the expected value")

    print(
        json.dumps(
            {
                "status": "SEMANTICS VERIFIED",
                "mode": "check" if args.check_cnf else "write",
                "class": args.cls,
                "group_order": len(perms),
                "abelian": abelian,
                "element_orders": orders,
                "vertex_orbits": N // len(perms),
                "variables": nvars,
                "triangle_clauses": len(triangles),
                "normalisation_clauses": len(block),
                "orbit_sorting_clauses": len(sorting),
                "separator_clauses": len(separators),
                "cnf_sha256": sha256(cnf_path),
                "separators_sha256": sha256(args.separators),
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
