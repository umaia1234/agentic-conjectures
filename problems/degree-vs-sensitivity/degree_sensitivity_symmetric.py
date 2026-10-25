#!/usr/bin/env python3
"""Exact exclusions of symmetric subclasses of the degree--sensitivity search.

A *normalized solution* on n variables of degree <= d is a Boolean function
f:{0,1}^n -> {0,1} whose multilinear polynomial has degree <= d and which
satisfies f(0)=0 and f(e_i)=1 for every i.  For (n,d)=(14,5) such a function
would improve the exponent log(6)/log(3).  For a permutation group G acting on
the coordinates, f is G-invariant if f(x^g)=f(x) for all g in G and all x.

This dependency-free script checks, in exact integer arithmetic, certificates
that no G-invariant normalized solution exists for groups G from GROUPS, for
Young subgroups ('young:a,b,...': functions symmetric inside consecutive blocks
of sizes a,b,...), and for the trivial group with (n,d)=(10,4).  Run without
arguments it checks every committed certificate and asserts the aggregate
claims (the committed group list, and that every Young subgroup with at most
three blocks is excluded).  Two kinds of certificate are checked.

* Counting.  Every solution has its layer vector (B_0,...,B_n) in the exact
  finite list of integral layer profiles (247 profiles for (14,5), computed by
  degree_sensitivity_pair_bound.py).  For a G-invariant f, B_t is a sum of
  sizes of G-orbits of t-subsets.  If no profile passes this subset-sum test,
  the class is empty.

* Farkas trees.  For each surviving profile, a binary branching tree on
  orbit variables y_O in {0,1} whose leaves carry integer multipliers for
  valid linear equalities: cube identities sum_{T subset S} (-1)^{|T|}
  f(top minus T)=0 (S a (d+1)-subset of top; valid for every f of degree
  <= d) and layer identities sum_{O in layer t} |O| y_O = B_t.  At a leaf the
  combined equality r.y = rhs must be impossible on the current 0/1 box,
  i.e. max_box r.y < rhs.  Certificates are JSON files produced by
  degree_sensitivity_symmetric_search.py; this checker recomputes every row
  from its key and never trusts numerical data from the search.

Run with no arguments to check everything that is committed, or pass
certificate files explicitly (for example regenerated large certificates).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter
from fractions import Fraction
from math import comb, prod
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from degree_sensitivity_pair_bound import (  # noqa: E402
    feasible_layer_profiles,
    layer_interpolation_coefficients,
)

CERT_DIR = HERE / "symmetric_certificates"


# ---------------------------------------------------------------------------
# Permutation groups on {0,...,13}.


def _perm(images: list[int]) -> tuple[int, ...]:
    assert sorted(images) == list(range(len(images))), images
    return tuple(images)


def _cycles(*cycles: list[int], n: int = 14) -> tuple[int, ...]:
    images = list(range(n))
    for cycle in cycles:
        for a, b in zip(cycle, cycle[1:] + cycle[:1]):
            images[a] = b
    return _perm(images)


def _young(parts: tuple[int, ...]) -> list[tuple[int, ...]]:
    gens = []
    start = 0
    for size in parts:
        if size >= 2:
            gens.append(_cycles([start, start + 1]))
            gens.append(_cycles(list(range(start, start + size))))
        start += size
    assert start == 14
    return gens


INF = 13  # the point at infinity of the projective line over F_13


def _moebius13(a: int, b: int, c: int, d: int) -> tuple[int, ...]:
    """x -> (a x + b)/(c x + d) on P^1(F_13) = {0,...,12} u {13=inf}."""
    assert (a * d - b * c) % 13
    images = []
    for x in range(14):
        if x == INF:
            images.append(INF if c == 0 else a * pow(c, -1, 13) % 13)
            continue
        den = (c * x + d) % 13
        images.append(INF if den == 0 else (a * x + b) * pow(den, -1, 13) % 13)
    return _perm(images)


def _affine13(a: int, b: int) -> tuple[int, ...]:
    return _moebius13(a, b, 0, 1)


def _vec(k: int) -> tuple[int, int, int]:
    return (k & 1, k >> 1 & 1, k >> 2 & 1)


def _mat_vec(m: list[list[int]], v: tuple[int, int, int]) -> int:
    w = [sum(m[i][j] * v[j] for j in range(3)) % 2 for i in range(3)]
    return w[0] | w[1] << 1 | w[2] << 2


def _dot(u: int, v: int) -> int:
    return (u & v).bit_count() % 2


# Fano plane: point k in {1..7} (a nonzero vector of F_2^3) gets label k-1;
# line u^perp (u nonzero) gets label 6+u.  Lines are acted on through their
# point sets, so no matrix inverse is needed.
FANO_LINES = {u: frozenset(v for v in range(1, 8) if _dot(u, v) == 0) for u in range(1, 8)}


def _gl32(m: list[list[int]]) -> tuple[int, ...]:
    point_image = {v: _mat_vec(m, _vec(v)) for v in range(1, 8)}
    assert sorted(point_image.values()) == list(range(1, 8))
    images = [point_image[v] - 1 for v in range(1, 8)]
    by_set = {points: u for u, points in FANO_LINES.items()}
    for u in range(1, 8):
        image = frozenset(point_image[v] for v in FANO_LINES[u])
        images.append(6 + by_set[image])
    return _perm(images)


# AG(3,2): the 14 affine planes {x : a.x = c}, a nonzero, get label 2(a-1)+c.
AFFINE_PLANES = {
    2 * (a - 1) + c: frozenset(x for x in range(8) if _dot(a, x) == c)
    for a in range(1, 8)
    for c in range(2)
}


def _agl32(m: list[list[int]], t: int) -> tuple[int, ...]:
    point_image = {x: _mat_vec(m, _vec(x)) ^ t for x in range(8)}
    assert sorted(point_image.values()) == list(range(8))
    by_set = {points: label for label, points in AFFINE_PLANES.items()}
    return _perm(
        [by_set[frozenset(point_image[x] for x in AFFINE_PLANES[label])] for label in range(14)]
    )


SINGER = [[0, 0, 1], [1, 0, 1], [0, 1, 0]]  # multiplication by a root of x^3+x+1
TRANSVECTION = [[1, 1, 0], [0, 1, 0], [0, 0, 1]]
IDENTITY3 = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]


def _signed_s7(pi: list[int]) -> tuple[int, ...]:
    """S_7 on {0..6} x {+,-} (label i+7e): g.(i,e) = (g(i), e xor sign(g))."""
    sign = sum(pi[a] > pi[b] for a in range(7) for b in range(a + 1, 7)) % 2
    return _perm([pi[x % 7] + 7 * ((x // 7) ^ sign) for x in range(14)])


SEVEN = list(range(7))
SEVEN_B = list(range(7, 14))

# name -> (description, generators).  Every name is the class of normalized
# solutions invariant under the group generated by the listed permutations.
GROUPS: dict[str, tuple[str, list[tuple[int, ...]]]] = {
    "PGL(2,13)": ("PGL(2,13) on the projective line P^1(F_13), transitive", [
        _moebius13(1, 1, 0, 1), _moebius13(2, 0, 0, 1), _moebius13(0, 12, 1, 0)]),
    "PSL(2,13)": ("PSL(2,13) on P^1(F_13), transitive, minimal transitive", [
        _moebius13(1, 1, 0, 1), _moebius13(4, 0, 0, 1), _moebius13(0, 12, 1, 0)]),
    "AGL(3,2)-planes": ("AGL(3,2) on the 14 affine planes of AG(3,2), transitive", [
        _agl32(SINGER, 0), _agl32(TRANSVECTION, 0), _agl32(IDENTITY3, 1)]),
    "PGL(2,7)-Heawood": ("Aut(Heawood graph) = PGL(2,7) on points and lines of the "
                         "Fano plane, transitive", [
        _gl32(SINGER), _gl32(TRANSVECTION), _cycles(*[[i, i + 7] for i in range(7)])]),
    "S7-signed": ("S_7 on {0..6}x{+,-} with sign twist, transitive", [
        _signed_s7([1, 0, 2, 3, 4, 5, 6]), _signed_s7([1, 2, 3, 4, 5, 6, 0])]),
    "S7wrS2": ("S_7 wr S_2, blocks {0..6},{7..13}, transitive", _young((7, 7)) + [
        _cycles(*[[i, i + 7] for i in range(7)])]),
    "S2wrS7": ("S_2 wr S_7, blocks {i,i+7}, transitive", [
        _cycles([0, 7]), _cycles(SEVEN, SEVEN_B), _cycles([0, 1], [7, 8])]),
    "F56-planes": ("Z_2^3:Z_7 (translations and a Singer cycle) on the 14 affine "
                   "planes of AG(3,2), transitive", [
        _agl32(SINGER, 0), _agl32(IDENTITY3, 1), _agl32(IDENTITY3, 2), _agl32(IDENTITY3, 4)]),
    "C14": ("cyclic group of order 14 acting regularly, transitive", [
        _cycles(list(range(14)))]),
    "D7-regular": ("dihedral group of order 14 acting regularly, transitive", [
        _perm([(x % 7 + 1) % 7 + 7 * (x // 7) for x in range(14)]),
        _perm([(-(x % 7)) % 7 + 7 * (1 - x // 7) for x in range(14)])]),
    "PSL(2,7)-Fano": ("PSL(2,7) = GL(3,2) on the 7 points and 7 lines of the Fano "
                      "plane, two orbits", [_gl32(SINGER), _gl32(TRANSVECTION)]),
    "A7-diagonal": ("A_7 acting identically on {0..6} and {7..13}, two orbits", [
        _cycles([0, 1, 2], [7, 8, 9]), _cycles(SEVEN, SEVEN_B)]),
    "C7xC7": ("Z_7 x Z_7 rotating {0..6} and {7..13} independently", [
        _cycles(SEVEN), _cycles(SEVEN_B)]),
    "D7-diagonal": ("dihedral group of order 14 acting identically on {0..6} and "
                    "{7..13}", [
        _cycles(SEVEN, SEVEN_B), _perm([(-(x % 7)) % 7 + 7 * (x // 7) for x in range(14)])]),
    "C7(7^2)": ("cyclic group generated by one permutation of cycle type 7^2", [
        _cycles(SEVEN, SEVEN_B)]),
    "AGL(1,13)": ("AGL(1,13) on F_13, fixing the 14th point", [
        _affine13(1, 1), _affine13(2, 0)]),
    "C13:C6": ("Z_13:Z_6 (x -> a x + b, a a square) on F_13, fixing the 14th point", [
        _affine13(1, 1), _affine13(4, 0)]),
    "C13:C4": ("Z_13:Z_4 on F_13, fixing the 14th point", [
        _affine13(1, 1), _affine13(8, 0)]),
    "C13:C3": ("Z_13:Z_3 on F_13, fixing the 14th point", [
        _affine13(1, 1), _affine13(3, 0)]),
    "D13": ("Z_13:Z_2 (dihedral of order 26) on F_13, fixing the 14th point", [
        _affine13(1, 1), _affine13(12, 0)]),
    "C13": ("cyclic group generated by one 13-cycle (one fixed point)", [
        _affine13(1, 1)]),
    "C11": ("cyclic group generated by one 11-cycle (three fixed points)", [
        _cycles(list(range(11)))]),
}

def _partitions(n: int, largest: int) -> list[tuple[int, ...]]:
    if n == 0:
        return [()]
    out = []
    for k in range(min(n, largest), 0, -1):
        out.extend((k,) + rest for rest in _partitions(n - k, k))
    return out


ALL_PARTITIONS_14 = _partitions(14, 14)


def resolve_group(name: str) -> list[tuple[int, ...]]:
    """Generators for a named group, 'young:a,b,...' or 'trivial'.

    'young:9,3,2' is the Young subgroup S_9 x S_3 x S_2 permuting the
    consecutive blocks {0..8}, {9..11}, {12,13} independently, i.e. the class
    of functions that are symmetric inside each block.
    """
    if name == "trivial":
        return []
    if name in GROUPS:
        return GROUPS[name][1]
    if name.startswith("young:"):
        parts = tuple(int(x) for x in name[len("young:"):].split(","))
        assert parts in ALL_PARTITIONS_14, f"not a partition of 14 in decreasing order: {name}"
        return _young(parts)
    raise KeyError(name)


# ---------------------------------------------------------------------------
# Orbits, layer profiles, rows.


def apply(perm: tuple[int, ...], mask: int) -> int:
    out = 0
    for i, j in enumerate(perm):
        if mask >> i & 1:
            out |= 1 << j
    return out


def orbit_map(n: int, gens: list[tuple[int, ...]]) -> list[int]:
    """Return orb[mask] = least mask in the G-orbit of mask."""
    parent = list(range(1 << n))

    def find(a: int) -> int:
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for perm in gens:
        assert len(perm) == n
        for mask in range(1 << n):
            a, b = find(mask), find(apply(perm, mask))
            if a != b:
                parent[max(a, b)] = min(a, b)
    return [find(mask) for mask in range(1 << n)]


def lagrange(x: int, node: int, degree: int) -> Fraction:
    value = Fraction(1)
    for other in range(degree + 1):
        if other != node:
            value *= Fraction(x - other, node - other)
    return value


def full_layer_vectors(n: int, d: int) -> list[tuple[int, ...]]:
    """Exact list of integral layer vectors (B_0..B_n) of normalized solutions.

    B_t/binom(n,t) is a polynomial of degree <= d in t (symmetrization), so
    B_{d+1},...,B_n are integral linear forms in B_0,...,B_d.  For (14,5) the
    already committed exhaustive enumeration is reused; for other (n,d) the
    first d-2 free layers are enumerated and the last one by exact intervals.
    """
    forms = {}
    for t in range(n + 1):
        row = [Fraction(comb(n, t), comb(n, k)) * lagrange(t, k, d) for k in range(d + 1)]
        assert all(v.denominator == 1 for v in row), (n, d, t)
        forms[t] = [int(v) for v in row]
    if (n, d) == (14, 5):
        for t in range(6, 15):
            assert tuple(forms[t]) == layer_interpolation_coefficients(t)
        heads = [(0, 14) + p for p in feasible_layer_profiles()]
        assert len(heads) == 247
    else:
        heads = []

        def extend(prefix: list[int]) -> None:
            k = len(prefix)
            if k < d:
                for value in range(comb(n, k) + 1):
                    extend(prefix + [value])
                return
            lower, upper = 0, comb(n, d)
            for t in range(d + 1, n + 1):
                base = sum(forms[t][j] * prefix[j] for j in range(d))
                slope, cap = forms[t][d], comb(n, t)
                if slope > 0:
                    lower = max(lower, -((base) // slope))
                    upper = min(upper, (cap - base) // slope)
                elif slope < 0:
                    lower = max(lower, -((cap - base) // -slope))
                    upper = min(upper, base // -slope)
                elif not 0 <= base <= cap:
                    return
            heads.extend(tuple(prefix) + (v,) for v in range(lower, upper + 1))

        extend([0, n])
    vectors = []
    for head in heads:
        vector = tuple(sum(forms[t][j] * head[j] for j in range(d + 1)) for t in range(n + 1))
        assert vector[: d + 1] == head
        if all(0 <= vector[t] <= comb(n, t) for t in range(n + 1)):
            vectors.append(vector)
    return vectors


def subset_sums(values: list[int]) -> int:
    """Bitset of all subset sums."""
    bits = 1
    for v in values:
        bits |= bits << v
    return bits


class Instance:
    def __init__(self, n: int, d: int, gens: list[tuple[int, ...]]):
        self.n, self.d = n, d
        self.orb = orbit_map(n, gens)
        self.size = Counter(self.orb)
        self.reps = sorted(self.size)
        self.layer: dict[int, list[int]] = {t: [] for t in range(n + 1)}
        for rep in self.reps:
            self.layer[rep.bit_count()].append(rep)
        self.rows: dict[tuple, tuple[dict[int, int], int]] = {}

    def surviving(self, vectors: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
        sums = [subset_sums([self.size[r] for r in self.layer[t]]) for t in range(self.n + 1)]
        return [B for B in vectors if all(sums[t] >> B[t] & 1 for t in range(self.n + 1))]

    def root_box(self) -> dict[int, int]:
        fixed = {self.orb[0]: 0}
        for i in range(self.n):
            assert fixed.get(self.orb[1 << i], 1) == 1
            fixed[self.orb[1 << i]] = 1
        return fixed

    def row(self, key: list[int], profile: tuple[int, ...]) -> tuple[dict[int, int], int]:
        if len(key) == 1:
            t = key[0]
            return {r: self.size[r] for r in self.layer[t]}, profile[t]
        top, sub = key
        cache_key = (top, sub)
        if cache_key not in self.rows:
            if sub & ~top or sub.bit_count() != self.d + 1 or top >> self.n:
                raise ValueError(f"invalid cube key {key}")
            coef: dict[int, int] = {}
            t = sub
            while True:
                o = self.orb[top & ~t]
                coef[o] = coef.get(o, 0) + (-1 if t.bit_count() & 1 else 1)
                if t == 0:
                    break
                t = (t - 1) & sub
            self.rows[cache_key] = ({o: a for o, a in coef.items() if a}, 0)
        return self.rows[cache_key]

    def check_tree(self, tree: dict, profile: tuple[int, ...]) -> tuple[int, int]:
        """Return (nodes, leaves); raise AssertionError on any invalid step."""
        nodes = leaves = 0
        stack = [(tree, self.root_box())]
        while stack:
            node, fixed = stack.pop()
            nodes += 1
            if "branch" in node:
                o = self.orb[node["branch"]]
                assert o == node["branch"], "branch key must be an orbit representative"
                assert o not in fixed, "branching on an already fixed variable"
                for value in (0, 1):
                    child = dict(fixed)
                    child[o] = value
                    stack.append((node[str(value)], child))
                continue
            leaves += 1
            r: dict[int, int] = {}
            rhs = 0
            for key, mult in node["farkas"]:
                assert isinstance(mult, int) and mult != 0
                coef, b = self.row(key, profile)
                rhs += mult * b
                for o, a in coef.items():
                    r[o] = r.get(o, 0) + mult * a
            # maximum of r.y over the box: free variables in [0,1], fixed ones fixed
            box_max = sum(
                (rv * fixed[o]) if o in fixed else max(rv, 0) for o, rv in r.items()
            )
            assert box_max < rhs, "Farkas leaf does not certify infeasibility"
        return nodes, leaves


def group_order(gens: list[tuple[int, ...]], cap: int = 6000) -> int | None:
    n = len(gens[0])
    identity = tuple(range(n))
    seen = {identity}
    frontier = [identity]
    while frontier:
        nxt = []
        for g in frontier:
            for h in gens:
                gh = tuple(h[g[i]] for i in range(n))
                if gh not in seen:
                    seen.add(gh)
                    nxt.append(gh)
                    if len(seen) > cap:
                        return None
        frontier = nxt
    return len(seen)


# ---------------------------------------------------------------------------


def check_certificate(path: Path, vectors_cache: dict) -> tuple[str, str]:
    data = json.loads(path.read_text(encoding="utf-8"))
    assert data["format"] == "degree-sensitivity-farkas-tree-v1"
    n, d = data["n"], data["degree"]
    gens = [tuple(g) for g in data["generators"]]
    name = data["group"]
    assert gens == resolve_group(name), f"generators of {name} differ from the definition"
    assert name == "trivial" or (n, d) == (14, 5), "groups are only defined for n=14"
    if (n, d) not in vectors_cache:
        vectors_cache[(n, d)] = full_layer_vectors(n, d)
    inst = Instance(n, d, gens)
    if name.startswith("young:"):
        parts = [int(x) for x in name[len("young:"):].split(",")]
        assert len(inst.reps) == prod(x + 1 for x in parts), "Young orbit count mismatch"
    surviving = inst.surviving(vectors_cache[(n, d)])
    covered = [tuple(p["layers"]) for p in data["profiles"]]
    assert sorted(covered) == sorted(surviving), "certificate must cover every surviving profile"
    total_nodes = total_leaves = 0
    for item in data["profiles"]:
        nodes, leaves = inst.check_tree(item["tree"], tuple(item["layers"]))
        total_nodes += nodes
        total_leaves += leaves
    digest = hashlib.sha256(path.read_bytes()).hexdigest()[:16]
    return name, (
        f"{name:18s} n={n} d={d} orbits={len(inst.reps):5d} profiles={len(surviving):3d} "
        f"tree nodes={total_nodes:6d} Farkas leaves={total_leaves:6d} sha256={digest}..."
    )


# Groups whose certificates are committed in symmetric_certificates/.
COMMITTED = {
    "F56-planes", "C14", "D7-regular", "C7xC7", "AGL(1,13)", "C13:C6", "C13:C4", "C13:C3",
    "young:9,3,2", "young:8,3,3", "young:7,5,2", "young:6,6,2", "young:7,4,3",
    "young:6,5,3", "young:6,4,4", "young:5,5,4",
}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("certificates", nargs="*", type=Path)
    parser.add_argument("--skip-counting", action="store_true")
    parser.add_argument(
        "--young-blocks", type=int, default=None, metavar="K",
        help="also check the committed certificates and assert that every Young "
             "subgroup with at most K blocks is excluded by counting or by a checked "
             "certificate",
    )
    args = parser.parse_args()
    if args.young_blocks is not None and args.skip_counting:
        parser.error("--young-blocks needs the counting step")

    vectors_cache: dict = {}
    if not args.skip_counting:
        # Degree 4: the layer vector on 10 variables is forced, and on 11
        # variables no integral layer vector exists at all.
        assert full_layer_vectors(10, 4) == [(0, 10, 45, 70, 35, 0, 35, 70, 45, 10, 0)]
        assert full_layer_vectors(11, 4) == []
        print("(n,d)=(10,4): unique layer vector (0,10,45,70,35,0,35,70,45,10,0); "
              "(11,4): none")
        vectors = full_layer_vectors(14, 5)
        vectors_cache[(14, 5)] = vectors
        assert len(vectors) == 247
        counted = []
        for name, (description, gens) in GROUPS.items():
            inst = Instance(14, 5, gens)
            s = inst.surviving(vectors)
            counted.append((name, len(inst.reps), len(s)))
        print("named groups: orbits on subsets, surviving layer profiles")
        for name, orbits, s in counted:
            order = group_order(GROUPS[name][1])
            print(f"  {name:18s} order={order if order else '>6000':>6} orbits={orbits:5d} "
                  f"surviving profiles={s}")
        excluded = [name for name, _, s in counted if s == 0]
        assert excluded == [
            "PGL(2,13)", "PSL(2,13)", "AGL(3,2)-planes", "PGL(2,7)-Heawood", "S7-signed",
            "S7wrS2", "S2wrS7", "PSL(2,7)-Fano", "A7-diagonal",
        ], excluded
        print("excluded by counting alone:", ", ".join(excluded))

        young_excluded = []
        for parts in ALL_PARTITIONS_14:
            sizes = {t: [] for t in range(15)}
            # orbits of the Young subgroup S_parts are indexed by count vectors
            stack = [((), 0, 1)]
            while stack:
                counts, weight, size = stack.pop()
                k = len(counts)
                if k == len(parts):
                    sizes[weight].append(size)
                    continue
                for c in range(parts[k] + 1):
                    stack.append((counts + (c,), weight + c, size * comb(parts[k], c)))
            sums = [subset_sums(sizes[t]) for t in range(15)]
            if not any(all(sums[t] >> B[t] & 1 for t in range(15)) for B in vectors):
                young_excluded.append(parts)
        assert len(ALL_PARTITIONS_14) == 135
        print(f"Young subgroups S_lambda: {len(young_excluded)} of 135 partitions excluded "
              "by counting alone:")
        print("  " + " ".join("(" + ",".join(map(str, p)) + ")" for p in young_excluded))
        assert len(young_excluded) == 19

    paths = args.certificates or sorted(CERT_DIR.glob("*.json"))
    if args.young_blocks is not None and args.certificates:
        paths = sorted(CERT_DIR.glob("*.json")) + list(args.certificates)
    certified = set()
    for path in paths:
        name, line = check_certificate(path, vectors_cache)
        certified.add(name)
        print(line, flush=True)
    print("all symmetric-subclass certificates verified")

    if not args.certificates and not args.skip_counting:
        assert certified == COMMITTED, sorted(certified ^ COMMITTED)
        at_most_three = [p for p in ALL_PARTITIONS_14 if len(p) <= 3]
        assert len(at_most_three) == 24
        for parts in at_most_three:
            label = "young:" + ",".join(map(str, parts))
            assert parts in young_excluded or label in certified, label
        print("every Young subgroup S_lambda with at most three blocks is excluded "
              f"({sum(p in young_excluded for p in at_most_three)} by counting, "
              f"{sum(p not in young_excluded for p in at_most_three)} by Farkas trees)")
    if args.young_blocks is not None:
        wanted = [p for p in ALL_PARTITIONS_14 if len(p) <= args.young_blocks]
        missing = [p for p in wanted
                   if p not in young_excluded and "young:" + ",".join(map(str, p)) not in certified]
        assert not missing, f"not excluded: {missing}"
        print(f"every Young subgroup S_lambda with at most {args.young_blocks} blocks is "
              f"excluded ({len(wanted)} partitions: "
              f"{sum(p in young_excluded for p in wanted)} by counting, "
              f"{sum(p not in young_excluded for p in wanted)} by Farkas trees)")


if __name__ == "__main__":
    main()
