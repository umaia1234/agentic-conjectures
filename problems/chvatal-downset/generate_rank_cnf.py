#!/usr/bin/env python3
"""Rank-split CNF for a minimal counterexample to Chvatal's conjecture.

Standard library only.  For a ground set {0, ..., n-1} and a rank r with
3 <= r <= n, the CNF written by this script is satisfiable iff there are
families D (x variables) and Y (y variables) with

  1. Y intersecting, every member of Y of size >= 3;
  2. D = down(Y) (both directions encoded);
  3. saturation: every T in D \\ Y is disjoint from some member of Y;
  4. every singleton in D;
  5. |Y| >= |star_i(D)| + 1 for every element i (totalizer counters);
  6. minimality: the set Tight = {i : |star_i(D)| = |Y| - 1} is not a
     member of D;
  7. rank: {0, ..., r-1} is in D and no (r+1)-set is in D;
  8. inside each block {0..r-1} and {r..n-1}: |star_j(D)| >= |star_{j+1}(D)|,
     and if equal, x >=_lex (j j+1)x with positions in bitmask order.

README.md proves that, if the conjecture holds for ground sets with at most
n-1 elements, a counterexample with n elements yields a solution for some r
(using the Kleitman-Magnanti theorem only for item 1's size bound).  Hence
UNSAT for every r in {3, ..., n} settles ground sets with n elements.

`--self-test` checks the encoding against brute force: for every small
family satisfying the conditions with a relaxed bound, an explicitly computed
assignment must satisfy every clause (the direction an UNSAT claim needs).
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import random
import sys
from pathlib import Path


class Encoding:
    """Clause builder with deterministic variable numbering."""

    def __init__(self, n: int) -> None:
        self.n = n
        self.size = 1 << n
        self.top = 2 * self.size
        self.clauses: list[list[int]] = []
        # Bookkeeping for the self-test: counter definitions, sections.
        self.counters: list[tuple[list[int], list[int]]] = []
        self.sections: list[tuple[str, int]] = []

    def section(self, name: str) -> None:
        self.sections.append((name, len(self.clauses)))

    def x(self, subset: int) -> int:
        return subset + 1

    def y(self, subset: int) -> int:
        return self.size + subset + 1

    def new(self) -> int:
        self.top += 1
        return self.top

    def add(self, clause: list[int]) -> None:
        self.clauses.append(clause)

    def totalizer(self, lits: list[int]) -> list[int]:
        """Unary outputs o with o[j-1] <-> (number of true lits >= j)."""

        if len(lits) == 1:
            return [lits[0]]
        mid = len(lits) // 2
        left = self.totalizer(lits[:mid])
        right = self.totalizer(lits[mid:])
        p, q = len(left), len(right)
        out = [self.new() for _ in range(p + q)]
        self.counters.append((lits, out))
        for a in range(p + 1):
            for b in range(q + 1):
                if a + b >= 1:  # left >= a and right >= b -> sum >= a + b
                    clause = [-left[a - 1]] if a else []
                    clause += [-right[b - 1]] if b else []
                    self.add(clause + [out[a + b - 1]])
                if a + b < p + q:  # left <= a and right <= b -> sum <= a + b
                    clause = [left[a]] if a < p else []
                    clause += [right[b]] if b < q else []
                    self.add(clause + [-out[a + b]])
        return out


def popcount(value: int) -> int:
    return bin(value).count("1")


def submasks(mask: int):
    sub = mask
    while True:
        yield sub
        if sub == 0:
            return
        sub = (sub - 1) & mask


def blocks(n: int, r: int) -> list[tuple[int, int]]:
    """Adjacent pairs (j, j+1) inside the blocks {0..r-1} and {r..n-1}."""

    return [(j, j + 1) for j in range(n - 1) if j != r - 1]


def build(n: int, r: int, bound: int = 1) -> Encoding:
    """Build the CNF.  `bound` is 1 for the real instance (tests relax it)."""

    if not 3 <= r <= n:
        raise ValueError("need 3 <= r <= n")
    enc = Encoding(n)
    size, full = enc.size, enc.size - 1
    allowed = [s for s in range(size) if popcount(s) >= 3]
    allowed_set = set(allowed)

    enc.section("base")
    for s in range(size):
        if s not in allowed_set:
            enc.add([-enc.y(s)])
    for a in allowed:
        for b in submasks(full ^ a):
            if b > a and b in allowed_set:
                enc.add([-enc.y(a), -enc.y(b)])
    for s in range(size):
        above = [s | e for e in submasks(full ^ s) if s | e in allowed_set]
        for t in above:
            enc.add([-enc.y(t), enc.x(s)])
        enc.add([-enc.x(s)] + [enc.y(t) for t in above])
    for t in range(size):
        clause = [-enc.x(t)] + ([enc.y(t)] if t in allowed_set else [])
        clause += [enc.y(s) for s in submasks(full ^ t) if s in allowed_set]
        enc.add(clause)
    enc.add([enc.x(0)])
    for i in range(n):
        enc.add([enc.x(1 << i)])
    enc.add([enc.x((1 << r) - 1)])
    for s in range(size):
        if popcount(s) == r + 1:
            enc.add([-enc.x(s)])

    enc.section("counters")
    count_y = enc.totalizer([enc.y(s) for s in allowed])
    stars = [
        enc.totalizer([enc.x(s) for s in range(size) if s >> i & 1])
        for i in range(n)
    ]

    def u(t: int) -> int | None:
        """Literal for |Y| >= t; None means the statement is constant."""
        return count_y[t - 1] if 1 <= t <= len(count_y) else None

    enc.section("counting")  # |Y| >= |star_i| + bound
    if bound >= 1:
        enc.add([u(bound)] if u(bound) else [])
    for star in stars:
        for t in range(1, len(star) + 1):
            if t + bound <= 0:
                continue
            target = u(t + bound)
            enc.add([-star[t - 1]] + ([target] if target else []))

    # Minimality: tight_i -> |star_i| >= |Y| - bound; Tight is not in D;
    # element r is tight (Tight meets {r..n-1}, sorted by star size there).
    enc.section("minimality")
    tight = [enc.new() for _ in range(n)]
    for i, star in enumerate(stars):
        for t in range(1, len(count_y) + 1):
            need = t - bound
            if need <= 0:
                continue
            clause = [-tight[i], -count_y[t - 1]]
            if need <= len(star):
                clause.append(star[need - 1])
            enc.add(clause)
    for s in range(size):
        enc.add([-enc.x(s)] + [tight[i] for i in range(n) if not s >> i & 1])
    if r < n:
        enc.add([tight[r]])

    enc.section("symmetry")  # inside the blocks {0..r-1} and {r..n-1}
    for j, k in blocks(n, r):
        for t in range(1, len(stars[j]) + 1):
            enc.add([-stars[k][t - 1], stars[j][t - 1]])
        equal = enc.new()
        differs = []
        for t in range(1, len(stars[j]) + 1):
            d = enc.new()
            enc.add([-d, stars[j][t - 1]])
            enc.add([-d, -stars[k][t - 1]])
            differs.append(d)
        enc.add([equal] + differs)
        prev = equal
        for s in range(size):
            if s >> j & 1 and not s >> k & 1:
                a, b = enc.x(s), enc.x(s ^ (1 << j) ^ (1 << k))
                nxt = enc.new()
                enc.add([-prev, a, -b])
                enc.add([-prev, -b, nxt])
                enc.add([-prev, a, nxt])
                prev = nxt
    return enc


def dimacs(enc: Encoding) -> str:
    lines = [f"p cnf {enc.top} {len(enc.clauses)}"]
    lines += [" ".join(map(str, c)) + " 0" for c in enc.clauses]
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Self-test: brute force against an explicit satisfying extension.


def star_sizes(n: int, family: set[int]) -> list[int]:
    return [sum(1 for s in family if s >> i & 1) for i in range(n)]


def invariant_conditions(n: int, ys: set[int]):
    """Items 1-5 (labelling-invariant) with bound = |Y| - max star.

    Returns (down(Y), bound, item 6 holds) or None.  Item 6 can only hold
    for this bound, because Tight must be nonempty.
    """

    if not ys or any(popcount(s) < 3 for s in ys):
        return None
    if any(a & b == 0 for a in ys for b in ys):
        return None
    down = {t for s in ys for t in submasks(s)}
    for t in down - ys:
        if all(t & s for s in ys):
            return None
    if any(1 << i not in down for i in range(n)):
        return None
    deg = star_sizes(n, down)
    tight = sum(1 << i for i in range(n) if deg[i] == max(deg))
    return down, len(ys) - max(deg), tight not in down


def canonical_conditions(n: int, r: int, down: set[int]) -> bool:
    """Items 7-8 (rank and symmetry breaking)."""

    if (1 << r) - 1 not in down or any(popcount(s) == r + 1 for s in down):
        return False
    deg = star_sizes(n, down)
    for j, k in blocks(n, r):
        if deg[j] < deg[k]:
            return False
        if deg[j] == deg[k]:
            swap = (1 << j) | (1 << k)
            for s in range(1 << n):
                t = s ^ swap if popcount(s & swap) == 1 else s
                if (s in down) != (t in down):
                    if s not in down:
                        return False
                    break
    return True


def extension(enc: Encoding, n: int, r: int, bound: int,
              ys: set[int]) -> dict[int, bool]:
    """Assignment encoding (down(Y), Y) with exact auxiliary values."""

    down = {t for s in ys for t in submasks(s)}
    value: dict[int, bool] = {}
    for s in range(enc.size):
        value[enc.x(s)] = s in down
        value[enc.y(s)] = s in ys

    def lit(v: int) -> bool:
        return value[v] if v > 0 else not value[-v]

    for lits, out in enc.counters:  # children are defined before parents
        total = sum(lit(v) for v in lits)
        for j, o in enumerate(out, start=1):
            value[o] = total >= j
    # Remaining auxiliaries in creation order: tight, then per block pair
    # (equal, differs..., chain...).  Recompute them from the semantics.
    deg = star_sizes(n, down)
    aux_start = max(max(out) for _, out in enc.counters) + 1
    v = aux_start
    for i in range(n):
        value[v] = deg[i] == len(ys) - bound
        v += 1
    for j, k in blocks(n, r):
        value[v] = deg[j] == deg[k]
        prev_true = value[v]
        v += 1
        size_j = 1 << (n - 1)
        for t in range(1, size_j + 1):
            value[v] = deg[j] >= t > deg[k]
            v += 1
        for s in range(enc.size):
            if s >> j & 1 and not s >> k & 1:
                other = s ^ (1 << j) ^ (1 << k)
                prev_true = prev_true and ((s in down) == (other in down))
                value[v] = prev_true
                v += 1
    if v != enc.top + 1:
        raise AssertionError("auxiliary bookkeeping mismatch")
    return value


def clause_violations(enc: Encoding, value: dict[int, bool]) -> int:
    bad = 0
    for clause in enc.clauses:
        if not any(value[v] if v > 0 else not value[-v] for v in clause):
            bad += 1
    return bad


def section_violations(enc: Encoding, value: dict[int, bool]) -> dict:
    bounds = enc.sections + [("end", len(enc.clauses))]
    bad = {}
    for (name, start), (_, stop) in zip(bounds, bounds[1:]):
        for clause in enc.clauses[start:stop]:
            if not any(value[v] if v > 0 else not value[-v] for v in clause):
                bad[name] = bad.get(name, 0) + 1
    return bad


def check_family(n: int, ys: set[int], cache: dict, stats: dict) -> None:
    """Check the explicit extension of (down(Y), Y) against the CNF built
    for its rank and for bound = |Y| - max star.  Every section except
    "minimality" must be satisfied whenever items 1-5 and 7-8 hold; the
    "minimality" section too whenever item 6 holds."""

    found = invariant_conditions(n, ys)
    if found is None:
        return
    down, bound, minimal = found
    r = max(popcount(s) for s in down)
    if not canonical_conditions(n, r, down):
        return
    if bound >= 1 and minimal:
        raise AssertionError(f"brute force found a counterexample: {sorted(ys)}")
    if (n, r, bound) not in cache:
        cache[(n, r, bound)] = build(n, r, bound)
    enc = cache[(n, r, bound)]
    bad = section_violations(enc, extension(enc, n, r, bound, ys))
    if not minimal:
        bad.pop("minimality", None)
    if bad:
        raise AssertionError(f"extension violates {bad}: n={n} r={r}")
    key = f"n{n}_families_checked" + ("_with_item6" if minimal else "")
    stats[key] = stats.get(key, 0) + 1


def totalizer_test(max_inputs: int = 9) -> int:
    """Exhaustive: exact counts satisfy the totalizer clauses, and the
    clauses force every output to the exact count."""

    checked = 0
    for m in range(1, max_inputs + 1):
        enc = Encoding(0)
        enc.top = m
        enc.section("totalizer")
        out = enc.totalizer(list(range(1, m + 1)))
        for bits in range(1 << m):
            value = {v: bool(bits >> (v - 1) & 1) for v in range(1, m + 1)}
            for lits, outs in enc.counters:
                total = sum(value[v] for v in lits)
                for j, o in enumerate(outs, start=1):
                    value[o] = total >= j
            assert section_violations(enc, value) == {}
            total = bin(bits).count("1")
            for j, o in enumerate(out, start=1):  # flipping breaks a clause
                flipped = dict(value)
                flipped[o] = not value[o]
                if m > 1:
                    assert section_violations(enc, flipped) != {}
            checked += 1
    return checked


def self_test(seed: int = 1) -> dict[str, object]:
    stats: dict[str, object] = {"totalizer_assignments": totalizer_test()}
    cache: dict = {}
    # Exhaustive for n = 4, 5: every family of sets of size >= 3.
    for n in (4, 5):
        allowed = [s for s in range(1 << n) if popcount(s) >= 3]
        for mask in range(1, 1 << len(allowed)):
            ys = {allowed[i] for i in range(len(allowed)) if mask >> i & 1}
            check_family(n, ys, cache, stats)
    # Randomised for n = 6, 7, 8: canonical relabellings of random families.
    rng = random.Random(seed)
    for n, wanted in ((6, 40), (7, 10), (8, 2)):
        before = stats.get(f"n{n}_families_checked", 0)
        attempts = 0
        while stats.get(f"n{n}_families_checked", 0) - before < wanted:
            attempts += 1
            if attempts > 5000:
                raise AssertionError(f"too few random families for n={n}")
            ys = random_saturated(n, rng)
            if ys is None or invariant_conditions(n, ys) is None:
                continue
            canon = canonical_form(n, ys)
            down = {t for s in canon for t in submasks(s)}
            if not canonical_conditions(n, max(map(popcount, down)), down):
                raise AssertionError("canonical form violates items 7-8")
            check_family(n, canon, cache, stats)
    # Item 6 (minimality) is rare for random families; cyclically invariant
    # families have equal stars, so Tight = everything and item 6 holds.
    for n, wanted in ((6, 3), (7, 4), (8, 2)):
        key = f"n{n}_families_checked_with_item6"
        attempts = 0
        while stats.get(key, 0) < wanted:
            attempts += 1
            if attempts > 20000:
                raise AssertionError(f"too few cyclic families for n={n}")
            ys = random_cyclic(n, rng)
            found = invariant_conditions(n, ys)
            if found is None or not found[2]:
                continue
            check_family(n, canonical_form(n, ys), cache, stats)
    stats["fano_plane_n7"] = fano_test(cache, stats)
    return stats


def random_cyclic(n: int, rng: random.Random) -> set[int]:
    """A random union of orbits of the cyclic shift i -> i+1 mod n."""

    def rotate(s: int) -> int:
        return ((s << 1) | (s >> (n - 1))) & ((1 << n) - 1)

    ys: set[int] = set()
    for _ in range(rng.randint(1, 3)):
        s = sum(1 << i for i in rng.sample(range(n), rng.randint(3, n - 2)))
        for _ in range(n):
            ys.add(s)
            s = rotate(s)
    return ys


def fano_test(cache: dict, stats: dict) -> bool:
    """The Fano plane satisfies item 6 (all seven points are tight)."""

    lines = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6),
             (2, 3, 6), (2, 4, 5)]
    ys = {sum(1 << p for p in line) for line in lines}
    canon = canonical_form(7, ys)
    before = stats.get("n7_families_checked_with_item6", 0)
    check_family(7, canon, cache, stats)
    return stats.get("n7_families_checked_with_item6", 0) == before + 1


def random_saturated(n: int, rng: random.Random) -> set[int] | None:
    """A random maximal intersecting family inside its own down-closure."""

    allowed = [s for s in range(1 << n) if popcount(s) >= 3]
    rng.shuffle(allowed)
    ys: set[int] = set()
    for s in allowed:
        if all(s & t for t in ys):
            ys.add(s)
    keep = {s for s in ys if rng.random() < 0.2}
    if not keep:
        return None
    down = {t for s in keep for t in submasks(s)}
    for s in sorted(down, key=lambda v: (-popcount(v), v)):
        if all(s & t for t in keep):
            keep.add(s)
    return keep


def canonical_form(n: int, ys: set[int]) -> set[int] | None:
    """Relabel to maximise (star sizes, x in bitmask order) subject to
    {0..r-1} in D; the result must satisfy items 7-8."""

    down = {t for s in ys for t in submasks(s)}
    r = max(popcount(s) for s in down)
    best = None
    for perm in itertools.permutations(range(n)):
        image = {s: sum(1 << perm[i] for i in range(n) if s >> i & 1)
                 for s in down}
        pdown = set(image.values())
        if (1 << r) - 1 not in pdown:
            continue
        key = (tuple(star_sizes(n, pdown)),
               tuple(s in pdown for s in range(1 << n)))
        if best is None or key > best[0]:
            best = (key, {image[s] for s in ys})
    return best[1] if best else None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--n", type=int)
    parser.add_argument("--rank", type=int)
    parser.add_argument("--output", type=Path, help="write DIMACS CNF here")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        print(json.dumps({"self_test": "passed", **self_test()}, indent=2))
        return
    if args.n is None or args.rank is None or args.output is None:
        parser.error("--n, --rank and --output are required")
    enc = build(args.n, args.rank)
    text = dimacs(enc)
    args.output.write_text(text)
    print(json.dumps({
        "n": args.n,
        "rank": args.rank,
        "variables": enc.top,
        "clauses": len(enc.clauses),
        "sha256": hashlib.sha256(text.encode()).hexdigest(),
    }, sort_keys=True))


if __name__ == "__main__":
    sys.exit(main())
