#!/usr/bin/env python3
"""Generate Farkas-tree certificates for symmetric subclasses (needs highspy).

For a group G from degree_sensitivity_symmetric.GROUPS (or the trivial group
with --n/--degree), the variables are the G-orbits of subsets of the n
coordinates.  The linear system contains one cube identity per orbit
representative of weight > d (the cube with that top and the d+1 highest
coordinates of the top as directions) and the layer identities of one
surviving layer profile.  A depth-first branch and bound solves the elastic LP
relaxation with HiGHS at every node.  If the relaxation is infeasible, the row
duals are scaled and rounded to integers, and the rounded multipliers are
checked exactly before being stored; otherwise the search branches on a
fractional variable of smallest Hamming weight (ties: closest to 1/2).
An integral LP point would be a genuine solution; it is verified by an exact
Moebius transform and reported.

The certificates are checked independently by degree_sensitivity_symmetric.py,
which recomputes every row from its key.  Nothing here needs to be trusted.

Example (research environment with highspy installed):
  python degree_sensitivity_symmetric_search.py --group 'C7(7^2)' --out cert.json
  python degree_sensitivity_symmetric_search.py --group young:9,3,2 --out cert.json
  python degree_sensitivity_symmetric_search.py --group trivial --n 10 --degree 4 \
      --out n10_d4.json
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from collections import defaultdict
from pathlib import Path

import highspy
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))

from degree_sensitivity_symmetric import (  # noqa: E402
    Instance,
    full_layer_vectors,
    resolve_group,
)


def moebius_degree(values: list[int], n: int) -> int:
    coefficients = list(values)
    for bit in range(n):
        step = 1 << bit
        for mask in range(1 << n):
            if mask & step:
                coefficients[mask] -= coefficients[mask ^ step]
    return max((mask.bit_count() for mask in range(1 << n) if coefficients[mask]), default=0)


class Search:
    def __init__(self, inst: Instance, profile: tuple[int, ...]):
        self.inst = inst
        self.profile = profile
        n, d = inst.n, inst.d
        self.cols = inst.reps
        self.col_index = {rep: i for i, rep in enumerate(self.cols)}
        keys = []
        for top in inst.reps:
            if top.bit_count() <= d:
                continue
            bits = [i for i in range(n) if top >> i & 1]
            sub = sum(1 << i for i in bits[-(d + 1):])
            keys.append([top, sub])
        keys += [[t] for t in range(n + 1)]
        self.keys = keys
        self.rows = [inst.row(key, profile) for key in keys]
        self.weight = [rep.bit_count() for rep in self.cols]
        self._build_lp()
        self.stats = defaultdict(int)

    def _build_lp(self) -> None:
        V, m = len(self.cols), len(self.rows)
        inf = highspy.kHighsInf
        lp = highspy.HighsLp()
        lp.num_col_ = V + 2 * m
        lp.num_row_ = m
        lp.col_cost_ = np.array([0.0] * V + [1.0] * (2 * m))
        lp.col_lower_ = np.zeros(V + 2 * m)
        lp.col_upper_ = np.array([1.0] * V + [inf] * (2 * m))
        rhs = np.array([float(b) for _, b in self.rows])
        lp.row_lower_ = rhs
        lp.row_upper_ = rhs.copy()
        per_col = defaultdict(list)
        for i, (coef, _) in enumerate(self.rows):
            for rep, a in coef.items():
                per_col[self.col_index[rep]].append((i, a))
        start, index, value = [], [], []
        for c in range(V):
            start.append(len(index))
            for i, a in sorted(per_col[c]):
                index.append(i)
                value.append(float(a))
        for sign in (1.0, -1.0):
            for i in range(m):
                start.append(len(index))
                index.append(i)
                value.append(sign)
        start.append(len(index))
        lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
        lp.a_matrix_.start_ = np.array(start)
        lp.a_matrix_.index_ = np.array(index)
        lp.a_matrix_.value_ = np.array(value)
        h = highspy.Highs()
        h.setOptionValue("output_flag", False)
        h.setOptionValue("threads", 1)
        h.setOptionValue("random_seed", 0)
        h.passModel(lp)
        self.h = h

    def solve(self, fixed: dict[int, int]):
        V = len(self.cols)
        lo = np.zeros(V)
        up = np.ones(V)
        for rep, v in fixed.items():
            lo[self.col_index[rep]] = up[self.col_index[rep]] = v
        self.h.changeColsBounds(V, np.arange(V, dtype=np.int32), lo, up)
        self.h.run()
        self.stats["lp"] += 1
        solution = self.h.getSolution()
        if self.h.getInfo().objective_function_value > 1e-7:
            return False, list(solution.row_dual)
        return True, list(solution.col_value[:V])

    def certificate(self, duals: list[float], fixed: dict[int, int]):
        for scale in (2 ** 6, 2 ** 10, 2 ** 14, 2 ** 20, 2 ** 30, 2 ** 44):
            for sign in (1, -1):
                mult = [int(round(sign * x * scale)) for x in duals]
                r: dict[int, int] = defaultdict(int)
                rhs = 0
                for k, (coef, b) in zip(mult, self.rows):
                    if k:
                        rhs += k * b
                        for rep, a in coef.items():
                            r[rep] += k * a
                box_max = sum(
                    rv * fixed[rep] if rep in fixed else max(rv, 0) for rep, rv in r.items()
                )
                if box_max < rhs:
                    return [[key, k] for key, k in zip(self.keys, mult) if k]
        return None

    def run(self) -> dict:
        root = dict(self.inst.root_box())
        self.t0 = time.time()
        # iterative depth-first search; each work item fills parent[slot]
        holder: dict = {"root": None}
        work = [(root, holder, "root")]
        while work:
            fixed, parent, slot = work.pop()
            self.stats["nodes"] += 1
            feasible, data = self.solve(fixed)
            if not feasible:
                cert = self.certificate(data, fixed)
                if cert is None:
                    raise RuntimeError("could not round a Farkas certificate")
                parent[slot] = {"farkas": cert}
                self.stats["leaves"] += 1
                if self.stats["leaves"] % 100 == 0:
                    print(f"    leaves={self.stats['leaves']} nodes={self.stats['nodes']} "
                          f"depth={len(fixed)} t={time.time() - self.t0:.0f}s", flush=True)
                continue
            y = data
            frac = [c for c, rep in enumerate(self.cols)
                    if rep not in fixed and 1e-6 < y[c] < 1 - 1e-6]
            if not frac:
                values = [1 if y[self.col_index[self.inst.orb[x]]] > 0.5 else 0
                          for x in range(1 << self.inst.n)]
                degree = moebius_degree(values, self.inst.n)
                raise RuntimeError(f"integral LP point found; exact degree {degree}; "
                                   f"truth table {values}")
            c = min(frac, key=lambda c: (self.weight[c], abs(y[c] - 0.5), c))
            rep = self.cols[c]
            node = {"branch": rep}
            parent[slot] = node
            first = 1 if y[c] > 0.5 else 0
            for value in (1 - first, first):  # pushed in reverse: `first` explored first
                child = dict(fixed)
                child[rep] = value
                work.append((child, node, str(value)))
        return holder["root"]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--group", required=True)
    parser.add_argument("--n", type=int, default=14)
    parser.add_argument("--degree", type=int, default=5)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    gens = resolve_group(args.group)
    assert args.group == "trivial" or (args.n, args.degree) == (14, 5)
    inst = Instance(args.n, args.degree, gens)
    surviving = inst.surviving(full_layer_vectors(args.n, args.degree))
    print(f"{args.group}: n={args.n} d={args.degree} orbits={len(inst.reps)} "
          f"surviving profiles={len(surviving)}", flush=True)
    profiles = []
    start = time.time()
    for layers in surviving:
        search = Search(inst, layers)
        tree = search.run()
        profiles.append({"layers": list(layers), "tree": tree})
        print(f"  profile {list(layers)}: nodes={search.stats['nodes']} "
              f"leaves={search.stats['leaves']} time={time.time() - search.t0:.1f}s", flush=True)
    data = {
        "format": "degree-sensitivity-farkas-tree-v1",
        "group": args.group,
        "n": args.n,
        "degree": args.degree,
        "generators": [list(g) for g in gens],
        "profiles": profiles,
    }
    args.out.write_text(json.dumps(data, separators=(",", ":")) + "\n", encoding="utf-8")
    print(f"wrote {args.out} ({args.out.stat().st_size} bytes) total {time.time() - start:.1f}s")


if __name__ == "__main__":
    main()
