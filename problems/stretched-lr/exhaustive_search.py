#!/usr/bin/env python3
"""Exhaustive sub-box search for negative stretched-LR coefficients.

Sub-box ``B(K, s)``: every triple of partitions with at most ``K`` rows and
``|outer| = |inner| + |content| = s``.  Unordered pairs ``{inner, content}``
are enumerated in a fixed order; for each pair, ``lrcalc.mult`` lists every
``outer`` with at most ``K`` rows and ``c^outer_(inner,content) > 0``.  That
list is certified complete by the GL_K dimension identity
``sum_outer c * dim_K(outer) = dim_K(inner) * dim_K(content)`` (Weyl's
formula, independent of any LR code).  Triples with ``c = 0`` have
``P(t) = 0`` for ``t >= 1`` and are not polynomials of interest.

For each listed triple, ``P(t) = c^(t outer)_(t inner, t content)`` is
computed exactly by interpolation.  ``lr_count.cpp`` (a row-by-row LR tableau
DP, unsigned 128-bit with overflow detection) supplies the values.  Two
regimes are used, and each triple's regime is recorded in the counts:

A. ``D`` = the minimum of ``degree_bound`` over the six orientations of the
   triple (see ``orientations``): the dimension of an affine space containing
   the LR polytope (equations plus variables forced to vanish), a rigorous
   bound on ``deg P``.  If the values at ``t = 1..D+1`` stay small, lrcalc
   recomputes every one of them independently; the values at ``t = 0..D``
   are interpolated and ``t = D+1`` is the extra check.
B. Otherwise Normaliz computes the polytope dimension ``d`` (checked to be at
   most ``D``) and the Ehrhart quasi-polynomial (it must have period 1 and
   degree ``d``).  The DP values at ``t = 0..d`` are interpolated, ``t = d+1``
   is the extra check, the result must equal Normaliz's polynomial, and
   lrcalc recomputes ``P(1)`` and, when ``P(2)`` is small enough, ``P(2)``
   (all stretches when cheap).  Values beyond those already computed come
   from the orientation with the cheapest DP at ``t = 3``, where all six
   orientations must agree.

Every power-basis coefficient is checked for negativity.  Any inconsistency
raises an exception and aborts the run.  ``--merge`` combines shard logs into
one summary; ``--self-test`` runs exact checks without lrcalc or Normaliz.
"""

from __future__ import annotations

import argparse
import ctypes
import hashlib
import json
import math
import sys
import time
from collections import Counter
from collections.abc import Iterator, Sequence
from fractions import Fraction
from pathlib import Path

Partition = tuple[int, ...]


# ----------------------------------------------------------------- partitions

def partitions(total: int, maximum: int, max_length: int) -> Iterator[Partition]:
    """Partitions of ``total`` with parts <= maximum and length <= max_length."""
    if total == 0:
        yield ()
        return
    if max_length == 0:
        return
    for first in range(min(total, maximum), 0, -1):
        for rest in partitions(total - first, first, max_length - 1):
            yield (first,) + rest


def pairs_of_size(size: int, rows: int) -> Iterator[tuple[Partition, Partition]]:
    """Unordered pairs {a, b} with |a| + |b| = size, each with <= rows parts.

    Each unordered pair is yielded once, as (a, b) with (|a|, a) >= (|b|, b).
    """
    for size_a in range(size, (size - 1) // 2, -1):
        size_b = size - size_a
        for a in partitions(size_a, size_a, rows):
            for b in partitions(size_b, size_b, rows):
                if size_a == size_b and b > a:
                    continue
                yield a, b


def weyl_dimension(partition: Sequence[int], rows: int) -> int:
    """Dimension of the GL_rows irreducible with highest weight ``partition``."""
    parts = list(partition) + [0] * (rows - len(partition))
    numerator = denominator = 1
    for i in range(rows):
        for j in range(i + 1, rows):
            numerator *= parts[i] - parts[j] + j - i
            denominator *= j - i
    assert numerator % denominator == 0
    return numerator // denominator


def pad(partition: Sequence[int], length: int) -> list[int]:
    return list(partition) + [0] * (length - len(partition))


def orientations(outer: Partition, inner: Partition, content: Partition) -> list:
    """Six triples with the same LR coefficient at every stretch.

    For GL_n with n = len(outer) and p^v = (w - p_n, ..., w - p_1) the
    complement in the n x w rectangle, w = outer[0]:
    c^nu_(lam,mu) = c^nu_(mu,lam) = c^(lam^v)_(mu,nu^v) = c^(mu^v)_(lam,nu^v)
    (all are dim (V_lam x V_mu x V_nu^*)^GL_n).  Complements commute with
    stretching, so all six orientations have the same stretched polynomial.
    """
    n, width = len(outer), outer[0]

    def complement(partition: Partition) -> Partition:
        return tuple(x for x in (width - y for y in reversed(pad(partition, n))) if x > 0)

    o, i, c = complement(outer), complement(inner), complement(content)
    return [
        (outer, inner, content), (outer, content, inner),
        (i, content, o), (i, o, content),
        (c, inner, o), (c, o, inner),
    ]


def degree_bound(outer: Partition, inner: Partition, content: Partition) -> int:
    """Rigorous upper bound on deg P (= dimension of the LR polytope).

    The polytope lies in the affine space cut out by the row-sum and content
    equations and by these identically-zero variables a[i][j] (label j in
    row i).  Each vanishing is forced for every LR tableau of every stretch
    (the counts p_i and q_i below are stretch-invariant), hence on the whole
    rational polytope:

    * empty rows, absent labels (j >= m = len(content)) and j > i;
    * j < p_i, p_i = number of skew cells above the first cell of row i
      (column strictness: that cell, the smallest of its row, has label >= p_i);
    * j > m - 1 - q_i, q_i = number of skew cells below the last cell of row i
      (the labels below it are distinct and < m);
    * label j + 1 in row i when label j is excluded from every row above i
      (lattice word: a[i][j+1] <= #j in rows < i - #(j+1) in rows < i).

    Restricted to the remaining variables the equations are the incidence
    system of a bipartite graph (rows, labels), of rank vertices - components.
    """
    n, m = len(outer), len(content)
    lam = list(inner) + [0] * (n - len(inner))
    low, high, live = [0] * n, [-1] * n, []
    for i in range(n):
        if outer[i] == lam[i]:
            continue
        live.append(i)
        last, first = outer[i], lam[i]
        below = 0
        for k in range(i + 1, n):
            if lam[k] < last <= outer[k]:
                below += 1
        above = 0
        for k in range(i):
            if lam[k] <= first < outer[k]:
                above += 1
        low[i], high[i] = above, min(i, m - 1 - below)
    # The allowed labels of each row form the interval low[i]..high[i]; the
    # lattice rule removes label j (and hence all larger labels) from rows
    # not below the earliest row that allows label j - 1.
    earliest = -1
    for j in range(m):
        for i in range(earliest + 1 if j else 0):
            if high[i] >= j:
                high[i] = j - 1
        earliest = next((i for i in live if low[i] <= j <= high[i]), None)
        if earliest is None:
            raise ArithmeticError(f"label {j} fits nowhere: {outer}, {inner}, {content}")
    edges = 0
    for i in live:
        if high[i] < low[i]:
            raise ArithmeticError(f"row {i} admits no label: {outer}, {inner}, {content}")
        edges += high[i] - low[i] + 1
    # Rows and labels form a bipartite graph whose components are separated
    # exactly at the label gaps j | j+1 that no row interval bridges.
    if m == 0:
        return 0  # then outer == inner and the polytope is a point
    components = 1 + sum(
        1 for j in range(m - 1) if not any(low[i] <= j < high[i] for i in live)
    )
    return edges - (len(live) + m - components)


# ------------------------------------------------------------ the LR polytope

def lr_polytope(outer: Partition, inner: Partition, content: Partition):
    """Inequalities/equations (Normaliz inhomogeneous format) for LR tableaux.

    Variables a[i][j], 0 <= j <= i < n: number of labels j in row i.  Every
    returned row is ``coefficients + [constant]`` meaning
    ``coefficients . a + constant >= 0`` (inequalities) or ``= 0``.
    """
    n = len(outer)
    lam, nu, mu = pad(inner, n), list(outer), pad(content, n)
    index = {}
    for i in range(n):
        for j in range(i + 1):
            index[(i, j)] = len(index)
    width = len(index)

    def blank() -> list[int]:
        return [0] * (width + 1)

    inequalities, equations = [], []
    for position in index.values():  # a[i][j] >= 0
        row = blank()
        row[position] = 1
        inequalities.append(row)
    for i in range(n):  # row sums
        row = blank()
        for j in range(i + 1):
            row[index[(i, j)]] = 1
        row[width] = -(nu[i] - lam[i])
        equations.append(row)
    for j in range(n):  # content
        row = blank()
        for i in range(j, n):
            row[index[(i, j)]] = 1
        row[width] = -mu[j]
        equations.append(row)
    # Column strictness between rows i and i+1, labels k = 0..i:
    # lam[i+1] + sum_{j<=k} a[i+1][j] <= lam[i] + sum_{j<k} a[i][j].
    for i in range(n - 1):
        for k in range(i + 1):
            row = blank()
            for j in range(k + 1):
                row[index[(i + 1, j)]] -= 1
            for j in range(k):
                row[index[(i, j)]] += 1
            row[width] = lam[i] - lam[i + 1]
            inequalities.append(row)
    # Lattice word: sum_{i'<=i} a[i'][j+1] <= sum_{i'<i} a[i'][j], j+1 <= i.
    for i in range(n):
        for j in range(i):
            row = blank()
            for i2 in range(j + 1, i + 1):
                row[index[(i2, j + 1)]] -= 1
            for i2 in range(j, i):
                row[index[(i2, j)]] += 1
            inequalities.append(row)
    return inequalities, equations


def normaliz_polynomial(outer, inner, content) -> tuple[int, list[int], int]:
    """(dimension, numerators, denominator) of the Ehrhart polynomial."""
    from PyNormaliz import Cone

    inequalities, equations = lr_polytope(outer, inner, content)
    cone = Cone(inhom_inequalities=inequalities, inhom_equations=equations)
    dimension = int(cone.AffineDim())
    *components, denominator = cone.EhrhartQuasiPolynomial()
    if len(components) != 1:
        raise ArithmeticError(f"Ehrhart quasi-polynomial has period {len(components)}")
    numerators = [int(c) for c in components[0]]
    while numerators and numerators[-1] == 0:
        numerators.pop()
    if len(numerators) - 1 != dimension:
        raise ArithmeticError(f"degree {len(numerators) - 1} != dimension {dimension}")
    return dimension, numerators, int(denominator)


# --------------------------------------------------------- independent counter

class LrCount:
    """ctypes wrapper of lr_count.cpp (exact row DP, unsigned 128-bit)."""

    def __init__(self, library: str | Path) -> None:
        self.lib = ctypes.CDLL(str(Path(library).resolve()))
        ints = ctypes.POINTER(ctypes.c_int)
        self.lib.lr_count_series.argtypes = [
            ctypes.c_int, ints, ints, ints, ctypes.c_int, ctypes.c_int,
            ctypes.c_longlong, ctypes.c_char_p, ctypes.c_int,
            ctypes.POINTER(ctypes.c_ulonglong),
        ]
        self.lib.lr_count_series.restype = ctypes.c_int
        self.size = 1 << 14
        self.buffer = ctypes.create_string_buffer(self.size)
        self.work = ctypes.c_ulonglong(0)

    def series(self, outer, inner, content, first: int, last: int, limit: int = 0) -> list[int]:
        """Values for t = first..last (fewer if the running sum passes limit).

        ``self.work.value`` is then the number of DP search nodes visited.
        """
        self.work.value = 0
        n = len(outer)
        if len(inner) > n or len(content) > n:
            return [0] * (last - first + 1)
        if n == 0:
            return [1] * (last - first + 1)
        array = ctypes.c_int * n
        written = self.lib.lr_count_series(
            n, array(*outer), array(*pad(inner, n)), array(*pad(content, n)),
            first, last, limit, self.buffer, self.size, ctypes.byref(self.work),
        )
        if written < 0:
            raise ArithmeticError(
                f"lr_count status {-written} for {outer},{inner},{content}"
            )
        raw = self.buffer.value.decode()
        return [int(x) for x in raw.split(",")] if written else []


# ----------------------------------------------------------------- polynomials

_STIRLING: list[list[int]] = [[1]]  # signed Stirling numbers of the first kind


def stirling_row(k: int) -> list[int]:
    while len(_STIRLING) <= k:
        prev = _STIRLING[-1]
        order = len(_STIRLING) - 1
        row = [0] * (len(prev) + 1)
        for j, value in enumerate(prev):  # falling(t, order+1) = falling(t, order)*(t-order)
            row[j + 1] += value
            row[j] -= order * value
        _STIRLING.append(row)
    return _STIRLING[k]


def forward_differences(values: Sequence[int]) -> list[int]:
    """[Delta^k values(0) for k = 0..len-1] in exact integers."""
    row, out = list(values), []
    while row:
        out.append(row[0])
        row = [b - a for a, b in zip(row, row[1:])]
    return out


def interpolate(values: Sequence[int]) -> tuple[list[int], int]:
    """Interpolant through (t, values[t]), t = 0..D, as (numerators, D!).

    The power-basis coefficient of t^j is numerators[j] / D!.
    """
    degree = len(values) - 1
    differences = forward_differences(values)
    scale = math.factorial(degree)
    numerators = [0] * (degree + 1)
    for k, delta in enumerate(differences):
        if delta:
            factor = delta * (scale // math.factorial(k))
            for j, s in enumerate(stirling_row(k)):
                numerators[j] += factor * s
    while len(numerators) > 1 and numerators[-1] == 0:
        numerators.pop()
    return numerators, scale


def fraction_text(numerator: int, denominator: int) -> str:
    value = Fraction(numerator, denominator)
    return str(value.numerator) if value.denominator == 1 else str(value)


def line_digest(outer, a, b, numerators: Sequence[int], scale: int) -> int:
    """SHA-256 of one triple's canonical line; a box digest is their sum mod 2^256."""
    line = "{}|{}|{}|{}".format(
        tuple(outer), tuple(a), tuple(b), ",".join(fraction_text(x, scale) for x in numerators)
    )
    return int(hashlib.sha256(line.encode()).hexdigest(), 16)


# --------------------------------------------------------------- the pipeline

class Search:
    def __init__(self, library: str, small_limit: int, full_limit: int, t2_limit: int) -> None:
        import lrcalc
        import PyNormaliz_cpp

        PyNormaliz_cpp.NmzSetNumberOfNormalizThreads(1)
        self.lrcalc = lrcalc
        self.counter = LrCount(library)
        self.small_limit = small_limit
        self.full_limit = full_limit
        self.t2_limit = t2_limit

    def lrcalc_value(self, outer, inner, content, t: int) -> int:
        return self.lrcalc.lrcoef(
            [t * x for x in outer], [t * x for x in inner], [t * x for x in content]
        )

    def polynomial(self, outer, inner, content, expected: int) -> dict:
        """Stretched polynomial of one triple with all checks (raises on mismatch)."""
        # All six orientations share P, so each bounds its degree.  The DP
        # starts with the shorter content (usually the cheaper of the two).
        triples = orientations(outer, inner, content)
        bound = min(degree_bound(*triple) for triple in triples)
        if (len(content), sum(content), content) > (len(inner), sum(inner), inner):
            inner, content = content, inner
        values = [1] + self.counter.series(outer, inner, content, 1, bound + 1, self.small_limit)
        if values[1] != expected:
            raise ArithmeticError(f"lr_count {values[1]} != lrcalc {expected}")
        record = {"outer": list(outer), "inner": list(inner), "content": list(content)}
        if len(values) == bound + 2 and sum(values) <= self.small_limit + 1:
            # Regime A: degree <= bound; lrcalc recomputes every value.
            for t in range(2, bound + 2):
                if self.lrcalc_value(outer, inner, content, t) != values[t]:
                    raise ArithmeticError(f"lrcalc disagrees at t={t}")
            used = bound
            record["regime"] = "A"
            record["lrcalc_stretches"] = bound + 1
        else:
            # Regime B: Normaliz dimension d and Ehrhart polynomial.
            dimension, normaliz, denominator = normaliz_polynomial(outer, inner, content)
            if dimension > bound:
                raise ArithmeticError(f"Normaliz dimension {dimension} > degree bound {bound}")
            if len(values) < dimension + 2:
                # The DP cost of the six orientations differs by up to ~100x;
                # all six count P(3) (they must agree) and the one that
                # visits the fewest nodes computes the remaining values.
                probe, costs = set(), []
                for triple in triples:
                    probe.update(self.counter.series(*triple, 3, 3))
                    costs.append(self.counter.work.value)
                if len(probe) != 1:
                    raise ArithmeticError(f"orientations disagree at t=3: {probe}")
                best = costs.index(min(costs))
                record["orientation"] = best
                values += self.counter.series(*triples[best], len(values), dimension + 1)
            used = dimension
            record["regime"] = "B"
            record["normaliz"] = [normaliz, denominator]
            checked = 1
            if sum(values) <= self.full_limit:
                stretches = range(2, len(values))
            elif len(values) > 2 and values[2] <= self.t2_limit:
                stretches = [2]
            else:
                stretches = []
            for t in stretches:
                if self.lrcalc_value(outer, inner, content, t) != values[t]:
                    raise ArithmeticError(f"lrcalc disagrees at t={t}")
                checked += 1
            record["lrcalc_stretches"] = checked
        numerators, scale = interpolate(values[: used + 1])
        # Every further value (at least t = used + 1) must lie on the interpolant.
        for k, delta in enumerate(forward_differences(values)):
            if k > used and delta != 0:
                raise ArithmeticError(f"extra stretch values disagree (difference order {k})")
        if record["regime"] == "B":
            normaliz, denominator = record.pop("normaliz")
            if len(normaliz) != len(numerators) or any(
                a * denominator != b * scale for a, b in zip(numerators, normaliz)
            ):
                raise ArithmeticError("Normaliz polynomial differs from interpolation")
        record["degree"] = len(numerators) - 1
        record["values"] = values
        record["numerators"] = numerators
        record["scale"] = scale
        return record

    def run_size(self, rows: int, size: int, shard: int, shards: int, report) -> dict:
        started = time.monotonic()
        stats = Counter()
        degrees = Counter()
        digest = 0
        best = None  # (positive coefficient / P(1), degree index, record)
        for pair_index, (a, b) in enumerate(pairs_of_size(size, rows)):
            if pair_index % shards != shard:
                continue
            stats["pairs"] += 1
            product = self.lrcalc.mult(list(a), list(b), rows)
            identity = sum(c * weyl_dimension(nu, rows) for nu, c in product.items())
            if identity != weyl_dimension(a, rows) * weyl_dimension(b, rows):
                raise ArithmeticError(f"incomplete product for {a} * {b}")
            for outer, coefficient in sorted(product.items()):
                record = self.polynomial(tuple(outer), a, b, coefficient)
                stats["triples"] += 1
                stats["regime_" + record["regime"]] += 1
                degrees[record["degree"]] += 1
                numerators, scale = record["numerators"], record["scale"]
                if any(x == 0 for x in numerators):
                    stats["with_zero_coefficient"] += 1
                digest = (digest + line_digest(outer, a, b, numerators, scale)) % (1 << 256)
                if any(x < 0 for x in numerators):
                    stats["negative"] += 1
                    report({"status": "NEGATIVE_COEFFICIENT", "record": serial(record)})
                for k in range(1, len(numerators)):
                    if numerators[k] > 0:
                        score = Fraction(numerators[k], scale * record["values"][1])
                        if best is None or score < best[0]:
                            best = (score, k, record)
        result = {
            "rows": rows,
            "size": size,
            "shard": f"{shard}/{shards}",
            "pairs": stats["pairs"],
            "triples": stats["triples"],
            "negative": stats["negative"],
            "with_zero_coefficient": stats["with_zero_coefficient"],
            "regime_A": stats["regime_A"],
            "regime_B": stats["regime_B"],
            "degree_histogram": {str(k): v for k, v in sorted(degrees.items())},
            "digest": f"{digest:064x}",
            "seconds": round(time.monotonic() - started, 3),
        }
        if best is not None:
            result["smallest_normalized_coefficient"] = {
                "value": str(best[0]),
                "power": best[1],
                "record": serial(best[2]),
            }
        return result


def serial(record: dict) -> dict:
    out = {k: v for k, v in record.items() if k not in ("numerators", "scale")}
    out["values"] = [str(v) for v in record["values"]]
    out["coefficients"] = [fraction_text(x, record["scale"]) for x in record["numerators"]]
    return out


# ------------------------------------------------------------- shard merging

def merge_logs(paths: Sequence[str]) -> dict:
    """Combine per-shard size records (JSON lines) into one record per box size."""
    shards: dict[tuple[int, int], dict[str, dict]] = {}
    negatives = []
    for path in paths:
        for line in Path(path).read_text().splitlines():
            record = json.loads(line)
            if record.get("status") == "NEGATIVE_COEFFICIENT":
                negatives.append(record)
            elif "size" in record:
                key = (record["rows"], record["size"])
                if record["shard"] in shards.setdefault(key, {}):
                    raise ValueError(f"duplicate shard {record['shard']} for {key}")
                shards[key][record["shard"]] = record
    sizes = []
    for (rows, size), parts in sorted(shards.items()):
        count = {int(name.split("/")[1]) for name in parts}
        if len(count) != 1 or set(parts) != {f"{k}/{min(count)}" for k in range(min(count))}:
            raise ValueError(f"incomplete shards for rows={rows} size={size}: {sorted(parts)}")
        merged = {"rows": rows, "size": size, "shards": min(count)}
        for field in ("pairs", "triples", "negative", "with_zero_coefficient",
                      "regime_A", "regime_B"):
            merged[field] = sum(part[field] for part in parts.values())
        histogram = Counter()
        for part in parts.values():
            histogram.update({int(k): v for k, v in part["degree_histogram"].items()})
        merged["degree_histogram"] = {str(k): v for k, v in sorted(histogram.items())}
        merged["digest"] = "{:064x}".format(
            sum(int(part["digest"], 16) for part in parts.values()) % (1 << 256)
        )
        merged["shard_seconds"] = round(sum(part["seconds"] for part in parts.values()), 1)
        smallest = [part["smallest_normalized_coefficient"] for part in parts.values()
                    if "smallest_normalized_coefficient" in part]
        if smallest:
            merged["smallest_normalized_coefficient"] = min(
                smallest, key=lambda x: (Fraction(x["value"]), x["record"]["outer"])
            )
        sizes.append(merged)
    boxes = []  # maximal runs of consecutive complete sizes, per row bound
    for entry in sizes:
        last = boxes[-1] if boxes else None
        if last and last["rows_at_most"] == entry["rows"] and last["max_size"] == entry["size"] - 1:
            last["max_size"] = entry["size"]
            last["pairs"] += entry["pairs"]
            last["triples"] += entry["triples"]
        else:
            boxes.append({"rows_at_most": entry["rows"], "min_size": entry["size"],
                          "max_size": entry["size"], "pairs": entry["pairs"],
                          "triples": entry["triples"]})
    return {"exhausted": boxes, "negative_records": negatives, "per_size": sizes}


# ----------------------------------------------------------------- self-test

# Stretched polynomials (coefficients of t^0, t^1, ...) recorded by full runs.
KNOWN_POLYNOMIALS = [
    ((3, 2, 1), (2, 1), (2, 1), "1 1"),
    ((4, 3, 2, 1), (3, 2, 1), (3, 1), "1 3/2 1/2"),
    ((4, 3, 2, 2, 1), (3, 2, 1), (3, 2, 1), "1 11/6 1 1/6"),
    ((6, 4, 3, 2, 1), (4, 3, 2, 1), (3, 2, 1), "1 38/15 31/12 17/12 5/12 1/20"),
    ((8, 5, 4, 3, 2, 1, 1), (4, 2, 2, 2, 1), (5, 4, 3, 1),
     "1 363/140 469/180 967/720 7/18 23/360 1/180 1/5040"),
    ((9, 8, 5, 4, 3, 1), (8, 4, 3, 1, 1), (5, 3, 2, 2, 1),
     "1 199/70 16399/5040 359/180 2087/2880 29/180 31/1440 1/630 1/20160"),
]


def self_test(library: str | None, box_rows: int, box_sizes: int) -> dict:
    """Exact checks without lrcalc or Normaliz (pure Python; C++ DP if given).

    Values come from ``lr_tableau_dp.py`` (pure Python, shares no code with
    lr_count.cpp).  With ``library`` the C++ DP must reproduce them: in all
    six orientations for t <= 4, and beyond that in the orientation the
    search would pick (fewest DP nodes at t = 3).  Checks: the recorded
    polynomials above; the degree-11 example of closest_positive.json; and a
    recomputation of the boxes B(box_rows, s), s <= box_sizes, whose per-size
    pair and triple counts, degree histograms and digests must match
    exhaustive_summary.json.
    """
    from lr_tableau_dp import lr_coefficient

    counter = LrCount(library) if library else None
    here = Path(__file__).resolve().parent
    compared = 0

    def check_counter(outer, inner, content, expected: list[int]) -> None:
        nonlocal compared
        last = len(expected) - 1
        low = min(last, 4)
        triples = orientations(outer, inner, content)
        costs = []
        for triple in triples:
            if counter.series(*triple, 1, low) != expected[1 : low + 1]:
                raise AssertionError(f"lr_count differs from lr_tableau_dp on {triple}")
            counter.series(*triple, 3, 3)
            costs.append(counter.work.value)
        best = triples[costs.index(min(costs))]
        if counter.series(*best, low + 1, last) != expected[low + 1 :]:
            raise AssertionError(f"lr_count differs from lr_tableau_dp on {best}")
        compared += 6 * low + last - low

    def values(outer, inner, content, last: int) -> list[int]:
        oracle = [1] + [
            lr_coefficient(*(tuple(t * x for x in p) for p in (outer, inner, content)))
            for t in range(1, last + 1)
        ]
        if counter is not None:
            check_counter(outer, inner, content, oracle)
        return oracle

    def polynomial(outer, inner, content) -> tuple[list[int], int]:
        bound = min(degree_bound(*triple) for triple in orientations(outer, inner, content))
        data = values(outer, inner, content, bound + 1)
        numerators, scale = interpolate(data[: bound + 1])
        if forward_differences(data)[bound + 1] != 0:
            raise AssertionError(f"extra value off the interpolant for {outer},{inner},{content}")
        return numerators, scale

    for outer, inner, content, text in KNOWN_POLYNOMIALS:
        numerators, scale = polynomial(outer, inner, content)
        got = " ".join(fraction_text(x, scale) for x in numerators)
        if got != text:
            raise AssertionError(f"{outer},{inner},{content}: {got} != {text}")

    example = json.loads((here / "closest_positive.json").read_text())
    outer, inner, content = (tuple(example[k]) for k in ("lambda", "mu", "nu"))
    recorded = [int(v) for v in example["values_t_0_through_12"]]
    numerators, scale = interpolate(recorded[:12])
    if forward_differences(recorded)[12] != 0 or [
        fraction_text(x, scale) for x in numerators
    ] != example["polynomial_coefficients_ascending"]:
        raise AssertionError("closest_positive.json is not self-consistent")
    if min(degree_bound(*triple) for triple in orientations(outer, inner, content)) != 11:
        raise AssertionError("degree bound of the closest_positive example is not 11")
    # Pure Python stops at t = 3; the C++ DP reproduces t = 1..12.
    if values(outer, inner, content, 3) != recorded[:4]:
        raise AssertionError("closest_positive values differ")
    if counter is not None:
        check_counter(outer, inner, content, recorded)

    summary = json.loads((here / "exhaustive_summary.json").read_text())
    expected = {(e["rows"], e["size"]): e for e in summary["per_size"]}
    triples = 0
    for size in range(1, box_sizes + 1):
        histogram, digest, count, pairs = Counter(), 0, 0, 0
        for a, b in pairs_of_size(size, box_rows):
            pairs += 1
            identity = 0
            for outer in partitions(size, size, box_rows):
                if len(a) > len(outer) or len(b) > len(outer) or any(
                    x > y for x, y in zip(a, outer)
                ) or any(x > y for x, y in zip(b, outer)):
                    continue
                coefficient = lr_coefficient(outer, a, b)
                if coefficient == 0:
                    continue
                identity += coefficient * weyl_dimension(outer, box_rows)
                numerators, scale = polynomial(outer, a, b)
                if any(x < 0 for x in numerators):
                    raise AssertionError(f"NEGATIVE coefficient: {outer},{a},{b}")
                histogram[len(numerators) - 1] += 1
                digest = (digest + line_digest(outer, a, b, numerators, scale)) % (1 << 256)
                count += 1
            if identity != weyl_dimension(a, box_rows) * weyl_dimension(b, box_rows):
                raise AssertionError(f"dimension identity fails for {a} * {b}")
        entry = expected[(box_rows, size)]
        if (pairs, count, f"{digest:064x}") != (entry["pairs"], entry["triples"], entry["digest"]):
            raise AssertionError(f"B({box_rows},{size}) differs from exhaustive_summary.json")
        if {str(k): v for k, v in sorted(histogram.items())} != entry["degree_histogram"]:
            raise AssertionError(f"B({box_rows},{size}) degree histogram differs")
        triples += count
    return {
        "self_test": "passed",
        "known_polynomials": len(KNOWN_POLYNOMIALS) + 1,
        "box": f"B({box_rows}, 1..{box_sizes})",
        "box_triples": triples,
        "lr_count_values_compared": compared,
    }


def parse_partition(value: str) -> Partition:
    parts = tuple(int(x) for x in value.split(",") if x != "")
    if any(x <= 0 for x in parts) or any(x < y for x, y in zip(parts, parts[1:])):
        raise argparse.ArgumentTypeError(f"not a partition: {value}")
    return parts


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--library", help="liblrcount shared library (from lr_count.cpp)")
    parser.add_argument("--rows", type=int, default=5)
    parser.add_argument("--min-size", type=int, default=1)
    parser.add_argument("--max-size", type=int, default=10)
    parser.add_argument("--shard", type=int, default=0)
    parser.add_argument("--shards", type=int, default=1)
    parser.add_argument("--small-limit", type=int, default=20_000,
                        help="regime A if sum of P(1..D+1) stays <= this")
    parser.add_argument("--full-limit", type=int, default=200_000,
                        help="regime B: lrcalc recomputes all stretches if sum <= this")
    parser.add_argument("--t2-limit", type=int, default=5_000_000,
                        help="regime B: lrcalc recomputes P(2) if P(2) <= this")
    parser.add_argument("--triple", nargs=3, type=parse_partition,
                        metavar=("OUTER", "INNER", "CONTENT"),
                        help="compute and print one stretched polynomial")
    parser.add_argument("--self-test", action="store_true",
                        help="exact checks without lrcalc/Normaliz (B(rows, 1..max-size))")
    parser.add_argument("--merge", nargs="+", metavar="LOG",
                        help="merge shard logs into one summary (JSON on stdout)")
    args = parser.parse_args()

    def report(obj: dict) -> None:
        print(json.dumps(obj), flush=True)

    if args.merge:
        print(json.dumps(merge_logs(args.merge), indent=1))
        return 0
    if args.self_test:
        report(self_test(args.library, args.rows, args.max_size))
        return 0
    if not args.library:
        parser.error("--library is required for searches")
    search = Search(args.library, args.small_limit, args.full_limit, args.t2_limit)

    if args.triple:
        outer, inner, content = args.triple
        expected = search.lrcalc.lrcoef(list(outer), list(inner), list(content))
        if expected == 0:
            report({"status": "zero", "outer": outer, "inner": inner, "content": content})
            return 0
        report(serial(search.polynomial(outer, inner, content, expected)))
        return 0
    if not (1 <= args.rows <= 7 and 0 <= args.shard < args.shards):
        parser.error("need 1 <= rows <= 7 and 0 <= shard < shards")
    for size in range(args.min_size, args.max_size + 1):
        report(search.run_size(args.rows, size, args.shard, args.shards, report))
    return 0


if __name__ == "__main__":
    sys.exit(main())
