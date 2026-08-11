#!/usr/bin/env python3
"""Exhaust all undirected circulant (3,10)-Ramsey candidates on Z/40Z.

A graph Cay(Z_40, S) is represented by choosing distances 1,...,19 and
optionally the antipodal distance 20.  Distance d < 20 contributes both d
and 40-d to S.  If a candidate is triangle-free and has independence number
at most 9, then its degree is at most 9, because every open neighbourhood in
a triangle-free graph is independent.  Consequently it suffices to enumerate
connection sets of degree at most 9; all larger-degree circulants already have
an independent 10-set inside every neighbourhood.

The independent-set test is an exact bit-set backtracking search.  For every
triangle-free connection set of degree <= 9, it searches for (and verifies) an
independent set of size 10.  Thus a zero value for ``survivors`` certifies that
there is no circulant graph on 40 vertices witnessing R(3,10) > 40.

This program uses only the Python standard library.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import platform
import sys
import time
from pathlib import Path


N = 40
TARGET = 10
ALL_VERTICES = (1 << N) - 1


def connection_residues(distances: tuple[int, ...], antipodal: bool) -> int:
    """Return S subset Z_40 as a bit mask (bit r means residue r is in S)."""
    mask = 0
    for d in distances:
        mask |= 1 << d
        mask |= 1 << (N - d)
    if antipodal:
        mask |= 1 << (N // 2)
    return mask


def rotate40(mask: int, shift: int) -> int:
    """Cyclically shift a 40-bit mask."""
    shift %= N
    return ((mask << shift) | (mask >> (N - shift))) & ALL_VERTICES


def adjacency_from_connection(connection: int) -> tuple[int, ...]:
    """Adjacency masks for Cay(Z_40,S)."""
    return tuple(rotate40(connection, v) for v in range(N))


def is_triangle_free(adjacency: tuple[int, ...]) -> bool:
    """An edge uv is in a triangle iff N(u) intersects N(v)."""
    for u in range(N):
        later_neighbours = adjacency[u] & ~((1 << (u + 1)) - 1)
        while later_neighbours:
            v_bit = later_neighbours & -later_neighbours
            v = v_bit.bit_length() - 1
            if adjacency[u] & adjacency[v]:
                return False
            later_neighbours ^= v_bit
    return True


def find_clique_of_size(
    candidates: int,
    need: int,
    adjacency: tuple[int, ...],
    chosen: tuple[int, ...] = (),
) -> tuple[int, ...] | None:
    """Exact branch-and-bound search for a clique of prescribed size.

    Vertices are considered once in increasing-bit order.  Intersecting with
    the chosen vertex's forward candidate neighbourhood makes every returned
    tuple a clique and makes the recursion exhaustive.
    """
    if need == 0:
        return chosen
    while candidates.bit_count() >= need:
        v_bit = candidates & -candidates
        candidates ^= v_bit
        v = v_bit.bit_length() - 1
        result = find_clique_of_size(
            candidates & adjacency[v], need - 1, adjacency, chosen + (v,)
        )
        if result is not None:
            return result
    return None


def find_independent_set(
    adjacency: tuple[int, ...], size: int
) -> tuple[int, ...] | None:
    complement = tuple(
        ALL_VERTICES & ~(adjacency[v] | (1 << v)) for v in range(N)
    )
    return find_clique_of_size(ALL_VERTICES, size, complement)


def find_independent_ten(adjacency: tuple[int, ...]) -> tuple[int, ...] | None:
    return find_independent_set(adjacency, TARGET)


def verify_witness(adjacency: tuple[int, ...], witness: tuple[int, ...]) -> bool:
    if len(witness) != TARGET or len(set(witness)) != TARGET:
        return False
    return all(
        not ((adjacency[u] >> v) & 1)
        for i, u in enumerate(witness)
        for v in witness[i + 1 :]
    )


def enumerate_candidates():
    """Yield every inverse-closed connection set having degree <= 9."""
    base_distances = range(1, N // 2)
    for antipodal in (False, True):
        for number_of_paired_distances in range(5):
            degree = 2 * number_of_paired_distances + int(antipodal)
            if degree > 9:
                continue
            for distances in itertools.combinations(
                base_distances, number_of_paired_distances
            ):
                yield distances, antipodal, degree


def multiply_connection_set(connection: int, unit: int) -> int:
    """Apply the group automorphism x -> unit*x of Z_40."""
    result = 0
    for residue in range(1, N):
        if (connection >> residue) & 1:
            result |= 1 << ((unit * residue) % N)
    return result


def canonical_multiplier_representative(connection: int) -> int:
    """Canonicalize under multiplication by units of Z_40.

    This is deliberately described as multiplier equivalence, not as a full
    graph-isomorphism classification: exceptional isomorphisms between
    circulants need not be multipliers.
    """
    units = (u for u in range(1, N) if math.gcd(u, N) == 1)
    return min(multiply_connection_set(connection, u) for u in units)


def distances_from_connection(connection: int) -> tuple[list[int], bool]:
    return (
        [d for d in range(1, N // 2) if (connection >> d) & 1],
        bool((connection >> (N // 2)) & 1),
    )


def run() -> dict:
    started = time.perf_counter()
    enumerated = 0
    triangle_free = 0
    certified_by_independent_ten = 0
    survivors: list[dict] = []
    alpha_exactly_ten: list[int] = []
    digest = hashlib.sha256()
    examples_by_degree: dict[int, dict] = {}

    for distances, antipodal, degree in enumerate_candidates():
        enumerated += 1
        connection = connection_residues(distances, antipodal)
        adjacency = adjacency_from_connection(connection)
        if not is_triangle_free(adjacency):
            continue
        triangle_free += 1

        witness = find_independent_ten(adjacency)
        if witness is None:
            survivors.append(
                {
                    "distances": list(distances),
                    "antipodal": antipodal,
                    "degree": degree,
                }
            )
            continue
        if not verify_witness(adjacency, witness):
            raise AssertionError("internal error: invalid independent-set witness")
        certified_by_independent_ten += 1
        if find_independent_set(adjacency, TARGET + 1) is None:
            alpha_exactly_ten.append(connection)
        record = (
            f"{','.join(map(str, distances))}|{int(antipodal)}|"
            f"{','.join(map(str, witness))}\n"
        )
        digest.update(record.encode("ascii"))
        examples_by_degree.setdefault(
            degree,
            {
                "distances": list(distances),
                "antipodal": antipodal,
                "independent_10_set": list(witness),
            },
        )

    tight_representatives = sorted(
        {canonical_multiplier_representative(c) for c in alpha_exactly_ten}
    )
    tight_representative_records = []
    for connection in tight_representatives:
        distances, antipodal = distances_from_connection(connection)
        adjacency = adjacency_from_connection(connection)
        witness = find_independent_ten(adjacency)
        assert witness is not None and verify_witness(adjacency, witness)
        tight_representative_records.append(
            {
                "distances": distances,
                "antipodal": antipodal,
                "degree": connection.bit_count(),
                "independent_10_set": list(witness),
            }
        )

    return {
        "problem": "circulant (3,10)-Ramsey graphs on 40 vertices",
        "n": N,
        "target_independence": TARGET,
        "parameterization": (
            "inverse-closed connection sets in Z_40; distances 1..19 plus 20"
        ),
        "degree_reduction": (
            "only degree <= 9 enumerated; degree >= 10 has an independent "
            "10-set in every neighbourhood when triangle-free"
        ),
        "candidate_connection_sets_degree_at_most_9": enumerated,
        "triangle_free_candidates_degree_at_most_9": triangle_free,
        "certified_with_independent_10_set": certified_by_independent_ten,
        "survivors": survivors,
        "triangle_free_candidates_with_independence_exactly_10": len(
            alpha_exactly_ten
        ),
        "tight_multiplier_classes": len(tight_representatives),
        "tight_multiplier_class_representatives": tight_representative_records,
        "witness_stream_sha256": digest.hexdigest(),
        "first_example_by_degree": examples_by_degree,
        "elapsed_seconds": time.perf_counter() - started,
        "python": sys.version,
        "platform": platform.platform(),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output",
        type=Path,
        help="optional JSON output path (stdout is always printed)",
    )
    args = parser.parse_args()
    result = run()
    rendered = json.dumps(result, indent=2, sort_keys=True)
    print(rendered)
    if args.output:
        args.output.write_text(rendered + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
