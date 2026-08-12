#!/usr/bin/env python3
"""Independently verify the subdivided-claw radius counterexample.

This certificate uses only the Python standard library.  It has its own
graph6 decoder and tuple-state recolouring graph implementation, separate
from ``recolor_radius_exact.cpp``.  Every colour-name orbit representative
receives a complete, unpruned BFS.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import re
import subprocess
import time
from collections import Counter, deque
from pathlib import Path


HERE = Path(__file__).resolve().parent


def decode_graph6(record: str) -> tuple[int, tuple[tuple[int, int], ...]]:
    raw = record.encode("ascii")
    if not raw or raw[0] == 126:
        raise ValueError("only short graph6 records are accepted")
    if any(byte < 63 or byte > 126 for byte in raw):
        raise ValueError("invalid graph6 byte")
    order = raw[0] - 63
    edge_bits = order * (order - 1) // 2
    expected_length = 1 + (edge_bits + 5) // 6
    if len(raw) != expected_length:
        raise ValueError(
            f"noncanonical graph6 length {len(raw)}; expected {expected_length}"
        )

    payload: list[int] = []
    for byte in raw[1:]:
        word = byte - 63
        payload.extend((word >> shift) & 1 for shift in range(5, -1, -1))
    if any(payload[edge_bits:]):
        raise ValueError("nonzero graph6 padding bits")

    edges: list[tuple[int, int]] = []
    position = 0
    for upper in range(1, order):
        for lower in range(upper):
            if payload[position]:
                edges.append((lower, upper))
            position += 1
    if position != edge_bits:
        raise AssertionError("graph6 decoder consumed the wrong number of bits")
    return order, tuple(sorted(edges))


def canonical_under_colour_names(state: tuple[int, ...]) -> bool:
    """Recognize the unique restricted-growth representative of its orbit."""
    if state[0] != 0:
        return False
    largest = 0
    for colour in state[1:]:
        if colour > largest + 1:
            return False
        largest = max(largest, colour)
    return True


def canonicalise(state: tuple[int, ...]) -> tuple[int, ...]:
    renaming: dict[int, int] = {}
    result: list[int] = []
    for colour in state:
        if colour not in renaming:
            renaming[colour] = len(renaming)
        result.append(renaming[colour])
    return tuple(result)


def verify_k(
    order: int,
    edges: tuple[tuple[int, int], ...],
    expected: dict[str, object],
) -> dict[str, object]:
    colours = int(expected["k"])
    neighbours: list[list[int]] = [[] for _ in range(order)]
    for left, right in edges:
        neighbours[left].append(right)
        neighbours[right].append(left)

    states = [
        state
        for state in itertools.product(range(colours), repeat=order)
        if all(state[left] != state[right] for left, right in edges)
    ]
    index = {state: number for number, state in enumerate(states)}
    if len(index) != len(states):
        raise AssertionError("proper-colouring enumeration contains a duplicate")
    if len(states) != colours * (colours - 1) ** (order - 1):
        raise AssertionError("proper-colouring count disagrees with the tree formula")

    adjacency: list[list[int]] = [[] for _ in states]
    for number, state in enumerate(states):
        candidate = list(state)
        for vertex in range(order):
            old_colour = state[vertex]
            forbidden = {state[other] for other in neighbours[vertex]}
            for new_colour in range(colours):
                if new_colour == old_colour or new_colour in forbidden:
                    continue
                candidate[vertex] = new_colour
                other_number = index.get(tuple(candidate))
                if other_number is None:
                    raise AssertionError("locally proper recolouring was not enumerated")
                adjacency[number].append(other_number)
            candidate[vertex] = old_colour

    directed_arcs = sum(map(len, adjacency))
    if directed_arcs % 2:
        raise AssertionError("recolouring graph has an odd directed-arc count")
    for here, adjacent in enumerate(adjacency):
        if len(adjacent) != len(set(adjacent)):
            raise AssertionError("duplicate recolouring edge")
        for other in adjacent:
            if here not in adjacency[other]:
                raise AssertionError("recolouring adjacency is not symmetric")

    def bfs(source: int) -> tuple[int, int, list[int]]:
        distance = [-1] * len(states)
        distance[source] = 0
        queue = deque([source])
        reached = 0
        eccentricity = 0
        layers: list[int] = []
        while queue:
            here = queue.popleft()
            reached += 1
            depth = distance[here]
            eccentricity = depth
            if depth == len(layers):
                layers.append(0)
            layers[depth] += 1
            for other in adjacency[here]:
                if distance[other] == -1:
                    distance[other] = depth + 1
                    queue.append(other)
        return eccentricity, reached, layers

    _, reached, _ = bfs(0)
    connected = reached == len(states)
    if not connected:
        raise AssertionError(
            f"C_{colours} is disconnected: reached {reached}/{len(states)} states"
        )

    representatives = [
        number
        for number, state in enumerate(states)
        if canonical_under_colour_names(state)
    ]
    expected_orbits = {states[number] for number in representatives}
    observed_orbits = {canonicalise(state) for state in states}
    if observed_orbits != expected_orbits:
        raise AssertionError("restricted-growth orbit reduction is incomplete")

    representative_eccentricities: list[int] = []
    for source in representatives:
        eccentricity, source_reached, _ = bfs(source)
        if source_reached != len(states):
            raise AssertionError("a radius BFS did not reach the full graph")
        representative_eccentricities.append(eccentricity)

    radius = min(representative_eccentricities)
    diameter = max(representative_eccentricities)
    centre_sources = [
        source
        for source, eccentricity in zip(
            representatives, representative_eccentricities, strict=True
        )
        if eccentricity == radius
    ]

    eccentricity_distribution: Counter[int] = Counter()
    labelled_centres = 0
    for source, eccentricity in zip(
        representatives, representative_eccentricities, strict=True
    ):
        used_colours = len(set(states[source]))
        orbit_size = math.factorial(colours) // math.factorial(colours - used_colours)
        eccentricity_distribution[eccentricity] += orbit_size
        if eccentricity == radius:
            labelled_centres += orbit_size
    if sum(eccentricity_distribution.values()) != len(states):
        raise AssertionError("colour-orbit sizes do not recover every labelled state")

    example_centre = tuple(int(value) for value in expected["example_centre"])
    if example_centre not in index:
        raise AssertionError("recorded centre is not a proper colouring")
    centre_eccentricity, centre_reached, centre_layers = bfs(index[example_centre])
    if centre_reached != len(states) or centre_eccentricity != radius:
        raise AssertionError("recorded centre does not realize the radius")

    actual: dict[str, object] = {
        "k": colours,
        "states": len(states),
        "undirected_recolouring_edges": directed_arcs // 2,
        "connected": connected,
        "colour_orbits": len(representatives),
        "radius": radius,
        "diameter": diameter,
        "centre_colour_orbits": len(centre_sources),
        "labelled_centres": labelled_centres,
        "labelled_eccentricity_distribution": {
            str(key): value for key, value in sorted(eccentricity_distribution.items())
        },
        "example_centre": list(example_centre),
        "example_centre_distance_layers": centre_layers,
        "sources_fully_explored": len(representatives),
    }
    if actual != expected:
        raise AssertionError(
            "independent Python result differs from certificate:\n"
            f"expected={json.dumps(expected, sort_keys=True)}\n"
            f"actual={json.dumps(actual, sort_keys=True)}"
        )
    return actual


def verify_cpp(
    executable: Path,
    graph6: str,
    order: int,
    edges: tuple[tuple[int, int], ...],
    results: list[dict[str, object]],
) -> None:
    token_pattern = re.compile(r"([a-z_0-9]+)=([^ ]+)")
    for expected in results:
        colours = int(expected["k"])
        completed = subprocess.run(
            [str(executable), "exact", graph6, str(colours)],
            check=True,
            capture_output=True,
            text=True,
        )
        if completed.stderr:
            raise AssertionError(f"C++ verifier wrote to stderr: {completed.stderr!r}")
        fields = dict(token_pattern.findall(completed.stdout.strip()))
        observed = {
            "graph6": fields.get("graph6"),
            "n": int(fields["n"]),
            "m": int(fields["m"]),
            "k": int(fields["k"]),
            "connected": fields["connected"] == "1",
            "radius": int(fields["radius"]),
            "states": int(fields["states"]),
            "undirected_recolouring_edges": int(fields["recolouring_edges"]),
            "colour_orbits": int(fields["colour_orbits"]),
        }
        wanted = {
            "graph6": graph6,
            "n": order,
            "m": len(edges),
            "k": colours,
            "connected": expected["connected"],
            "radius": expected["radius"],
            "states": expected["states"],
            "undirected_recolouring_edges": expected[
                "undirected_recolouring_edges"
            ],
            "colour_orbits": expected["colour_orbits"],
        }
        if observed != wanted:
            raise AssertionError(f"C++ result {observed!r} != expected {wanted!r}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--data", type=Path, default=HERE / "counterexample.json"
    )
    parser.add_argument("--cpp", type=Path, required=True)
    args = parser.parse_args()

    started = time.perf_counter()
    certificate = json.loads(args.data.read_text(encoding="utf-8"))
    if certificate.get("schema_version") != 1:
        raise AssertionError("unsupported counterexample schema")
    graph6 = str(certificate["graph6"])
    order, edges = decode_graph6(graph6)
    recorded_edges = tuple(tuple(edge) for edge in certificate["edges"])
    if order != certificate["order"] or edges != recorded_edges:
        raise AssertionError("graph6 witness does not match the recorded graph")

    degrees = [0] * order
    for left, right in edges:
        degrees[left] += 1
        degrees[right] += 1
    expected_neighbourhoods = {
        0: {3, 6},
        1: {4, 6},
        2: {5, 6},
        3: {0},
        4: {1},
        5: {2},
        6: {0, 1, 2},
    }
    actual_neighbourhoods = {
        vertex: {
            other
            for edge in edges
            if vertex in edge
            for other in edge
            if other != vertex
        }
        for vertex in range(order)
    }
    if (
        len(edges) != order - 1
        or sorted(degrees) != [1, 1, 1, 2, 2, 2, 3]
        or actual_neighbourhoods != expected_neighbourhoods
    ):
        raise AssertionError("witness is not the recorded subdivided claw")

    expected_results = certificate["results"]
    results = [verify_k(order, edges, expected) for expected in expected_results]
    comparison = certificate["comparison"]
    if (
        int(comparison["k"]) < 3
        or int(comparison["next_k"]) != int(comparison["k"]) + 1
    ):
        raise AssertionError("witness does not compare consecutive palettes from k >= 3")
    if [result["k"] for result in results] != [
        comparison["k"],
        comparison["next_k"],
    ]:
        raise AssertionError("certificate compares the wrong consecutive palettes")
    strict_increase = results[0]["radius"] < results[1]["radius"]
    if strict_increase != bool(comparison["strict_increase"]) or not strict_increase:
        raise AssertionError("certificate does not exhibit a strict radius increase")

    verify_cpp(args.cpp.resolve(), graph6, order, edges, results)

    print(f"PASS graph6 {graph6} decodes as the 7-vertex subdivided claw")
    for result in results:
        print(
            "PASS independent Python exhaustive BFS: "
            f"C_{result['k']} connected, {result['states']} states, "
            f"{result['undirected_recolouring_edges']} edges, "
            f"radius {result['radius']}, diameter {result['diameter']}"
        )
    print("PASS independent C++ exact-radius results agree")
    print(
        f"PASS counterexample: {results[0]['radius']} < {results[1]['radius']} "
        f"({time.perf_counter() - started:.2f}s)"
    )


if __name__ == "__main__":
    main()
