#!/usr/bin/env python3
"""Verify the bounded graph-atlas result with an independent Python BFS."""

from __future__ import annotations

import argparse
import functools
import hashlib
import itertools
import json
import subprocess
import time
from collections import Counter, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence


EXPECTED_DATA_SHA256 = "ad68465d32eb7679a1ed8b0aa7a7f1da366da9b1ef8566b04664c504e8876255"
EXPECTED_RECORDS_BY_ORDER = [0, 1, 2, 4, 11, 34, 156, 1044]
EXPECTED_C3_CONNECTED_BY_ORDER = [0, 1, 2, 3, 7, 13, 34, 85]
EXPECTED_ELIGIBLE_BY_ORDER = [0, 1, 2, 3, 7, 13, 34, 85]


@dataclass(frozen=True)
class Graph:
    adjacency: tuple[int, ...]

    @property
    def n(self) -> int:
        return len(self.adjacency)


@dataclass(frozen=True)
class RadiusResult:
    connected: bool
    radius: int | None
    states: int


def parse_graph6(record: str) -> Graph:
    """Parse a short graph6 record independently of the C++ bit reader."""

    if record.startswith(">>graph6<<"):
        record = record[10:]
    if not record or record[0] == "~":
        raise ValueError("only short nonempty graph6 records are supported")
    values = [ord(character) - 63 for character in record]
    if any(value < 0 or value > 63 for value in values):
        raise ValueError(f"invalid graph6 byte in {record!r}")
    n = values[0]
    edge_bits = n * (n - 1) // 2
    expected_length = 1 + (edge_bits + 5) // 6
    if len(record) != expected_length:
        raise ValueError(
            f"graph6 record for n={n} has length {len(record)}, "
            f"expected {expected_length}"
        )

    bit_string = "".join(f"{value:06b}" for value in values[1:])
    if any(bit != "0" for bit in bit_string[edge_bits:]):
        raise ValueError(f"nonzero graph6 padding in {record!r}")
    adjacency = [0] * n
    position = 0
    for upper in range(1, n):
        for lower in range(upper):
            if bit_string[position] == "1":
                adjacency[lower] |= 1 << upper
                adjacency[upper] |= 1 << lower
            position += 1
    return Graph(tuple(adjacency))


def proper_colourings(graph: Graph, colours: int) -> list[tuple[int, ...]]:
    edges = [
        (left, right)
        for right in range(graph.n)
        for left in range(right)
        if graph.adjacency[left] & (1 << right)
    ]
    return [
        state
        for state in itertools.product(range(colours), repeat=graph.n)
        if all(state[left] != state[right] for left, right in edges)
    ]


def restricted_growth(state: Sequence[int]) -> bool:
    """Choose one representative under global permutations of colour names."""

    if not state or state[0] != 0:
        return not state
    largest_seen = 0
    for colour in state[1:]:
        if colour > largest_seen + 1:
            return False
        largest_seen = max(largest_seen, colour)
    return True


@functools.cache
def exact_radius(graph: Graph, colours: int) -> RadiusResult:
    states = proper_colourings(graph, colours)
    if not states:
        return RadiusResult(False, None, 0)
    state_set = set(states)

    def bfs(
        source: tuple[int, ...], cutoff: int | None = None
    ) -> tuple[int, int | None]:
        distance = {source: 0}
        queue = deque([source])
        eccentricity = 0
        while queue:
            state = queue.popleft()
            depth = distance[state]
            eccentricity = max(eccentricity, depth)
            if cutoff is not None and eccentricity >= cutoff:
                return eccentricity, None
            for vertex in range(graph.n):
                forbidden = {
                    state[neighbour]
                    for neighbour in range(graph.n)
                    if graph.adjacency[vertex] & (1 << neighbour)
                }
                for replacement in range(colours):
                    if replacement == state[vertex] or replacement in forbidden:
                        continue
                    candidate = (
                        state[:vertex]
                        + (replacement,)
                        + state[vertex + 1 :]
                    )
                    if candidate not in distance:
                        if candidate not in state_set:
                            raise AssertionError("locally proper state was not enumerated")
                        distance[candidate] = depth + 1
                        queue.append(candidate)
        return eccentricity, len(distance)

    _, reached = bfs(states[0])
    if reached != len(states):
        return RadiusResult(False, None, len(states))

    best: int | None = None
    for source in states:
        if not restricted_growth(source):
            continue
        eccentricity, completed_reach = bfs(source, cutoff=best)
        if completed_reach is not None and (best is None or eccentricity < best):
            best = eccentricity
    if best is None:
        raise AssertionError("connected recolouring graph had no orbit representative")
    return RadiusResult(True, best, len(states))


def components(graph: Graph) -> list[Graph]:
    """Return induced connected components with fresh consecutive labels."""

    unseen = set(range(graph.n))
    answer: list[Graph] = []
    while unseen:
        root = min(unseen)
        unseen.remove(root)
        vertices = [root]
        queue = deque([root])
        while queue:
            vertex = queue.popleft()
            neighbours = [
                other
                for other in tuple(unseen)
                if graph.adjacency[vertex] & (1 << other)
            ]
            for other in neighbours:
                unseen.remove(other)
                vertices.append(other)
                queue.append(other)
        vertices.sort()
        new_index = {old: new for new, old in enumerate(vertices)}
        component_adjacency = []
        for old in vertices:
            mask = 0
            for neighbour in vertices:
                if graph.adjacency[old] & (1 << neighbour):
                    mask |= 1 << new_index[neighbour]
            component_adjacency.append(mask)
        answer.append(Graph(tuple(component_adjacency)))
    return answer


def componentwise_radius(graph: Graph, colours: int) -> RadiusResult:
    """Use the Cartesian-product decomposition over graph components."""

    results = [exact_radius(component, colours) for component in components(graph)]
    states = 1
    for result in results:
        states *= result.states
    if any(not result.connected or result.radius is None for result in results):
        return RadiusResult(False, None, states)
    radius = 0
    for result in results:
        assert result.radius is not None
        radius += result.radius
    return RadiusResult(True, radius, states)


def require_list(value: Any, name: str) -> list[int]:
    if not isinstance(value, list) or not all(isinstance(item, int) for item in value):
        raise TypeError(f"{name} must be a list of integers")
    return value


def main() -> None:
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=here / "atlas_1_7.g6")
    parser.add_argument("--result", type=Path, default=here / "atlas_result.json")
    parser.add_argument(
        "--cpp",
        type=Path,
        help="also run this compiled C++ verifier over the full seven-vertex atlas",
    )
    args = parser.parse_args()

    metadata = json.loads(args.result.read_text(encoding="utf-8"))
    if metadata.get("format_version") != 1:
        raise ValueError("unsupported result format")
    dataset = metadata["dataset"]
    payload = args.data.read_bytes()
    digest = hashlib.sha256(payload).hexdigest()
    if dataset["sha256"] != EXPECTED_DATA_SHA256:
        raise AssertionError("metadata does not contain the pinned dataset SHA-256")
    if digest != EXPECTED_DATA_SHA256:
        raise AssertionError(f"dataset SHA-256 {digest} does not match the pinned value")
    records = payload.decode("ascii").splitlines()
    if len(records) != len(set(records)):
        raise AssertionError("graph6 dataset contains duplicate records")
    graphs = [parse_graph6(record) for record in records]
    counts = [0] * 8
    for order, count in Counter(graph.n for graph in graphs).items():
        if not 0 <= order < len(counts):
            raise AssertionError(f"unexpected graph order {order}")
        counts[order] = count
    expected_counts = require_list(dataset["records_by_order"], "records_by_order")
    if expected_counts != EXPECTED_RECORDS_BY_ORDER:
        raise AssertionError("metadata does not contain the pinned per-order counts")
    if counts != EXPECTED_RECORDS_BY_ORDER:
        raise AssertionError(
            f"dataset order counts {counts}, expected {EXPECTED_RECORDS_BY_ORDER}"
        )
    if dataset["records"] != sum(EXPECTED_RECORDS_BY_ORDER):
        raise AssertionError("metadata does not contain the pinned record total")
    if len(records) != sum(EXPECTED_RECORDS_BY_ORDER):
        raise AssertionError("dataset record total does not match metadata")
    print(f"PASS dataset: {len(records)} unique records, SHA-256 {digest}")

    if args.cpp is not None:
        completed = subprocess.run(
            [str(args.cpp), "verify-atlas", str(args.data)],
            check=False,
            capture_output=True,
            text=True,
        )
        if completed.returncode != 0:
            raise AssertionError(
                "C++ verifier failed:\n" + completed.stdout + completed.stderr
            )
        observed = json.loads(completed.stdout)
        expected = metadata["exhaustive_cpp"]["result"]
        pinned_cpp_result = {
            "records_by_order": EXPECTED_RECORDS_BY_ORDER,
            "c3_connected_by_order": EXPECTED_C3_CONNECTED_BY_ORDER,
            "eligible_by_order": EXPECTED_ELIGIBLE_BY_ORDER,
            "counterexamples": 0,
        }
        if expected != pinned_cpp_result:
            raise AssertionError("metadata does not contain the pinned C++ result")
        if observed != expected:
            raise AssertionError(f"C++ result {observed}, expected {expected}")
        print(
            "PASS C++ exhaustive audit: "
            f"{sum(observed['records_by_order'])} graphs, "
            f"{sum(observed['eligible_by_order'])} eligible pairs, "
            f"{observed['counterexamples']} counterexamples"
        )

    audit = metadata["independent_python_audit"]
    maximum_order = int(audit["maximum_order"])
    if maximum_order != 7:
        raise AssertionError("metadata does not request the full order-7 Python audit")
    expected_eligible = require_list(
        audit["eligible_by_order"], "independent eligible_by_order"
    )
    if expected_eligible != EXPECTED_ELIGIBLE_BY_ORDER:
        raise AssertionError("metadata does not contain the pinned Python eligible counts")
    c3_connected = [0] * (maximum_order + 1)
    eligible = [0] * (maximum_order + 1)
    counterexamples: list[tuple[str, int, int]] = []
    checked_records = 0
    started = time.perf_counter()
    for record, graph in zip(records, graphs, strict=True):
        if graph.n > maximum_order:
            continue
        checked_records += 1
        low = componentwise_radius(graph, 3)
        if graph.n <= 6 and low != exact_radius(graph, 3):
            raise AssertionError(
                f"component reduction disagrees with direct C3 BFS for {record}"
            )
        if not low.connected:
            continue
        c3_connected[graph.n] += 1
        high = componentwise_radius(graph, 4)
        if graph.n <= 6 and high != exact_radius(graph, 4):
            raise AssertionError(
                f"component reduction disagrees with direct C4 BFS for {record}"
            )
        if not high.connected:
            continue
        eligible[graph.n] += 1
        if low.radius is None or high.radius is None:
            raise AssertionError("connected pair has no radius")
        if low.radius < high.radius:
            counterexamples.append((record, low.radius, high.radius))
    elapsed = time.perf_counter() - started

    if audit["records"] != sum(EXPECTED_RECORDS_BY_ORDER):
        raise AssertionError("metadata does not contain the pinned Python record total")
    if checked_records != sum(EXPECTED_RECORDS_BY_ORDER):
        raise AssertionError(
            f"Python checked {checked_records} records, expected {audit['records']}"
        )
    if eligible != expected_eligible:
        raise AssertionError(f"Python eligible counts {eligible}, expected {expected_eligible}")
    expected_c3_connected = require_list(
        audit["c3_connected_by_order"], "independent c3_connected_by_order"
    )
    if expected_c3_connected != EXPECTED_C3_CONNECTED_BY_ORDER:
        raise AssertionError(
            "metadata does not contain the pinned Python C3-connected counts"
        )
    if c3_connected != expected_c3_connected:
        raise AssertionError(
            f"Python C3-connected counts {c3_connected}, "
            f"expected {expected_c3_connected}"
        )
    if counterexamples:
        raise AssertionError(f"Python found counterexamples: {counterexamples}")
    if audit["counterexamples"] != 0:
        raise AssertionError("metadata does not record zero Python counterexamples")
    print(
        "PASS independent Python audit: "
        f"{checked_records} graphs through order {maximum_order}, "
        f"{sum(eligible)} eligible pairs, 0 counterexamples ({elapsed:.2f}s)"
    )


if __name__ == "__main__":
    main()
