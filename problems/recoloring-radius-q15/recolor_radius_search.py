#!/usr/bin/env python3
"""Exact search for a counterexample to Cambie--Cames van Batenburg--Cranston Q15.

For a graph G, C_k(G) has the proper k-colourings as vertices, adjacent when they
differ at exactly one graph vertex.  Question 15 asks, when C_k(G) and C_{k+1}(G)
are connected, whether rad C_k(G) >= rad C_{k+1}(G).

The search uses NetworkX's complete atlas of nonisomorphic graphs on at most seven
vertices.  Distances and radii are computed by integer BFS.  Global permutations of
colour names preserve eccentricity, so only one restricted-growth representative is
used as a BFS source; the BFS itself still ranges over every labelled colouring.
"""

from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
from itertools import product

import networkx as nx


@dataclass(frozen=True)
class RadiusResult:
    connected: bool
    radius: int | None
    center: tuple[int, ...] | None
    states: int


def canonical_colours(colouring: tuple[int, ...]) -> tuple[int, ...]:
    rename: dict[int, int] = {}
    next_colour = 0
    result = []
    for colour in colouring:
        if colour not in rename:
            rename[colour] = next_colour
            next_colour += 1
        result.append(rename[colour])
    return tuple(result)


def proper_colours(graph: nx.Graph, colours: int) -> list[tuple[int, ...]]:
    n = graph.number_of_nodes()
    edges = list(graph.edges())
    return [
        state
        for state in product(range(colours), repeat=n)
        if all(state[u] != state[v] for u, v in edges)
    ]


def radius(graph: nx.Graph, colours: int) -> RadiusResult:
    states = proper_colours(graph, colours)
    state_set = set(states)
    if not states:
        return RadiusResult(False, None, None, 0)

    neighbours = [tuple(graph.neighbors(v)) for v in graph.nodes()]

    def bfs(source: tuple[int, ...], cutoff: int | None = None) -> tuple[int, int]:
        distance = {source: 0}
        queue = deque([source])
        eccentricity = 0
        while queue:
            state = queue.popleft()
            depth = distance[state]
            eccentricity = max(eccentricity, depth)
            if cutoff is not None and eccentricity >= cutoff:
                return eccentricity, len(distance)
            for vertex in range(len(state)):
                forbidden = {state[u] for u in neighbours[vertex]}
                for colour in range(colours):
                    if colour == state[vertex] or colour in forbidden:
                        continue
                    candidate = state[:vertex] + (colour,) + state[vertex + 1 :]
                    if candidate not in distance:
                        # candidate is proper by the local forbidden-colour check.
                        assert candidate in state_set
                        distance[candidate] = depth + 1
                        queue.append(candidate)
        return eccentricity, len(distance)

    _, reached = bfs(states[0])
    if reached != len(states):
        return RadiusResult(False, None, None, len(states))

    sources = [state for state in states if canonical_colours(state) == state]
    best_radius: int | None = None
    best_center: tuple[int, ...] | None = None
    for source in sources:
        eccentricity, _ = bfs(source, cutoff=best_radius)
        if best_radius is None or eccentricity < best_radius:
            best_radius = eccentricity
            best_center = source
    return RadiusResult(True, best_radius, best_center, len(states))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-vertices", type=int, default=1)
    parser.add_argument("--vertices", type=int, default=7)
    parser.add_argument("--k", type=int, default=3)
    parser.add_argument("--connected-only", action="store_true")
    parser.add_argument("--shard", type=int, default=0)
    parser.add_argument("--shards", type=int, default=1)
    args = parser.parse_args()

    checked = 0
    connected_pairs = 0
    eligible_index = 0
    for graph in nx.graph_atlas_g():
        n = graph.number_of_nodes()
        if n < args.min_vertices or n > args.vertices:
            continue
        if args.connected_only and not nx.is_connected(graph):
            continue
        if eligible_index % args.shards != args.shard:
            eligible_index += 1
            continue
        eligible_index += 1
        graph = nx.convert_node_labels_to_integers(graph)
        low = radius(graph, args.k)
        if not low.connected:
            continue
        high = radius(graph, args.k + 1)
        checked += 1
        if not high.connected:
            continue
        connected_pairs += 1
        print(
            "checked",
            checked,
            "n",
            n,
            "m",
            graph.number_of_edges(),
            "radii",
            low.radius,
            high.radius,
            "states",
            low.states,
            high.states,
            flush=True,
        )
        if low.radius is not None and high.radius is not None and low.radius < high.radius:
            print("COUNTEREXAMPLE graph6", nx.to_graph6_bytes(graph, header=False).decode().strip())
            print("edges", sorted(graph.edges()))
            print("centers", low.center, high.center)
            return
    print("no counterexample", "checked", checked, "connected_pairs", connected_pairs)


if __name__ == "__main__":
    main()
