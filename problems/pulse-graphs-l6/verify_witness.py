#!/usr/bin/env python3
"""Independent exact verifier for the period-17 Pulse Graph witness."""

import json
from pathlib import Path


HERE = Path(__file__).resolve().parent


def pulse_update(state, n, arcs):
    """Apply the paper's synchronous prime-active-in-neighbor rule."""
    result = 0
    counts = []
    for v in range(n):
        active_inputs = sum((state >> u) & 1 for u, w in arcs if w == v)
        counts.append(active_inputs)
        if active_inputs in (2, 3, 5):
            result |= 1 << v
    return result, counts


def maximum_period(n, arcs):
    """Find every cycle in the witness's exact 2^n-state functional graph."""
    successor = [pulse_update(s, n, arcs)[0] for s in range(1 << n)]
    processed = set()
    maximum = 0
    cycles = []
    for start in range(1 << n):
        if start in processed:
            continue
        position = {}
        path = []
        state = start
        while state not in processed and state not in position:
            position[state] = len(path)
            path.append(state)
            state = successor[state]
        if state in position:
            cycle = path[position[state]:]
            cycles.append(cycle)
            maximum = max(maximum, len(cycle))
        processed.update(path)
    return maximum, cycles


def main():
    data = json.loads((HERE / "witness.json").read_text(encoding="utf-8"))
    n = data["n"]
    arcs = [tuple(edge) for edge in data["arcs"]]
    cycle = data["cycle"]

    assert n == 6
    assert len(arcs) == 21
    assert len(set(arcs)) == len(arcs)
    assert all(0 <= u < n and 0 <= v < n and u != v for u, v in arcs)

    out_masks = [sum(1 << v for u, v in arcs if u == source) for source in range(n)]
    in_masks = [sum(1 << u for u, v in arcs if v == target) for target in range(n)]
    assert out_masks == data["out_neighbor_masks"]
    assert in_masks == data["in_neighbor_masks"]

    assert len(cycle) == data["period"] == 17
    assert len(set(cycle)) == len(cycle)
    transitions = []
    for i, state in enumerate(cycle):
        expected = cycle[(i + 1) % len(cycle)]
        actual, counts = pulse_update(state, n, arcs)
        assert actual == expected, (state, expected, actual, counts)
        transitions.append((state, actual, counts))

    witness_maximum, cycles = maximum_period(n, arcs)
    assert witness_maximum == 17

    print("PASS witness")
    print(f"n={n} arcs={len(arcs)} period={len(cycle)} witness_graph_max={witness_maximum}")
    print("cycle=" + ",".join(map(str, cycle)))
    for state, target, counts in transitions:
        print(f"{state:02d} ({state:06b}) -> {target:02d} ({target:06b}); in-counts={counts}")
    print("all_cycle_lengths=" + ",".join(map(str, sorted(map(len, cycles)))))


if __name__ == "__main__":
    main()
