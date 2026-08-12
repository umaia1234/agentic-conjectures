#!/usr/bin/env python3
"""Regenerate the fixed graph6 input used by the bounded atlas search.

This is a provenance helper, not a CI dependency.  The committed data are
verified by hash without importing NetworkX.
"""

from __future__ import annotations

import argparse
import hashlib
from collections import Counter
from pathlib import Path

try:
    import networkx as nx
except ImportError as exc:  # pragma: no cover - local regeneration only
    raise SystemExit("install the pinned dependency: pip install networkx==3.6.1") from exc


EXPECTED_NETWORKX = "3.6.1"
EXPECTED_SHA256 = "ad68465d32eb7679a1ed8b0aa7a7f1da366da9b1ef8566b04664c504e8876255"
EXPECTED_COUNTS = {1: 1, 2: 2, 3: 4, 4: 11, 5: 34, 6: 156, 7: 1044}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    if nx.__version__ != EXPECTED_NETWORKX:
        raise SystemExit(
            f"expected NetworkX {EXPECTED_NETWORKX}, found {nx.__version__}"
        )

    graphs = [
        graph
        for graph in nx.graph_atlas_g()
        if 1 <= graph.number_of_nodes() <= 7
    ]
    records = [
        nx.to_graph6_bytes(graph, header=False).decode("ascii").strip()
        for graph in graphs
    ]
    counts = Counter(graph.number_of_nodes() for graph in graphs)
    if dict(sorted(counts.items())) != EXPECTED_COUNTS:
        raise AssertionError(f"unexpected order counts: {dict(sorted(counts.items()))}")
    if len(records) != len(set(records)):
        raise AssertionError("the generated graph6 records are not unique")

    payload = ("\n".join(records) + "\n").encode("ascii")
    digest = hashlib.sha256(payload).hexdigest()
    if digest != EXPECTED_SHA256:
        raise AssertionError(f"unexpected dataset SHA-256: {digest}")

    args.output.write_bytes(payload)
    print(
        f"wrote {len(records)} records ({len(payload)} bytes), SHA-256 {digest}"
    )


if __name__ == "__main__":
    main()
