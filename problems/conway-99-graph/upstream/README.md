# FormalConjectures upstream snapshot

This directory preserves the exact Lean source for Conway's 99-graph problem.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Exact commit: `9118d083ffca1536f521f9a7d103201f537ea670`
- Original path: `FormalConjectures/Wikipedia/Conway99Graph.lean`
- Immutable upstream file: [Conway99Graph.lean](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/Wikipedia/Conway99Graph.lean)
- Local snapshot: [Conway99Graph.lean](Conway99Graph.lean)
- SHA-256: `7f0a5090b0e94bd86003e3630c9dd49af8ce10a7903e6bfd8fe188499e4eae0f`
- Central declaration: `Conway99Graph.conway99Graph`

## Relation to this problem

The declaration asks for a graph on 99 vertices whose edges have one common neighbor and whose nonedges have two. The parent README records the open status and automorphism restrictions but supplies no existence or nonexistence result.

The central declaration closes with `by sorry`. It is a machine-readable statement of the open problem, not a formal proof. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` and is a non-standalone snapshot. It needs the upstream `answer`, `category`, and `AMS` machinery. The central statement uses `SimpleGraph.LocallyLinear` and `SimpleGraph.EdgeDisjointTriangles` from mathlib's `Mathlib/Combinatorics/SimpleGraph/Triangle/Basic.lean`; whole-file examples additionally use `SimpleGraph.cliqueSet` and `SimpleGraph.boxProd`. `Conway99Graph.NonEdgesAreDiagonals` and `Conway99Graph.Conway9` are defined locally in the copied file. The mathlib helper sources are not copied.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt).
