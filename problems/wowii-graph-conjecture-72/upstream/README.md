# FormalConjectures upstream snapshot

This directory preserves the exact Lean source for Written on the Wall II graph conjecture 72.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Source list: [E. DeLaViña, Written on the Wall II](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/WrittenOnTheWallII/GraphConjecture72.lean`
- Immutable upstream file: [GraphConjecture72.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/WrittenOnTheWallII/GraphConjecture72.lean)
- Local snapshot: [GraphConjecture72.lean](GraphConjecture72.lean)
- SHA-256: `1568fb0e24d6e46753afa7514c3355911a7f0887fc4f1fa2f581a93c81832d4f`
- Central declaration: `WrittenOnTheWallII.GraphConjecture72.conjecture72`

## Relation to this problem

The declaration reads the source row as ⌈A + L/3⌉ ≤ tree(G), dividing only the maximum local independence number by 3, for every finite connected simple graph on at least two vertices (`[Nontrivial α]`). The parent directory refutes exactly this declaration in [`AgenticConjectures/WowiiGraphConjecture72.lean`](../../../AgenticConjectures/WowiiGraphConjecture72.lean) with a connected graph on 28 vertices, and [`upstream_statement_check.lean`](../upstream_statement_check.lean) derives the negation of the upstream theorem text, over the upstream definitions, from that refutation. The other reading of the row, ⌈(A + L)/3⌉ ≤ tree(G), is not refuted; see the parent [README](../README.md#two-readings).

In the snapshot, the central declaration still closes with `by sorry` and carries `@[category research open, AMS 5]`. It is the formal statement of the conjecture, not a proof. The file and the three helper files below are unchanged at `main` commit `37f0808b83c56c8cef4ea5816b8329c09b8905a8` (2026-10-24): their Git blob hashes there equal those at the snapshot commit. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` and is a non-standalone snapshot. Three upstream-only FormalConjecturesForMathlib helpers are essential: `SimpleGraph.averageEccentricity` from [`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Eccentricity.lean`](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Eccentricity.lean#L34), `SimpleGraph.largestInducedTreeSize` from [`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/LargestInducedTree.lean`](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/LargestInducedTree.lean#L39), and `SimpleGraph.indepNeighborsCard` from [`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Independence.lean`](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Independence.lean#L40). It also uses mathlib's `SimpleGraph.eccent`, `SimpleGraph.IsTree` and `SimpleGraph.indepNum`. The helper files are intentionally not copied; the three definitions are reproduced term for term in the checked module and in `upstream_statement_check.lean`.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt).
