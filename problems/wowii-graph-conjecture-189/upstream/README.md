# FormalConjectures upstream snapshot

This directory preserves the exact Lean source for Written on the Wall II graph conjecture 189.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/WrittenOnTheWallII/GraphConjecture189.lean`
- Immutable upstream file: [GraphConjecture189.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/WrittenOnTheWallII/GraphConjecture189.lean)
- Local snapshot: [GraphConjecture189.lean](GraphConjecture189.lean)
- SHA-256: `45121063d4d0e1045b51625b09a70bfdc91ff92f905f0d9acab92a657147ef6b`
- Central declaration: `WrittenOnTheWallII.GraphConjecture189.conjecture189`

## Relation to this problem

The declaration states the full conjecture for every finite nontrivial connected simple graph.
`AgenticConjectures.WowiiGraphConjecture189.statement` is its universal closure, with the three
upstream helper definitions copied term for term (see the module docstring for the exact
correspondence). The parent [README](../README.md) proves the diameter-at-most-two case and the
bounds behind the computer search in Lean, and reports exhaustive searches; it does not prove the
general statement.

The central declaration closes with `by sorry`. It is the formal statement of the conjecture, not
a proof. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` and is a non-standalone snapshot. Two upstream-only
FormalConjecturesForMathlib helpers are essential: `SimpleGraph.distEven` from
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean`, and
`SimpleGraph.secondSmallestDegree` (built from `SimpleGraph.degreeSequence`) from
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Degrees.lean`. It also uses
`SimpleGraph.Walk.IsHamiltonian` from mathlib. The helper files are intentionally not copied;
their three definitions are reproduced in `AgenticConjectures/WowiiGraphConjecture189.lean`.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt).
