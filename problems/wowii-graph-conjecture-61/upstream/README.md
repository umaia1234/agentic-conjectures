# FormalConjectures upstream snapshot

This directory preserves the exact Lean source for Written on the Wall II graph conjecture 61.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Exact commit: `9118d083ffca1536f521f9a7d103201f537ea670`
- Original path: `FormalConjectures/WrittenOnTheWallII/GraphConjecture61.lean`
- Immutable upstream file: [GraphConjecture61.lean](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/WrittenOnTheWallII/GraphConjecture61.lean)
- Local snapshot: [GraphConjecture61.lean](GraphConjecture61.lean)
- SHA-256: `54620e7b70a9a98eaaf7ce10154f533046b9f6d36fa276c8923c1a7301a7e091`
- Central declaration: `WrittenOnTheWallII.GraphConjecture61.conjecture61`

## Relation to this problem

The declaration is the full inequality for every finite nontrivial connected simple graph. The parent `PROOF.md` establishes several diameter classes, a weaker diameter-four bound, and all trees, but it does not prove the remaining general case or provide a completed Lean proof.

The central declaration closes with `by sorry`. It is the formal statement of the conjecture, not a proof. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` and is a non-standalone snapshot. Two upstream-only FormalConjecturesForMathlib helpers are essential: `SimpleGraph.largestInducedForestSize` from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Induced.lean`, and `SimpleGraph.residue` (built from `SimpleGraph.residueAux` and `SimpleGraph.havelHakimiStep`) from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Residue.lean`. It also uses `SimpleGraph.diam` from mathlib's `Mathlib/Combinatorics/SimpleGraph/Diam.lean`. The helper files are intentionally not copied.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt).
