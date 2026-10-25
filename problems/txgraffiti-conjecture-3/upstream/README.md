# FormalConjectures upstream snapshot

This directory preserves the exact Lean source for TxGraffiti Conjecture 3 of arXiv:2507.17780.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/Arxiv/2507.17780/3.lean`
- Immutable upstream file: [3.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/Arxiv/2507.17780/3.lean)
- Local snapshot: [3.lean](3.lean)
- SHA-256: `eff8af26bb8b4ad030e16faa42fb3e1f15bd9ffe23de68bd281b064794689a95`
- Central declaration: `Arxiv.«2507.17780».tx_graffiti_conjecture_3`

## Relation to this problem

The declaration states the conjecture for every finite simple graph that is `r`-regular with
`r ≥ 1`. `AgenticConjectures.TxGraffitiConjecture3.statement` is its universal closure, with the
upstream helper definitions copied term for term (see the module docstring for the exact
correspondence). The parent [README](../README.md) refutes it, given a lower bound that a
CI-checked DRAT certificate establishes. The cubic counterexample it uses was already public.

The central declaration closes with `by sorry` and is tagged `research open` at this commit. It
is the formal statement of the conjecture, not a proof. The copied file retains its original
copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` and is a non-standalone snapshot. It relies on
upstream-only FormalConjecturesForMathlib helpers: `SimpleGraph.indepDominationNumber` (with
`IsNIndepDominatingSet` and `IsDominating`) from
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Domination.lean`,
`SimpleGraph.saturationNumber` from `.../SimpleGraph/Saturation.lean`, and
`IsMaximalEdgeMatching` (with `IsEdgeMatching`) from `.../SimpleGraph/Matching.lean`. The helper
files are intentionally not copied; the definitions are reproduced in
`AgenticConjectures/TxGraffitiConjecture3.lean`.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt).
