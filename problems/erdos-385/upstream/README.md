# FormalConjectures upstream snapshot

This directory preserves the exact Lean source for Erdős problem #385.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Exact commit: `9118d083ffca1536f521f9a7d103201f537ea670`
- Original path: `FormalConjectures/ErdosProblems/385.lean`
- Immutable upstream file: [385.lean](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/ErdosProblems/385.lean)
- Local snapshot: [385.lean](385.lean)
- SHA-256: `0fef1d5f4db7911c905d14f3cf6fe6c23c236201e3edb4784dec5dbfd8fc0f3c`
- Central declarations: `Erdos385.F`; `Erdos385.erdos_385.parts.i`; `Erdos385.erdos_385.parts.ii`; `Erdos385.erdos_385.variants.lb`

## Relation to this problem

The upstream parts ask whether `F(n) > n` eventually and whether `F(n) - n → ∞`. The parent C++ programs inspect those quantities over finite ranges only. Their historical `ep430_*` basenames do not indicate a separate `430.lean`; no such upstream source file exists.

All three research declarations contain `sorry`; the proved `trivial_ub` is only an elementary upper bound. This file states the open problems but does not solve them. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` and is a non-standalone snapshot. It needs the upstream `answer`, `category`, and `AMS` machinery. In particular, `Nat.Composite` comes from the uncopied `FormalConjecturesForMathlib/Data/Nat/Prime/Composite.lean`; `Nat.minFac` and the natural-square-root API come from matching mathlib sources. Filters, asymptotics, and real square roots are also supplied by mathlib.

## FC100 benchmark provenance

The immutable `bench-v1-lean4.27.0` snapshot at commit `7a41db3d761324599812d6ca6cb6a9f311046dc7` includes exactly `Erdos385.erdos_385.parts.ii` in [`FormalConjectures/Subsets/FC100OpenSet1.lean`](https://github.com/google-deepmind/formal-conjectures/blob/7a41db3d761324599812d6ca6cb6a9f311046dc7/FormalConjectures/Subsets/FC100OpenSet1.lean). The aggregate is not copied, and that membership does not by itself include parts (i) or the lower-bound variant.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt).
