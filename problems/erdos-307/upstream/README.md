# FormalConjectures upstream snapshot

This directory preserves the exact Lean source for Erdős problem #307.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Exact commit: `9118d083ffca1536f521f9a7d103201f537ea670`
- Original path: `FormalConjectures/ErdosProblems/307.lean`
- Immutable upstream file: [307.lean](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/ErdosProblems/307.lean)
- Local snapshot: [307.lean](307.lean)
- SHA-256: `840a39903e713a528a624f8db66312c74c96262764d8bd51cdc6776978bce77d`
- Central declarations: `Erdos307.erdos_307`; `Erdos307.erdos_307.variants.coprime`; `Erdos307.erdos_307.variants.coprime_one_notMem`; `Erdos307.erdos_307.barrier`

## Relation to this problem

The main declaration is the same prime-set reciprocal-product question audited in the parent directory. The local arguments and exact enumerations establish necessary conditions and finite exclusions, including `|P ∪ Q| ≥ 60`; they do not produce prime sets or prove nonexistence. The later upstream `barrier` declaration records a weaker machine-checked lower barrier and links to its separate proof repository.

The open declarations and the local copy of `barrier` have `sorry` bodies. They are benchmark statements and proof-location metadata, not proofs contained in this file. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` and is a non-standalone snapshot. It needs the upstream `answer`, `category`, `AMS`, and `formal_proof` machinery plus the matching mathlib `Finset`, prime, and rational-arithmetic APIs. No problem-specific companion helper file is copied.

## FC100 benchmark provenance

The immutable `bench-v1-lean4.27.0` snapshot at commit `7a41db3d761324599812d6ca6cb6a9f311046dc7` includes exactly `Erdos307.erdos_307` in [`FormalConjectures/Subsets/FC100OpenSet1.lean`](https://github.com/google-deepmind/formal-conjectures/blob/7a41db3d761324599812d6ca6cb6a9f311046dc7/FormalConjectures/Subsets/FC100OpenSet1.lean). The 100-problem aggregate is provenance only and is not copied here.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt).
