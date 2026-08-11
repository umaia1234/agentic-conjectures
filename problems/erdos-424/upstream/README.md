# FormalConjectures upstream snapshot

This directory preserves the exact Lean source for Erdős problem #424.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Exact commit: `9118d083ffca1536f521f9a7d103201f537ea670`
- Original path: `FormalConjectures/ErdosProblems/424.lean`
- Immutable upstream file: [424.lean](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/ErdosProblems/424.lean)
- Local snapshot: [424.lean](424.lean)
- SHA-256: `05876ee2a0d7e75f72af414dbb6c415212cfa04ef3941dfbd5d9f7c87e6a30d9`
- Central declarations: `Erdos424.nextGeneration`; `Erdos424.sequenceSet`; `Erdos424.generatedSet`; `Erdos424.erdos_424`

## Relation to this problem

The declaration asks whether the generated set has positive density. The parent program performs an exact finite generation and residue-class probe, so it does not establish positive density.

The central conjecture closes with `by sorry`. It is a machine-readable statement, not a proof. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` and is a non-standalone snapshot. It needs the upstream `answer`, `category`, and `AMS` machinery. In particular, `Set.HasPosDensity` comes from `FormalConjecturesForMathlib/Data/Set/Density.lean`; that helper file is intentionally not copied.

The byte-identical upstream alias `FormalConjectures/GreensOpenProblems/63.lean` only imports this canonical file and records that Ben Green's problem 63 is the same question. It is retained here as provenance in this note, not as another copied source.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt).
