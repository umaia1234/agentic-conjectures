# FormalConjectures upstream snapshot

This directory preserves the exact Lean source for the formalized Chvátal downset conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Exact commit: `9118d083ffca1536f521f9a7d103201f537ea670`
- Original path: `FormalConjectures/Paper/Chvatal.lean`
- Immutable upstream file: [Chvatal.lean](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/Paper/Chvatal.lean)
- Local snapshot: [Chvatal.lean](Chvatal.lean)
- SHA-256: `7e1c593f9e6644ed879738a4f2bf083ce81e2e8d5d6cf2c42f23c5d9e53791b9`
- Central declaration: `Chvatal.exists_maximal_star`

## Relation to this problem

The declaration states the full conjecture for every finite decreasing family. The parent directory records a saturation reduction and bounded SAT/MILP experiments only; it neither proves a new ground-set case nor proves the global declaration.

The central declaration has a `sorry` body. This is a machine-readable conjecture statement, not an upstream formal proof. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` and is a non-standalone snapshot. The upstream utility layer supplies the `category` and `AMS` attributes and the matching Lean/mathlib environment. The problem-specific helpers `Chvatal.Decreasing` and `Chvatal.Intersecting` are defined in the copied file itself; no separate helper source is copied.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt).
