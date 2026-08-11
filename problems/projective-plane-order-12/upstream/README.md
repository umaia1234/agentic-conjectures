# FormalConjectures upstream snapshot

This directory preserves the exact Lean source containing the finite projective-plane problem of order 12.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Exact commit: `9118d083ffca1536f521f9a7d103201f537ea670`
- Original path: `FormalConjectures/ErdosProblems/723.lean`
- Immutable upstream file: [723.lean](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/ErdosProblems/723.lean)
- Local snapshot: [723.lean](723.lean)
- SHA-256: `57d2a9c701808324dbb207ed10d764059cef77584270bb097d8c810e6c83010f`
- Central declarations: `Erdos723.erdos_723`; `Erdos723.erdos_723.variants.leq_11`; `Erdos723.erdos_723.variants.eq_12`

## Relation to this problem

The exact target is `variants.eq_12`, asserting the existence question for a projective plane whose order is 12. The parent README records the open status and restrictions on possible collineation groups but gives no construction or nonexistence proof.

The order-12 declaration closes with `by sorry`; the recorded `≤ 11` result also has a `sorry` body in this benchmark source. These are machine-readable statements, not proofs contained in the copied file. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` and is a non-standalone snapshot. It needs the upstream `answer`, `category`, and `AMS` machinery. The crucial mathlib helpers are `Configuration.ProjectivePlane` and `Configuration.ProjectivePlane.order` from `Mathlib/Combinatorics/Configuration.lean`, plus `IsPrimePow` from `Mathlib/Algebra/IsPrimePow.lean`. Those library sources are not copied.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt).
