# FormalConjectures upstream snapshot

This directory preserves the exact Lean source for Frankl's union-closed sets conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Exact commit: `9118d083ffca1536f521f9a7d103201f537ea670`
- Original path: `FormalConjectures/Wikipedia/UnionClosed.lean`
- Immutable upstream file: [UnionClosed.lean](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/Wikipedia/UnionClosed.lean)
- Local snapshot: [UnionClosed.lean](UnionClosed.lean)
- SHA-256: `654961decb9451f33c3042730674430cc1fc4adf71fa101f948f39e2f1207228`
- Central declarations: `UnionClosed.IsUnionClosed`; `UnionClosed.union_closed`; `UnionClosed.union_closed.variants.univ_card`

## Relation to this problem

The main declaration states Frankl's full conjecture, and `variants.univ_card` records the verified ground-set bound of 12 described in the parent README. The parent directory is a status and computation-candidate note; it provides no new proof for ground-set size 13 or for the general conjecture.

The main declaration and the 12-element variant both have `sorry` bodies in this benchmark source. They are formalized statements of mathematical results/status, not proofs contained in this file. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` and is a non-standalone snapshot. It needs the upstream `category` and `AMS` attributes and the matching mathlib finite-set APIs. `UnionClosed.IsUnionClosed` is defined in the copied file; no separate problem-specific helper source is copied.

The frozen FC100 open subset contains the related declaration `UnionClosed.union_closed.variants.cardinality_even_of_union_closed_tight`, not the main Frankl conjecture or its next ground-set case. It is therefore not claimed as exact FC100 membership for this target, and the aggregate subset file is not copied.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt).
