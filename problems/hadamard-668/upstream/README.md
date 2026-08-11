# FormalConjectures upstream snapshot

This directory preserves the exact Lean source containing the order-668 Hadamard problem.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Exact commit: `9118d083ffca1536f521f9a7d103201f537ea670`
- Original path: `FormalConjectures/Wikipedia/Hadamard.lean`
- Immutable upstream file: [Hadamard.lean](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/Wikipedia/Hadamard.lean)
- Local snapshot: [Hadamard.lean](Hadamard.lean)
- SHA-256: `5d93de8bc9aa044c0503dd880b0127d0e7f9465e7f4919e00e93f7b8453e74e1`
- Central declarations: `Hadamard.IsHadamard`; `Hadamard.HadamardConjecture`; `Hadamard.HadamardConjecture.variants.first_cases`; `Hadamard.HadamardConjecture.variants.«167»`

## Relation to this problem

The exact target is `variants.«167»`, which asks for a matrix of order `4 * 167 = 668`. The parent README surveys the current status and structured Legendre-pair search only; it supplies no order-668 matrix or nonexistence proof.

The order-668 declaration closes with `by sorry`. It is an open-problem statement, not a formal proof. Other solved/test declarations in the same benchmark file can also use `sorry`, so their labels should not be read as proof terms. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` and is a non-standalone snapshot. It needs the upstream `category` and `AMS` attributes and matching mathlib matrix, determinant, and real-number APIs. `Hadamard.IsHadamard`, `Hadamard.IsHadamard'`, and `Hadamard.H12` are defined in the copied file; no separate problem-specific helper source is copied.

The frozen FC100 solved subset contains `Hadamard.HadamardConjecture.variants.first_cases`, the result for `k ≤ 166`, not the open `variants.«167»` target. It is therefore only an adjacent predecessor and not exact FC100 membership for order 668; the aggregate file is not copied.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt).
