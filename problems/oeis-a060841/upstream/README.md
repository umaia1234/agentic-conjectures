# FormalConjectures upstream snapshot

This directory preserves the exact Lean source used to connect the A060841 work in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A060841](https://oeis.org/A060841)
- Exact commit: `67338a157bbb8d87e9a349d662f82a868bda6327`
- Original path: `FormalConjectures/OEIS/Auto/60841_4cba886e.lean`
- Immutable upstream file: [60841_4cba886e.lean](https://github.com/google-deepmind/formal-conjectures/blob/67338a157bbb8d87e9a349d662f82a868bda6327/FormalConjectures/OEIS/Auto/60841_4cba886e.lean)
- Local snapshot: [60841_4cba886e.lean](60841_4cba886e.lean)
- SHA-256: `31b238c9ac5eb60b785cdd1c81d490d34d148f504966b2d9c0b7f6a0a001aea1`
- Central declaration(s): `A060841`; `A060841_val_rat`; `oeis_60841_conjecture_0`

## Relation to this problem

The upstream theorem conjoins the claimed power-of-two denominator property with the integrality classification. The parent directory proves the classification but gives the rigorous counterexample `n = 1807` to the denominator claim, so the upstream conjunction is false as stated.

The conjectural declaration still closes with `by sorry`. It is a machine-readable statement of the conjecture, not a formal proof. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjectures.Util.ProblemImports` from the upstream project and is preserved as a non-standalone snapshot. It will not compile merely from this problem directory after the upstream repository is removed; reproducing the original environment requires the matching FormalConjectures project and its Lean/mathlib dependencies.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content remains attributed through the OEIS source link above.
