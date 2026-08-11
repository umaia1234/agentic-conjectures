# FormalConjectures upstream snapshot

This directory preserves the exact Lean source used to connect the A190363 work in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A190363](https://oeis.org/A190363)
- Exact commit: `67338a157bbb8d87e9a349d662f82a868bda6327`
- Original path: `FormalConjectures/OEIS/Auto/190363_e4edee15.lean`
- Immutable upstream file: [190363_e4edee15.lean](https://github.com/google-deepmind/formal-conjectures/blob/67338a157bbb8d87e9a349d662f82a868bda6327/FormalConjectures/OEIS/Auto/190363_e4edee15.lean)
- Local snapshot: [190363_e4edee15.lean](190363_e4edee15.lean)
- SHA-256: `b74e4e0f67f521adf22cd1d3cb148e8308a88e1f5d35a552127d06ed87d3cd73`
- Central declaration(s): `a`; `A190363_LR`; `oeis_190363_conjecture_0`

## Relation to this problem

The upstream theorem states the proposed order-21 recurrence. The parent directory gives its first failure at recurrence index `140` and an infinite Pell-generated counterexample family, so the upstream statement is false.

The conjectural declaration still closes with `by sorry`. It is a machine-readable statement of the conjecture, not a formal proof. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjectures.Util.ProblemImports` from the upstream project and is preserved as a non-standalone snapshot. It will not compile merely from this problem directory after the upstream repository is removed; reproducing the original environment requires the matching FormalConjectures project and its Lean/mathlib dependencies.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content remains attributed through the OEIS source link above.
