# FormalConjectures upstream snapshot

This directory preserves the exact Lean source used to connect the A076141 work in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A076141](https://oeis.org/A076141)
- Exact commit: `67338a157bbb8d87e9a349d662f82a868bda6327`
- Original path: `FormalConjectures/OEIS/Auto/76141_34382c19.lean`
- Immutable upstream file: [76141_34382c19.lean](https://github.com/google-deepmind/formal-conjectures/blob/67338a157bbb8d87e9a349d662f82a868bda6327/FormalConjectures/OEIS/Auto/76141_34382c19.lean)
- Local snapshot: [76141_34382c19.lean](76141_34382c19.lean)
- SHA-256: `c2001f87cfa7dd6a3aefc8ba8345d4ba7a4f2c8684213362ecacd27c5494be37`
- Central declaration(s): `binary_pattern_nat`; `a`; `oeis_a076141_conjecture`

## Relation to this problem

The upstream theorem is universal over all natural numbers. The parent directory gives an exact finite verification through `n < 2^40`; this is evidence for, not a proof of, that universal statement.

The conjectural declaration still closes with `by sorry`. It is a machine-readable statement of the conjecture, not a formal proof. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjectures.Util.ProblemImports` from the upstream project and is preserved as a non-standalone snapshot. It will not compile merely from this problem directory after the upstream repository is removed; reproducing the original environment requires the matching FormalConjectures project and its Lean/mathlib dependencies.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content remains attributed through the OEIS source link above.
