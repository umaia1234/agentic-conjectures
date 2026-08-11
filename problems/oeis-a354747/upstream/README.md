# FormalConjectures upstream snapshot

This directory preserves the exact Lean source used to connect the A354747 work in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A354747](https://oeis.org/A354747)
- Exact commit: `67338a157bbb8d87e9a349d662f82a868bda6327`
- Original path: `FormalConjectures/OEIS/Auto/354747_c4bbc149.lean`
- Immutable upstream file: [354747_c4bbc149.lean](https://github.com/google-deepmind/formal-conjectures/blob/67338a157bbb8d87e9a349d662f82a868bda6327/FormalConjectures/OEIS/Auto/354747_c4bbc149.lean)
- Local snapshot: [354747_c4bbc149.lean](354747_c4bbc149.lean)
- SHA-256: `52cd14fd2fe826e788ce0d3374d2d9f99b8059c908b2ec9dbff3474a7dd1bece`
- Central declaration(s): `a354747`; `oeis_a354747_conjecture_0`

## Relation to this problem

The upstream theorem asks for and states `a354747 100943 = 0`. The parent directory proves instead that the value is `39101`, with deterministic primality and exhaustive minimality certificates, so the upstream statement is false.

The conjectural declaration still closes with `by sorry`. It is a machine-readable statement of the conjecture, not a formal proof. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjectures.Util.ProblemImports` from the upstream project and is preserved as a non-standalone snapshot. It will not compile merely from this problem directory after the upstream repository is removed; reproducing the original environment requires the matching FormalConjectures project and its Lean/mathlib dependencies.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content remains attributed through the OEIS source link above.
