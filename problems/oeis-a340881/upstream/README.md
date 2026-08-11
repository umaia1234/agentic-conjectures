# FormalConjectures upstream snapshot

This directory preserves the exact Lean source used to connect the A340881 work in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A340881](https://oeis.org/A340881)
- Exact commit: `67338a157bbb8d87e9a349d662f82a868bda6327`
- Original path: `FormalConjectures/OEIS/Auto/340881_294a5574.lean`
- Immutable upstream file: [340881_294a5574.lean](https://github.com/google-deepmind/formal-conjectures/blob/67338a157bbb8d87e9a349d662f82a868bda6327/FormalConjectures/OEIS/Auto/340881_294a5574.lean)
- Local snapshot: [340881_294a5574.lean](340881_294a5574.lean)
- SHA-256: `e1f4904c4d6b73e0eef6029c09cfd56a60d349dcc5c8809aba663311cc1bcab8`
- Central declaration(s): `a`; `oeis_340881_conjecture_0`

## Relation to this problem

The upstream theorem asserts that `2(p - 1)` is a period modulo each prime `p`; it does not itself formalize minimality or general composite moduli. The parent directory proves a stronger periodicity result, including every modulus, but that proof has not been translated into this Lean snapshot.

The conjectural declaration still closes with `by sorry`. It is a machine-readable statement of the conjecture, not a formal proof. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjectures.Util.ProblemImports` from the upstream project and is preserved as a non-standalone snapshot. It will not compile merely from this problem directory after the upstream repository is removed; reproducing the original environment requires the matching FormalConjectures project and its Lean/mathlib dependencies.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content remains attributed through the OEIS source link above.
