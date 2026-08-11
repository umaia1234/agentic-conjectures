# FormalConjectures upstream snapshot

This directory preserves the exact Lean source used to connect the A245211 work in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A245211](https://oeis.org/A245211)
- Exact commit: `67338a157bbb8d87e9a349d662f82a868bda6327`
- Original path: `FormalConjectures/OEIS/Auto/245211_cbf46b82.lean`
- Immutable upstream file: [245211_cbf46b82.lean](https://github.com/google-deepmind/formal-conjectures/blob/67338a157bbb8d87e9a349d662f82a868bda6327/FormalConjectures/OEIS/Auto/245211_cbf46b82.lean)
- Local snapshot: [245211_cbf46b82.lean](245211_cbf46b82.lean)
- SHA-256: `f3440f0e245abbe548b8e189567bcff5f4e327c7ce7633ec9f2a64d741536610`
- Central declaration(s): `a`; `oeis_245211_conjecture_0`

## Relation to this problem

The upstream theorem states that `21` is the unique positive fixed point. The parent directory proves strong necessary conditions and several complete subfamilies, but explicitly leaves the full conjecture unresolved.

The conjectural declaration still closes with `by sorry`. It is a machine-readable statement of the conjecture, not a formal proof. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjectures.Util.ProblemImports` from the upstream project and is preserved as a non-standalone snapshot. It will not compile merely from this problem directory after the upstream repository is removed; reproducing the original environment requires the matching FormalConjectures project and its Lean/mathlib dependencies.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content remains attributed through the OEIS source link above.
