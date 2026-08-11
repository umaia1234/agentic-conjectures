# FormalConjectures upstream snapshot

This directory preserves the exact Lean source used to connect the A000224 work in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A000224](https://oeis.org/A000224)
- Exact commit: `67338a157bbb8d87e9a349d662f82a868bda6327`
- Original path: `FormalConjectures/OEIS/Auto/224_2322a58c.lean`
- Immutable upstream file: [224_2322a58c.lean](https://github.com/google-deepmind/formal-conjectures/blob/67338a157bbb8d87e9a349d662f82a868bda6327/FormalConjectures/OEIS/Auto/224_2322a58c.lean)
- Local snapshot: [224_2322a58c.lean](224_2322a58c.lean)
- SHA-256: `fc836bc0d378c9f32dca114f03fca32eca0234b68cad05d8718327501f27e4f4`
- Central declaration(s): `A000224`; `oeis_a000224_conjecture_ordowski`

## Relation to this problem

The upstream theorem states the full odd-prime equivalence. The parent directory proves only the even, odd-prime-power, and distinct-two-prime composite cases and records bounded searches, so it does not prove the universal Lean statement.

The conjectural declaration still closes with `by sorry`. It is a machine-readable statement of the conjecture, not a formal proof. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjectures.Util.ProblemImports` from the upstream project and is preserved as a non-standalone snapshot. It will not compile merely from this problem directory after the upstream repository is removed; reproducing the original environment requires the matching FormalConjectures project and its Lean/mathlib dependencies.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content remains attributed through the OEIS source link above.
