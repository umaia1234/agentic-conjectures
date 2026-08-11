# FormalConjectures upstream snapshot

This directory preserves the exact Lean source used to connect the A297707 work in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A297707](https://oeis.org/A297707)
- Exact commit: `67338a157bbb8d87e9a349d662f82a868bda6327`
- Original path: `FormalConjectures/OEIS/Auto/297707_fd3973db.lean`
- Immutable upstream file: [297707_fd3973db.lean](https://github.com/google-deepmind/formal-conjectures/blob/67338a157bbb8d87e9a349d662f82a868bda6327/FormalConjectures/OEIS/Auto/297707_fd3973db.lean)
- Local snapshot: [297707_fd3973db.lean](297707_fd3973db.lean)
- SHA-256: `f07f543027f89b28371533df04b9e34a7c3e08bea8331e651cef364b666b97bf`
- Central declaration(s): `A297707`; `Nat.prevPrime`; `oeis_297707_conjecture_0`

## Relation to this problem

The upstream theorem states only that any index producing a composite previous-prime gap is greater than `250`. The parent directory contains an experimental probable-prime search; it does not supply a formal proof of that bound or a certified answer to the least-index question.

The conjectural declaration still closes with `by sorry`. It is a machine-readable statement of the conjecture, not a formal proof. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjectures.Util.ProblemImports` from the upstream project and is preserved as a non-standalone snapshot. It will not compile merely from this problem directory after the upstream repository is removed; reproducing the original environment requires the matching FormalConjectures project and its Lean/mathlib dependencies.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content remains attributed through the OEIS source link above.
