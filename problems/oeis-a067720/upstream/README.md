# FormalConjectures upstream snapshot

This directory preserves the exact Lean source used to connect the A067720 work in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A067720](https://oeis.org/A067720)
- Exact commit: `9118d083ffca1536f521f9a7d103201f537ea670`
- Original path: `FormalConjectures/OEIS/67720.lean`
- Immutable upstream file: [67720.lean](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/OEIS/67720.lean)
- Local snapshot: [67720.lean](67720.lean)
- SHA-256: `7387a319aad73fae84ab7088c5b2af1bca1736755ecc07c6a0d1ce7e47112282`
- Central declaration(s): `OeisA67720.A`; `OeisA67720.prime_add_one_of_a`

## Relation to this problem

The upstream theorem states that every sequence member other than `8` has `k + 1` prime. The parent directory settles only a specified prime-power subfamily, so it does not prove the global Lean statement.

The conjectural declaration still closes with `by sorry`. It is a machine-readable statement of the conjecture, not a formal proof. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` from the upstream project and is preserved as a non-standalone snapshot. It will not compile merely from this problem directory after the upstream repository is removed; reproducing the original environment requires the matching FormalConjectures project and its Lean/mathlib dependencies.

## Snapshot choice

The detached `formal-auto-oeis` checkout at commit `67338a157bbb8d87e9a349d662f82a868bda6327` also contains an earlier version of this manual OEIS file at the same path. This directory deliberately keeps the later main-branch version at `9118d083ffca1536f521f9a7d103201f537ea670`, which is the revision audited by the parent problem document; the older duplicate is not copied.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content remains attributed through the OEIS source link above.
