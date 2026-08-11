# FormalConjectures upstream snapshot

This directory preserves the exact Lean source used to connect the A056777 work in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A056777](https://oeis.org/A056777)
- Exact commit: `9118d083ffca1536f521f9a7d103201f537ea670`
- Original path: `FormalConjectures/OEIS/56777.lean`
- Immutable upstream file: [56777.lean](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/OEIS/56777.lean)
- Local snapshot: [56777.lean](56777.lean)
- SHA-256: `578e8ea54d211c1243dcd37bb8b95470424a4cb5372a056576fa40b30a51e0ed`
- Central declaration(s): `OeisA56777.A`; `OeisA56777.ComesFromPrimeQuadruple`; `OeisA56777.comesFromPrimeQuadruple_of_a`

## Relation to this problem

The upstream file states the full Choudhury–Wei characterization. The parent directory proves a different partial theorem, excluding the case in which `n + 12` is a prime power; that new partial result is not formalized in this snapshot.

The conjectural declaration still closes with `by sorry`. It is a machine-readable statement of the conjecture, not a formal proof. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` from the upstream project and is preserved as a non-standalone snapshot. It will not compile merely from this problem directory after the upstream repository is removed; reproducing the original environment requires the matching FormalConjectures project and its Lean/mathlib dependencies.

## Snapshot choice

The detached `formal-auto-oeis` checkout at commit `67338a157bbb8d87e9a349d662f82a868bda6327` also contains an earlier version of this manual OEIS file at the same path. This directory deliberately keeps the later main-branch version at `9118d083ffca1536f521f9a7d103201f537ea670`, which is the revision audited by the parent problem document; the older duplicate is not copied.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content remains attributed through the OEIS source link above.
