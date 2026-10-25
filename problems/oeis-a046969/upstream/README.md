# FormalConjectures upstream snapshot

This directory preserves the exact Lean source used to connect the A046969 work in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A046969](https://oeis.org/A046969)
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/OEIS/46969.lean`
- Immutable upstream file: [46969.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/OEIS/46969.lean)
- Local snapshot: [46969.lean](46969.lean)
- SHA-256: `a053a37e67334865ccb72372decea7cb247e4c07cb37a97eb0cf118243bfe197`
- Central declaration(s): `OeisA46969.a`; `OeisA46969.conjecture1`; `OeisA46969.conjecture2`

## Relation to this problem

The parent directory proves the upstream theorem `conjecture1` (Conjecture I). The local Lean module [`AgenticConjectures/OeisA046969.lean`](../../../AgenticConjectures/OeisA046969.lean) copies `a` term for term, states `statement` as the universal closure of `conjecture1`, and proves it as `conjecture1_holds`; its theorem `conjecture1` repeats the upstream signature verbatim.

In the snapshot, `conjecture1` still closes with `by sorry` (tagged `research open`). The upstream `conjecture2` (Conjecture II) is tagged `research solved` and refers to an external formal disproof at `n = 236791`; it is out of scope here. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` and uses the upstream module system (`module`, `public import`, `@[expose] public section`, and the `category`/`AMS` attributes). It is preserved as a non-standalone snapshot and will not compile from this problem directory alone; reproducing the original environment requires the matching Formal Conjectures project and its Lean/mathlib dependencies.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content remains attributed through the OEIS source link above.
