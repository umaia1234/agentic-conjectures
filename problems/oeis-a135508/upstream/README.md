# FormalConjectures upstream snapshot

This directory preserves the exact Lean source used to connect the A135508 work in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A135508](https://oeis.org/A135508)
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/OEIS/135508.lean`
- Immutable upstream file: [135508.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/OEIS/135508.lean)
- Local snapshot: [135508.lean](135508.lean)
- SHA-256: `b835462e33d8f075663ae8f345678ac40b2f4e5bc4cfeeba8d5ea3f68a087b1d`
- Central declaration(s): `OeisA135508.x`; `OeisA135508.a`; `OeisA135508.conjecture`

## Relation to this problem

The upstream theorem `conjecture` states McEachen's conjecture: `a (p - 1) = p` for every prime `p` with `p - 2` not prime. The parent directory does not prove it. [`AgenticConjectures/OeisA135508.lean`](../../../AgenticConjectures/OeisA135508.lean) copies `x` and `a` term for term, restates `conjecture` as `statement : Prop`, and proves partial results: an exact criterion, the cases where `p - 2` has a prime factor below 1009 (all primes `p < 1018083` included), and conditional reductions of the full statement. The upstream test theorems `a_0`–`a_4` are reproduced with the same `rfl` proofs.

The conjectural declaration still closes with `by sorry`. It is a machine-readable statement of the conjecture, not a formal proof. The copied file retains its original copyright and license header.

## Build status

The source uses the Lean module system (`module`, `public import`, `@[expose] public section`) and imports `FormalConjecturesUtil` from the upstream project. It is preserved as a non-standalone snapshot. It will not compile merely from this problem directory after the upstream repository is removed; reproducing the original environment requires the matching FormalConjectures project and its Lean/mathlib dependencies.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content remains attributed through the OEIS source link above.
