# FormalConjectures upstream snapshot

This directory preserves the exact Lean sources used to connect the A007406 work in the parent directory to its upstream formalized conjecture. The conjecture file imports a second upstream file (A089026), so both are kept.

## Provenance

### `7406.lean` (the conjecture)

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A007406](https://oeis.org/A007406)
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/OEIS/7406.lean`
- Immutable upstream file: [7406.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/OEIS/7406.lean)
- Local snapshot: [7406.lean](7406.lean)
- SHA-256: `6b8101561979aac0a9f110530c68c296eb5c5a7177ea56d0680d4455f2fc3af1`
- Central declaration(s): `OeisA7406.a`; `OeisA7406.conjecture`; test values `OeisA7406.a_0` … `OeisA7406.a_4`

### `89026.lean` (the right-hand side of the conjecture)

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A089026](https://oeis.org/A089026)
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/OEIS/89026.lean`
- Immutable upstream file: [89026.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/OEIS/89026.lean)
- Local snapshot: [89026.lean](89026.lean)
- SHA-256: `179710a0172b7c236759855fe92c88eab990a5114cd15d7c6ffeeb007457c304`
- Central declaration(s): `OeisA89026.a`; test values `OeisA89026.a_0` … `OeisA89026.a_5`

## Relation to this problem

`OeisA7406.conjecture` states that `Nat.gcd n (a (n - 1)) = OeisA89026.a n` for every `n > 3`. The parent directory's Lean module `AgenticConjectures.OeisA007406` copies `OeisA7406.a` term for term as `a`, copies `OeisA89026.a` term for term under the name `a089026`, and records the conjecture as `statement`. It proves the prime half, the `2`-, `3`- and `5`-parts, an equivalent reformulation and several infinite families, but not the conjecture itself; a computational certificate extends the check to all `n` up to a bound (see the parent README).

The conjectural declaration still closes with `by sorry`. It is a machine-readable statement of the conjecture, not a formal proof. The upstream test lemmas use `decide +native`, which this repository does not allow; the corresponding values are proved there without it. The copied files retain their original copyright and license header.

## Build status

The sources import `FormalConjecturesUtil` (and `7406.lean` imports `FormalConjectures.OEIS.«89026»`) from the upstream project and are preserved as non-standalone snapshots. They will not compile merely from this problem directory after the upstream repository is removed; reproducing the original environment requires the matching FormalConjectures project and its Lean/mathlib dependencies.

## License

The Lean sources retain the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content remains attributed through the OEIS source links above.
