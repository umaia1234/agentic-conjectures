# FormalConjectures upstream snapshot

This directory keeps the exact Lean source that links the A110566 refutation in the parent directory to the upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A110566](https://oeis.org/A110566)
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/OEIS/110566.lean`
- Immutable upstream file: [110566.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/OEIS/110566.lean)
- Local snapshot: [110566.lean](110566.lean)
- SHA-256: `be64ecc2912955029a28034fbd04fb3b47fee4ab432dc27456c074e51dbf9309`
- Central declarations: `OeisA110566.a`; `OeisA110566.conjecture`; the value tests `OeisA110566.a_1` … `OeisA110566.a_6`

## Relation to this problem

The upstream theorem `conjecture` states Jianing Song's OEIS conjecture: every odd number occurs in A110566, written `∀ m : ℕ, Odd m → ∃ n > 0, a n = m`. The parent directory refutes exactly this proposition. [`AgenticConjectures/OeisA110566.lean`](../../../AgenticConjectures/OeisA110566.lean) copies `a` and the proposition term for term (as `a` and `statement`) and proves `not_statement : ¬ statement`.

The conjectural declaration still ends with `by sorry`. It is a machine-readable statement of the conjecture, not a formal proof. The copied file keeps its original copyright and license header.

## Build status

The source uses the Lean module system (`module`, `public import FormalConjecturesUtil`, `@[expose] public section`) and the Formal Conjectures `category`/`AMS` attributes. It is kept as a non-standalone snapshot and does not compile from this problem directory alone. Rebuilding it in its original environment needs the matching Formal Conjectures project, which pins Lean/mathlib `v4.33.1`.

## License

The Lean source keeps the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content stays attributed through the OEIS source link above.
