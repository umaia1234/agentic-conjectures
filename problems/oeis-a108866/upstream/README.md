# FormalConjectures upstream snapshot

This directory keeps the exact Lean source that links the A108866 work in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A108866](https://oeis.org/A108866)
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/OEIS/108866.lean`
- Immutable upstream file: [108866.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/OEIS/108866.lean)
- Local snapshot: [108866.lean](108866.lean)
- SHA-256: `9b6abdf05b5158b21a83c09ea59ab6b47c3c9375f81c9c8d161503af2eabd464`
- Central declaration(s): `OeisA108866.a`; `OeisA108866.ratExpression`; `OeisA108866.conjecture`

## Relation to this problem

The upstream theorem `conjecture` states Thomas Ordowski's conjecture: for every `n > 3`, `n^2` divides `(ratExpression n).num` if and only if `n` is prime. [`AgenticConjectures/OeisA108866.lean`](../../../AgenticConjectures/OeisA108866.lean) copies `a` and `ratExpression` term for term. It records `conjecture` as the proposition `statement`, with the hypothesis `n > 3` moved under a universal quantifier. It proves the prime direction (`prime_imp`) and the composite direction for several families of composite `n`. The full equivalence is not proved; see the [parent README](../README.md).

The upstream declaration still ends in `by sorry`. It is a machine-readable statement of the conjecture, not a formal proof. The copied file keeps its original copyright and license header.

## Build status

The source uses the `module` system and `public import FormalConjecturesUtil` from the upstream project, so this directory keeps it as a non-standalone snapshot. Once the upstream repository is gone, it will not compile from this problem directory alone. Reproducing the original environment requires the matching FormalConjectures project and its Lean/mathlib dependencies. Its test lemmas `a_0`–`a_4` are not copied into this repository's module.

## License

The Lean source keeps the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content remains attributed through the OEIS source link above.
