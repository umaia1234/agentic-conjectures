# FormalConjectures upstream snapshot

This directory preserves the exact Lean source of the upstream statement of Colton's conjecture
that the parent directory proves.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A111291](https://oeis.org/A111291)
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/OEIS/111291.lean`
- Immutable upstream file: [111291.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/OEIS/111291.lean)
- Local snapshot: [111291.lean](111291.lean)
- SHA-256: `fab5203877e5724a7f2bbfbb681f79e1c93d4d68628dc31dbdc2686f255bf9cf`
- Central declaration(s): `OeisA111291.countRefactorableNat`; `OeisA111291.a`; `OeisA111291.countRefactorable`; `OeisA111291.colton_conjecture`

## Relation to this problem

`colton_conjecture` states `∀ n : ℕ, Nat.primeCounting n ≤ 2 * countRefactorableNat n` and is
marked `research open`; this is the proposition of
`AgenticConjectures.OeisA111291.statement`. The definitions `countRefactorableNat`, `a` and
`countRefactorable` and the tests `a_0`, `a_1`, `a_2` are copied term for term into
[`AgenticConjectures/OeisA111291.lean`](../../../AgenticConjectures/OeisA111291.lean). The
parent directory gives a computer-assisted proof of the proposition; it is not a Lean proof.

The file also states the eventual form `conjecture` (count $\ge x/(2\log x)$ for large $x$,
marked `research solved`), which is not part of this problem, and proves small cases with
`native_decide`, which this repository does not use.

The research declarations still close with `by sorry`. They are machine-readable statements, not
formal proofs. The copied file retains its original copyright and license header.

## Build status

The source starts with a `module` header and imports `FormalConjecturesUtil` from the upstream
project, so it is preserved as a non-standalone snapshot. It does not compile from this problem
directory; reproducing the original environment requires the matching FormalConjectures project
and its Lean/mathlib dependencies.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content remains attributed through the OEIS source link above.
