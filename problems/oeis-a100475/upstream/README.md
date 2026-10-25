# FormalConjectures upstream snapshot

This directory preserves the exact Lean source used to connect the A100475 work in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A100475](https://oeis.org/A100475)
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/OEIS/100475.lean`
- Immutable upstream file: [100475.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/OEIS/100475.lean)
- Local snapshot: [100475.lean](100475.lean)
- SHA-256: `9fa2e0e887d0d8e5b8c3043aded923135cf6e0056100e5223d0155557845983a`
- Central declaration(s): `OeisA100475.reverseDigits`; `OeisA100475.aStartAt`; `OeisA100475.IsUltimatelyPeriodic`; `OeisA100475.conjecture`

## Relation to this problem

The upstream theorem `conjecture` asserts `∃ x : ℕ, 0 < x ∧ x ≠ 1 ∧ IsUltimatelyPeriodic (aStartAt x)`, i.e. that some positive start other than `1` eventually loops. [`AgenticConjectures/OeisA100475.lean`](../../../AgenticConjectures/OeisA100475.lean) copies `reverseDigits`, `a`, `aStartAt` and `IsUltimatelyPeriodic` term for term, records the proposition as `statement`, and proves `not_statement : ¬ statement`. It also proves the stronger `not_isUltimatelyPeriodic`, which covers every start `x > 0`, including `x = 1`. The upstream theorem `conjecture_with_zero` (the start `0` is constant) is unaffected.

The upstream `conjecture` still closes with `by sorry`. It is a machine-readable statement of the question, not a formal proof. The copied file retains its original copyright and license header.

## Build status

The source starts with `module` and `public import FormalConjecturesUtil` from the upstream project and is preserved as a non-standalone snapshot. It will not compile merely from this problem directory after the upstream repository is removed; reproducing the original environment requires the matching FormalConjectures project and its Lean/mathlib dependencies.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content remains attributed through the OEIS source link above.
