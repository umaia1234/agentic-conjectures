# FormalConjectures upstream snapshot

This directory preserves the exact Lean source that states the Catch-Up conjecture studied in the parent directory.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Paper source: A. Isaksen, M. Ismail, S. J. Brams, A. Nealen, *Catch-Up: A Game in Which the Lead Alternates*, Game & Puzzle Design 1(2), 38–49 (2015); [MPRA preprint 108784](https://mpra.ub.uni-muenchen.de/108784/)
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/Paper/CatchUpConjecture.lean`
- Immutable upstream file: [CatchUpConjecture.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/Paper/CatchUpConjecture.lean)
- Local snapshot: [CatchUpConjecture.lean](CatchUpConjecture.lean)
- SHA-256: `53b9153986d279c1512993a9d3ffe80ff8c53233f59a82998dea36326e0f2790`
- Central declaration(s): `CatchUp.valueAux`; `CatchUp.value`; `CatchUp.value_of_even_mul_succ_self_div_two`

## Relation to this problem

The upstream theorem `value_of_even_mul_succ_self_div_two` states that Catch-Up on `{1, …, N}` is a draw whenever `N(N+1)/2` is even, and it closes with `by sorry`: it is a machine-readable statement of the open conjecture, not a proof. [`AgenticConjectures/CatchUpGame.lean`](../../../AgenticConjectures/CatchUpGame.lean) copies the definitions `Player` through `value` verbatim (checked byte for byte by [`check_upstream_copy.py`](../check_upstream_copy.py)), restates the theorem as `def statement : Prop`, and proves it for `N ≤ 10` together with lemmas about `valueAux`. The parent directory adds exact values for `N ≤ 28`, computed outside Lean.

## Build status

The source uses `module`, `public import FormalConjecturesUtil` and `@[expose] public section` from the upstream project and is preserved as a non-standalone snapshot. It does not compile from this directory; reproducing the original environment requires the matching FormalConjectures project and its Lean/mathlib dependencies. The adapted copy in `AgenticConjectures/CatchUpGame.lean` builds with this repository's mathlib.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt).
