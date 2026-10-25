# FormalConjectures upstream snapshot

This directory preserves the exact Lean source for Written on the Wall II graph conjecture 96.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Source list: [E. DeLaViña, Written on the Wall II](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/WrittenOnTheWallII/GraphConjecture96.lean`
- Immutable upstream file: [GraphConjecture96.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/WrittenOnTheWallII/GraphConjecture96.lean)
- Local snapshot: [GraphConjecture96.lean](GraphConjecture96.lean)
- SHA-256: `8d5ec6576f17d23d3c6f0cea448e8505697648e3a892bfb5a47d0efc928434ae`
- Central declaration: `WrittenOnTheWallII.GraphConjecture96.conjecture96`

## Relation to this problem

The declaration states the inequality for every finite connected simple graph on at least two vertices (`[Nontrivial α]`). Its docstring explains that the literal source row fails on the one-vertex graph. The parent directory proves exactly this declaration in [`AgenticConjectures/WowiiGraphConjecture96.lean`](../../../AgenticConjectures/WowiiGraphConjecture96.lean), and [`upstream_statement_check.lean`](../upstream_statement_check.lean) closes the upstream theorem text, over the upstream definitions, with that proof.

In the snapshot, the central declaration still closes with `by sorry` and carries `@[category research open, AMS 5]`. It is the formal statement of the conjecture, not a proof. The file is unchanged at `main` commit `37f0808b83c56c8cef4ea5816b8329c09b8905a8` (2026-10-24). The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` and is a non-standalone snapshot. Two upstream-only FormalConjecturesForMathlib helpers are essential: `SimpleGraph.distEven` from [`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean`](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean#L396), and `SimpleGraph.indepNeighborsCard` from [`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Independence.lean`](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Independence.lean#L40). It also uses mathlib's `SimpleGraph.indepNum` and `SimpleGraph.dist`. The helper files are intentionally not copied; the two definitions are reproduced term for term in the checked module and in `upstream_statement_check.lean`.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt).
