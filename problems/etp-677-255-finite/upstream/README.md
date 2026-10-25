# FormalConjectures upstream snapshot

This directory preserves the exact Lean source for Problem 8.1 of the
Equational Theories Project (does Equation 677 imply Equation 255 for finite
magmas?).

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/Other/EquationalTheories_677_255.lean`
- Immutable upstream file: [EquationalTheories_677_255.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/Other/EquationalTheories_677_255.lean)
- Local snapshot: [EquationalTheories_677_255.lean](EquationalTheories_677_255.lean)
- SHA-256: `02562980966eed324c96b7a743bb80474526b8837f4d014a7a537d4b5f957e98`
- Central declarations: `EquationalTheories_677_255.Magma`; `EquationalTheories_677_255.Equation255`; `EquationalTheories_677_255.Equation677`; `EquationalTheories_677_255.Finite.Equation677_implies_Equation255` (tagged `research open`)

## Relation to this problem

[`Etp677Implies255Finite.lean`](../../../AgenticConjectures/Etp677Implies255Finite.lean)
copies `Magma`, the `◇` notation, `Equation255` and `Equation677` term for term
and states `Finite.Equation677_implies_Equation255` verbatim as
`def statement : Prop`. The remaining upstream theorems are side results:
`Equation255_not_implies_Equation677` and its finite variant are proved
upstream by a 3-element table; `Equation677_not_implies_Equation255` (the
infinite case, resolved by the project's free-magma construction) is
`sorry`-backed upstream. None of them is restated.

The open theorem is `sorry`-backed upstream and remains open here. The copied
file retains its original copyright and license header.

## Build status

The source starts with `module` and `public import FormalConjecturesUtil` and
uses `@[expose] public section` and the `category`/`AMS` attributes, so it is a
non-standalone snapshot that only builds inside FormalConjectures. The local
module drops exactly that infrastructure and keeps every definition verbatim.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt).
