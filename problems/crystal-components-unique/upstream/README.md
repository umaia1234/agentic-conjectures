# FormalConjectures upstream snapshot

This directory preserves the exact Lean source for the uniqueness of crystal components from
*The Biharmonic mean* (arXiv:1601.03081).

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Source paper: [M. Abrate, S. Barbero, U. Cerruti and N. Murru, *The Biharmonic mean*, arXiv:1601.03081](https://arxiv.org/abs/1601.03081)
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/Arxiv/1601.03081/UniqueCrystalComponents.lean`
- Immutable upstream file: [UniqueCrystalComponents.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/Arxiv/1601.03081/UniqueCrystalComponents.lean)
- Local snapshot: [UniqueCrystalComponents.lean](UniqueCrystalComponents.lean)
- SHA-256: `56b139be44fc9b8ef5b32b35e6ab46f6fef05c352a9c4417f7300398adc1f488`
- Central declarations: `Arxiv.«1601.03081».IsCrystalWithComponents`;
  `Arxiv.«1601.03081».isCrystalWithComponents_35_5_7`; `Arxiv.«1601.03081».crystals_components_unique`

## Relation to this problem

`crystals_components_unique` states the conjecture of the paper's concluding section: two crystal
factorizations n = ab = cd have {a, b} = {c, d}. The parent directory does not prove it. Its Lean
module [`AgenticConjectures/CrystalComponentsUnique.lean`](../../../AgenticConjectures/CrystalComponentsUnique.lean)
copies `IsCrystalWithComponents` and the test case term for term, records the theorem as
`statement`, and proves the partial results listed in the [problem README](../README.md).

In the snapshot, `crystals_components_unique` still closes with `by sorry` and carries
`@[category research open, AMS 11 26]`. It is the formal statement of the conjecture, not a proof.
The folder `FormalConjectures/Arxiv/1601.03081/` is unchanged at `main` commit
`37f0808b83c56c8cef4ea5816b8329c09b8905a8` (2026-10-24). The open pull request
[google-deepmind/formal-conjectures#7051](https://github.com/google-deepmind/formal-conjectures/pull/7051)
would add the divisibility conditions of Proposition 1 to this file. The copied file retains its
original copyright and license header.

## Build status

The source is a `module` file that imports `FormalConjecturesUtil` and uses the upstream
`category` and `AMS` attributes, so it is a non-standalone snapshot. Formal Conjectures at this
commit builds against Lean and mathlib `v4.33.1`. The definition itself uses only mathlib's `Odd`,
divisibility, multiplication and powers on `ℕ`, and the theorem only `Finset` insertion.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local
[Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt).
