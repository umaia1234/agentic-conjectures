# FormalConjectures upstream snapshot

This directory preserves the exact Lean source used to connect the A063880 work in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A063880](https://oeis.org/A063880)
- Exact commit: `9118d083ffca1536f521f9a7d103201f537ea670`
- Original path: `FormalConjectures/OEIS/63880.lean`
- Immutable upstream file: [63880.lean](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/OEIS/63880.lean)
- Local snapshot: [63880.lean](63880.lean)
- SHA-256: `d221ce0fb59297e6555e2632c38c422c2bd2b393eff9f58f118c30d860c080c0`
- Central declaration(s): `OeisA63880.A`; `OeisA63880.IsPrimitiveTerm`; `OeisA63880.mod_216_of_a`; `OeisA63880.unique_primitive_108`

## Relation to this problem

The upstream file states the global congruence and unique-primitive-term conjectures. The parent directory proves their predicted structure only when the powerful core has at most two distinct prime factors; it does not prove the global Lean statements.

The conjectural declaration still closes with `by sorry`. It is a machine-readable statement of the conjecture, not a formal proof. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` from the upstream project and is preserved as a non-standalone snapshot. It will not compile merely from this problem directory after the upstream repository is removed; reproducing the original environment requires the matching FormalConjectures project and its Lean/mathlib dependencies.

The exact source also relies transitively on upstream-only companion definitions that are not copied here:

- `Set.IsPrimitive` from `FormalConjecturesForMathlib/NumberTheory/Primitive.lean`;
- `Nat.Powerful` from `FormalConjecturesForMathlib/Data/Nat/Full.lean`.

## Snapshot choice

The detached `formal-auto-oeis` checkout at commit `67338a157bbb8d87e9a349d662f82a868bda6327` also contains an earlier version of this manual OEIS file at the same path. This directory deliberately keeps the later main-branch version at `9118d083ffca1536f521f9a7d103201f537ea670`, which is the revision audited by the parent problem document; the older duplicate is not copied.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived mathematical content remains attributed through the OEIS source link above.
