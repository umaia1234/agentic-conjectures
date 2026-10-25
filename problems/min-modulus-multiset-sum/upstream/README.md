# FormalConjectures upstream snapshot

This directory preserves the exact Lean source used to connect the work in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Paper: J. A. R. Fonollosa, *Minimum modulus for the unique multiset-sum problem*, [arXiv:2607.08366](https://arxiv.org/abs/2607.08366) (v2, 14 Jul 2026), Conjecture 1
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/Arxiv/2607.08366/MinModulus.lean` (the `Arxiv` folder of formal-conjectures, not the OEIS folders named in the shared `docs/upstream/sources.yaml` entry for this commit)
- Immutable upstream file: [MinModulus.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/Arxiv/2607.08366/MinModulus.lean)
- Local snapshot: [MinModulus.lean](MinModulus.lean)
- SHA-256: `033f9e60b50697530a788f371f1853494d42d6a078944df7dec45352b1805e8a`
- Central declaration(s): `IsValidMod`; `minModulus`; `min_modulus` (Conjecture 1); `exists_isValidMod_minModulus` (Theorem A, the matching construction)

## Relation to this problem

`min_modulus` is the open conjecture: for `2 ≤ n` and `0 < N < minModulus n`, no `n`-element subset of `ZMod N` is valid. The parent directory does not prove it. It records, in [`MinModulusMultisetSum.lean`](../../../AgenticConjectures/MinModulusMultisetSum.lean), the same proposition as `statement` (word for word, over the same definitions `IsValidMod` and `minModulus`), Lean proofs of three lower bounds on the modulus and of the cases `n ≤ 4`, and a two-implementation exhaustive search for `n ≤ 9`.

Both theorem bodies in the snapshot close with `by sorry`. `min_modulus` is a machine-readable statement of the conjecture, not a proof. `exists_isValidMod_minModulus` is tagged as solved, with a link to the author's separate Lean development. The copied file keeps its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` from the upstream project and uses its `category`/`AMS` attributes and the `module`/`public import`/`@[expose]` header. It is kept as a snapshot that does not build on its own: it will not compile from this problem directory once the upstream repository is gone. To rebuild it you need the matching FormalConjectures project with its Lean and mathlib versions.

## License

The Lean source keeps the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). The mathematical content is attributed to the paper linked above.
