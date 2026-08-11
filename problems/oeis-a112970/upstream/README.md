**English** | [한국어](README.ko.md)

# Formal Conjectures upstream snapshot

This directory preserves the exact Lean source used to compare the A112970
result in the parent directory with its pending upstream formalization.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Pull request: [#4450](https://github.com/google-deepmind/formal-conjectures/pull/4450)
- OEIS source: [A112970](https://oeis.org/A112970)
- Exact commit: [`93dc5e41789aadbd85380183779a94e7a59cb80e`](https://github.com/google-deepmind/formal-conjectures/tree/93dc5e41789aadbd85380183779a94e7a59cb80e)
- Original path: `FormalConjectures/OEIS/112970.lean`
- Immutable upstream file: [112970.lean](https://github.com/google-deepmind/formal-conjectures/blob/93dc5e41789aadbd85380183779a94e7a59cb80e/FormalConjectures/OEIS/112970.lean)
- Local snapshot: [112970_93dc5e41.lean](112970_93dc5e41.lean)
- SHA-256: `acd3d5c737707b44128d5cae814253e0feea8a9cd62889e31fa3191702394185`
- Central declarations: `OeisA112970.a`; `conjecture1`; `conjecture2`; `conjecture3`

## Relation to this problem

The snapshot defines the same guarded natural-number recurrence as the local
module. Its three research declarations formalize the equality
$a(2^n)=a(2^{n+1}+1)$ and both parts of
$a(2^n-1)=a(3\cdot2^n-1)=1$; every declaration ends in `sorry` at the pinned
commit. It explicitly describes, but does not formalize, the canonical OEIS
clause $a(2^n)=A033638(n)$. The parent module proves all three declarations
and adds the omitted quarter-square theorem.

The copied file retains its original copyright and Apache-2.0 license header.

## Build status

The source imports `FormalConjecturesUtil` and uses upstream benchmark
attributes, so it is preserved as a non-standalone provenance snapshot. Build
the local theorem module instead, or restore the upstream repository at the
pinned commit to compile this exact file in its original environment.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local
[Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived
mathematical content remains attributed through the canonical source link.
