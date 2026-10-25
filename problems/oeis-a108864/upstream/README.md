**English** | [한국어](README.ko.md)

# Formal Conjectures upstream snapshot

This directory preserves the exact Lean source used to connect the A108864
refutation in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A108864](https://oeis.org/A108864) (perfect deficiency:
  [A109883](https://oeis.org/A109883))
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/OEIS/108864.lean`
- Immutable upstream file: [108864.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/OEIS/108864.lean)
- Local snapshot: [108864.lean](108864.lean)
- SHA-256: `ef28b630f7c6c2370106c8286daee4ad374efbdcfcb04558368ac7150e68ce10`
- Central declarations: `OeisA108864.perfectDeficiency`; `OeisA108864.A`;
  `OeisA108864.a`; `OeisA108864.conjecture`

## Relation to this problem

The snapshot formalizes the OEIS question "Is 1155 the last odd number in
this sequence?" as `conjecture : ∀ n > 58, Even (a n)`, with the 0-indexed
`a n = Nat.nth A n` and `a 58 = 1155`. The parent directory proves the
negation of exactly this proposition: the odd number
`815634435 = 3 * 5 * 7 * 11 * 547 * 1291` is a term (perfect deficiency 6)
with index greater than 58. The local module
`AgenticConjectures/OeisA108864.lean` copies `perfectDeficiency`, `A`, its
`DecidablePred` instance, and `a` term for term.

The research declaration `conjecture` still closes with `sorry` at the
pinned commit. It is a machine-readable statement of the question, not a
formal proof. The five `test` theorems `a_0`–`a_4` are proved upstream by
`decide`. The copied file retains its original copyright and license header.

## Build status

The source starts with `module`, imports `FormalConjecturesUtil`, and uses
the upstream `category` and `AMS` attributes, so it is preserved as a
non-standalone provenance snapshot. Build the local theorem module instead,
or restore the upstream repository at the pinned commit to compile this
exact file in its original environment.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local
[Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived
mathematical content remains attributed through the OEIS source links above.
