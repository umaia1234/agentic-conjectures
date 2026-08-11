**English** | [한국어](README.ko.md)

# Formal Conjectures upstream snapshot

This directory preserves the exact Lean source used to connect the A072780
counterexample in the parent directory to its upstream formalized conjecture.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- OEIS source: [A072780](https://oeis.org/A072780)
- Exact commit: `67338a157bbb8d87e9a349d662f82a868bda6327`
- Original path: `FormalConjectures/OEIS/Auto/72780_30fabef9.lean`
- Immutable upstream file: [72780_30fabef9.lean](https://github.com/google-deepmind/formal-conjectures/blob/67338a157bbb8d87e9a349d662f82a868bda6327/FormalConjectures/OEIS/Auto/72780_30fabef9.lean)
- Local snapshot: [72780_30fabef9.lean](72780_30fabef9.lean)
- SHA-256: `9c984bee8555b50e7226f77c2ff422f33c2c220c06461073f1bbae31c6a62839`
- Central declarations: `a`; `oeis_72780_conjecture`;
  `oeis_72780_twin_prime_conjecture`; `oeis_72780_goldbach_conjecture`

## Relation to this problem

The parent directory refutes `oeis_72780_goldbach_conjecture` at
`(m,r)=(8,7)`. It makes no claim against the other two conjectural theorems
in the snapshot.

The conjectural declarations close with `by sorry`. They are machine-readable
statements, not formal proofs. The copied file retains its original copyright
and license header.

## Build status

The source imports `FormalConjectures.Util.ProblemImports` from the upstream
project and is preserved as a non-standalone snapshot. Reproducing its
original environment requires the matching Formal Conjectures project and
its Lean/mathlib dependencies.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local
[Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). OEIS-derived
mathematical content remains attributed through the OEIS source link above.
