# FormalConjectures upstream snapshot

This directory preserves the exact Lean source used to connect the work in the parent directory to its upstream formalized conjectures.

## Provenance

- Repository: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
- Paper: [arXiv:2501.03234](https://arxiv.org/abs/2501.03234) (B. C. Berndt, R. N. Bhat, J. L. Meyer, L. Xie, A. Zaharescu, *An arithmetic sum associated with the classical theta function*)
- Exact commit: `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
- Original path: `FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean`
- Immutable upstream file: [ArithmeticSumS.lean](https://github.com/google-deepmind/formal-conjectures/blob/c094b979118b89adb77cf5f8d923ac9dd2e51b1d/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)
- Local snapshot: [ArithmeticSumS.lean](ArithmeticSumS.lean)
- SHA-256: `ff3587186cca274bad749267876939be91a28a4f55b6bcfa30dd6b70f08100c2`
- Central declaration(s): `Arxiv.«2501.03234».S'`; `Arxiv.«2501.03234».S`; `conjecture_1_1`; `conjecture_4_1`; `conjecture_4_2`; `conjecture_4_3`; `conjecture_4_4`

## Relation to this problem

The upstream file defines `S' h k` and `S k` and states five conjectures about `S k` for odd primes `k`: positivity (`conjecture_1_1`), the lower bounds `k < S k` for `k > 5`, `2k < S k` for `k > 233`, `3k < S k` for `k > 3119` (`conjecture_4_1` to `conjecture_4_3`), and the asymptotic statement that `n * k < S k` for all large primes, for every `n` (`conjecture_4_4`). The parent directory copies the two definitions term for term into `AgenticConjectures.ThetaArithmeticSum`, restates the five conjectures as `Prop` definitions, and proves exact reduction identities and small cases there. It does not prove any of the five conjectures; the computational evidence and the exact identities are described in the parent README.

The five conjectural declarations still close with `by sorry`. They are machine-readable statements of the conjectures, not formal proofs. The copied file retains its original copyright and license header.

## Build status

The source imports `FormalConjecturesUtil` from the upstream project and uses its `category`/`AMS` attributes, so it is preserved as a non-standalone snapshot. It will not compile merely from this problem directory after the upstream repository is removed; reproducing the original environment requires the matching FormalConjectures project and its Lean/mathlib dependencies.

## License

The Lean source retains the upstream Apache-2.0 notice; see the local [Apache License 2.0](../../../THIRD_PARTY_LICENSES/Apache-2.0.txt). The mathematical content is attributed to the paper linked above.
