**English** | [한국어](README.ko.md)

# Let's Prove Goldbach prize problem 4

The official [prize page](https://www.dimostriamogoldbach.it/en/prizes/)
listed problem 4 at **€100** with status **“No solutions received”** when
retrieved on 2026-08-12. On 2026-08-13 the same page instead showed
**“Solution under review.”** That state confirms receipt of a submission, not
its validity, and the page does not identify the submitter. Its opening
sentence is:

> “Let n_1, n_2 and n_3 be prime numbers such that n_1 < n_2 < n_3.”

For every integer (n>1), it then asks for positive (h,k), (h+k=n),
such that neither (n_1h-1) nor (n_1k+1) is divisible by (n_2) or
(n_3).

## Result

The universal assertion is false. Take

\[
  (n_1,n_2,n_3,n)=(2,3,5,5).
\]

There are only four positive ordered decompositions of (5):

| (h) | (k) | violated requirement |
|---:|---:|---|
| 1 | 4 | (3\mid 2k+1=9) |
| 2 | 3 | (3\mid 2h-1=3) |
| 3 | 2 | (5\mid 2h-1=5) |
| 4 | 1 | (3\mid 2k+1=3) |

Thus no permitted pair exists. This is not merely an (n=2) or (n=3)
boundary failure: (n=5), so changing the advertised hypothesis to
(n\geq4) would not repair it.

## Statement faithfulness

The Lean definition [`statement`](../../AgenticConjectures/GoldbachPrize4.lean)
quantifies over natural numbers. This matches the source because primes and
the requested (n,h,k) are positive integers. Natural-number subtraction
does not truncate in any admissible witness: primality gives (n_1\geq2)
and (h>0), hence (n_1h\geq2). The formal conjunction includes all four
nondivisibility requirements and the exact equation (h+k=n).

The source calls the claim a generalization of an earlier result. The
counterexample addresses the currently advertised quantifiers only; it does
not contradict a differently bounded earlier proposition.

## Machine verification

The sorry-free theorem
[`refuted`](../../AgenticConjectures/GoldbachPrize4.lean) specializes the
universal statement to (2,3,5,5), derives the four decompositions from
positivity and their sum, and closes each branch with the displayed exact
divisibility witness.

```bash
lake env lean AgenticConjectures/GoldbachPrize4.lean
```

See [DETAILS.md](DETAILS.md) for the kernel-checked proof map.

## Research status

Targeted searches for the exact divisibility statement and the tuple
((2,3,5,5)) found no published solution or counterexample on 2026-08-12.
They did recover the sponsor's earlier two-modulus proposition; that result
omits (n_3) and therefore does not address this counterexample.

The official page changed all three listed prize problems to “Solution under
review” by 2026-08-13. The page neither publishes the submissions nor names
their authors, so no relationship between that change and this repository is
asserted.

This result has not been reviewed or accepted by the prize sponsor, so the
repository does not claim the prize, novelty, or priority. No email or other
external submission has been made; repository policy requires human approval
before that step.
