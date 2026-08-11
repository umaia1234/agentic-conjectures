**English** | [한국어](README.ko.md)

# OEIS A369378: the lower-bound conjecture is proved

## Result

[OEIS A369378](https://oeis.org/A369378) contains the conjecture:

> Conjecture: if n > 0, then 2^(2^n+1)-1 + 2^k is not prime for every k < 2^n.

The conjecture is true. For every natural \(n>0\) and \(k<2^n\),

\[
N_{n,k}=2^{2^n+1}-1+2^k
\]

is composite. This proves only the displayed lower bound: it makes no claim
about \(k\ge 2^n\) or about whether the sequence term \(a(n)\) exists.

## Proof

If \(k=0\), then

\[
N_{n,0}=2^{2^n+1},
\]

which is a nontrivial power of two.

Now suppose \(k>0\). Write

\[
k=2^r q
\]

with \(q\) odd. Since \(2^r\le k<2^n\), we have \(r<n\). Set

\[
x=2^{2^r},\qquad d=x+1.
\]

The exponent \(2^{n-r}\) is even, so

\[
d\mid x^{2^{n-r}}-1=2^{2^n}-1.
\]

Because \(q\) is odd, \(d\mid x^q+1=2^k+1\). Therefore

\[
\begin{aligned}
N_{n,k}
  &=2\bigl(2^{2^n}-1\bigr)+(2^k+1),
\end{aligned}
\]

and \(d\mid N_{n,k}\). Finally \(2\le d<N_{n,k}\), so \(N_{n,k}\) is not
prime. Notice that the argument uses a Fermat *number* as a divisor; it does
not assume that \(d\) itself is prime.

## Source and statement faithfulness

The canonical OEIS record was checked on 2026-08-12. Its internal record is
revision 40, timestamped 2024-02-13, with offset 0. Earlier entry history
explicitly said "natural k," so the Lean statement uses \(k:\mathbb N\),
including \(k=0\). The entry's sample Mathematica search starts at \(k=1\),
but the zero case is part of the literal natural-number claim and is
immediately composite.

Lean's natural-number subtraction in \(2^{2^n+1}-1\) is exact because the
power is positive. There is no upstream Lean snapshot for this entry; the
module records these domain, boundary, and subtraction conventions directly.

## Machine verification

[`AgenticConjectures/OeisA369378.lean`](../../AgenticConjectures/OeisA369378.lean)
proves the universal theorem in mathlib-based Lean 4 without `sorry`, extra
axioms, or `native_decide`:

```lean
oeis_a369378 : ∀ n k : ℕ, 0 < n → k < 2 ^ n →
  ¬ Nat.Prime (2 ^ (2 ^ n + 1) - 1 + 2 ^ k)
```

Run from the repository root:

```bash
lake build AgenticConjectures.OeisA369378
python3 scripts/check_sorry.py
python3 scripts/check_axioms.py
```

## Prior-art and submission status

Exact-identifier and exact-formula searches on 2026-08-12 found the OEIS
record and a public brute-force search program, but no public proof or
resolution on OEIS, arXiv, GitHub, MathOverflow, or Math StackExchange. That
negative search is not evidence of novelty. This proof is unreviewed, no
novelty is claimed, and nothing has been submitted to OEIS or any other
external venue.
