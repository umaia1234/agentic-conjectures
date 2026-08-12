**English** | [한국어](README.ko.md)

# OEIS A197702

[OEIS A197702](https://oeis.org/A197702) defines \(a(n)\) as the least
positive integer \(k\) for which \(n\) is a signed sum

\[
n=\pm1\pm3\pm\cdots\pm(2k-1).
\]

The canonical entry states:

> Conjecture. Let SO(k) be the sum of the first k odd positive integers.
> Then a(n)=k if n=SO(k). Otherwise, choose k so that
> SO(k-1)<n<SO(k). Then if SO(k)-n=4, a(n)=k+2, else if SO(k)-n is odd
> then a(n)=k+1 else a(n)=k. (This has been verified for n up to 200.)

The exact source fields and revision metadata are preserved in the
[local statement snapshot](upstream/A197702.txt).

## Result

The conjecture holds for every official index \(n\ge1\). Since the sum of the
first \(k\) odd numbers is \(k^2\), choose the unique upper-square index with

\[
(k-1)^2<n\le k^2
\]

and put \(d=k^2-n\). Then

\[
a(n)=
\begin{cases}
k+2,&d=4,\\
k+1,&d\text{ is odd},\\
k,&\text{otherwise}.
\end{cases}
\]

This is the full infinite claim, not a bounded verification.

## Proof idea

Let \(S\) be the positions given a minus sign. Then the signed-sum equation is
equivalent to

\[
n+2\sum_{i\in S}(2i+1)=k^2. \tag{1}
\]

The key lemma is that every integer \(t\) with
\(0<t<2k+1\), except \(t=2\), is a sum of distinct members of
\(\{1,3,\ldots,2k-1\}\). If \(t\) is odd, use \(t\) itself. If \(t\) is
even and not 2, use \(1+(t-1)\). Conversely, a sum of distinct positive odd
numbers cannot be 2.

Equation (1) now settles all cases. An even gap \(d\ne0,4\) is handled at
length \(k\) by a subset sum of \(d/2\); \(d=0\) uses no minus signs. An odd
gap cannot occur at length \(k\) by parity, but at length \(k+1\) the required
subset sum lies in the lemma's range. When \(d=4\), length \(k\) would require
the impossible subset sum 2 and length \(k+1\) has the wrong parity, while
length \(k+2\) works using \(1+(2k+3)=2k+4\).

No smaller length can work: if \(j<k\), any signed sum of the first \(j\) odd
numbers is at most \(j^2\le(k-1)^2<n\). Full details are in
[DETAILS.md](DETAILS.md).

## Lean formal proof

[`AgenticConjectures/OeisA197702.lean`](../../AgenticConjectures/OeisA197702.lean)
defines the literal sign-choice predicate `SignedSum`, proves it equivalent to
the normalized finite-subset equation, and proves an `IsLeast` theorem. The
registered final theorem is:

```text
oeis_a197702 :
  ∀ n k, 0 < k → (k - 1) * (k - 1) < n → n ≤ k * k →
    a n = if k * k - n = 4 then k + 2
      else if Odd (k * k - n) then k + 1 else k
```

It contains no `sorry`, extra axiom, or `native_decide`.

## Statement faithfulness

- `SignedSum n k` literally quantifies a sign \(+1\) or \(-1\) for each of
  the first \(k\) odd numbers. The theorem `signedSum_iff_representable`
  proves that this is equivalent to (1).
- `a n` is the infimum of exactly the positive qualifying lengths. The proof
  constructs a candidate and proves it least, so the infimum is attained.
- The interval hypotheses reproduce both OEIS branches: equality
  \(n=SO(k)=k^2\), and the strict interval
  \(SO(k-1)<n<SO(k)\).
- The official offset is 1. The interval hypotheses imply \(n>0\); no
  synthetic value at \(n=0\) is claimed.
- Natural subtraction occurs only as \(k^2-n\) under the explicit hypothesis
  \(n\le k^2\), so it agrees with the ordinary nonnegative gap.

## Research and verification status

As audited on 2026-08-12, the approved live OEIS entry still called the
formula a conjecture and recorded only a check through \(n=200\). Exact
A-number, wording, and formula searches found no independent proof. The
closest located entry is [A140358](https://oeis.org/A140358), an analogous
problem for consecutive rather than odd summands. This negative search does
not establish novelty. The result is unreviewed and has not been submitted to
OEIS or anywhere else.

The proof uses no computational search or finite certificate. From the
repository root, its Lean checks are reproduced by:

```bash
lake env lean AgenticConjectures/OeisA197702.lean
lake build
python3 scripts/check_axioms.py
```

The remaining repository-wide documentation and certificate gates are listed
in the root `AGENTS.md` and are also enforced in CI.
