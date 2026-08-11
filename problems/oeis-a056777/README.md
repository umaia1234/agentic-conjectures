**English** | [한국어](README.ko.md)

# OEIS A056777 / Choudhury–Wei Conjecture 1.1

## Partial theorem

The original conjecture asks whether a composite number \(n\ge4\) that
simultaneously satisfies

\[
\varphi(n+12)=\varphi(n)+12,
\qquad
\sigma(n+12)=\sigma(n)+12
\]

must be of the form

\[
n=p(p+8),
\qquad p,p+2,p+6,p+8\text{ all prime}.
\]

In this folder we prove the following.

> For a composite \(n\ge4\) satisfying the two equations above, \(n+12\)
> cannot be a prime power.

The detailed invariants and the case analysis for every prime are in
[PROOF.md](PROOF.md). This result rules out the opposite end of the
case "\(n\) is a prime power" already excluded by the paper, but does
not resolve the full original conjecture. In any remaining solution,
neither side is a prime power, and outside the paper's semiprime
theorem at least one side has three or more distinct prime factors or a
repeated prime factor.

## Status of the source and scope of verification

- The [Choudhury–Wei paper v3, Conjecture
  1.1](https://arxiv.org/abs/2606.10331v3), as of 2026-07-22, explicitly
  left this problem open. Theorem 2.2 of the paper decides the case
  where \(n,n+12\) are both products of two distinct primes, and
  Theorem 3.1 rules out the case where \(n\) itself is a prime power.
- The authors reported that, with their published [OpenMP
  code](https://github.com/bvrtoverfitprimes/integersequencetesting/blob/main/search_omp.cpp),
  they checked exactly \(2\le n<10^{12}\) and that all 166 solutions
  obtained were of the expected form. This is a computation reported by
  the source; it does not mean this work independently re-ran that
  range.
- This folder contains no computational certificate. The result does
  not rely on a finite search: it excludes every prime power
  \(n+12\) by the elementary number-theoretic argument of
  [PROOF.md](PROOF.md).
- The same public partial theorem could not be found on the open web,
  arXiv, math Q&A sites, SeqFan, or GitHub as of 2026-08-11, but this
  is only a negative search result. We do not assert novelty before
  peer review.

## Upstream Lean formalization

The FormalConjectures original and pinned provenance used for the audit
are preserved in the [upstream record](upstream/README.md) and in
[`56777.lean`](upstream/56777.lean). The central conjecture is a
**statement** closed with `by sorry`, not a formal proof, and the
prime-power exclusion theorem for \(n+12\) in this folder is not
formalized in that Lean file.
