**English** | [한국어](README.ko.md)

# OEIS A063880

## Partial theorem

The original problem asks whether the only primitive term among the
numbers with

\[
\sigma(n)=2\sigma^*(n)
\]

is \(108\) and whether every term is \(108\pmod{216}\). Here, letting

\[
C(n):=\prod_{e_p\ge2}p^{e_p}
\]

be the powerful core of \(n\), this folder proves the following.

> In every solution with \(\omega(C(n))\le2\), \(C(n)=108\). Hence the
> solutions in this subfamily are exactly
> \[
> n=108s,\qquad s\text{ squarefree},\qquad\gcd(s,108)=1
> \]
> and the unique primitive solution in this subfamily is \(108\), with
> every solution being \(108\pmod{216}\).

The detailed proof is in [PROOF.md](PROOF.md). This theorem only shows
that the powerful core of a hypothetical additional primitive solution
must have at least three distinct primes; it does not exclude that
case. It is therefore not a resolution of the full original
conjecture.

## Status of the source and scope of verification

- [OEIS A063880](https://oeis.org/A063880) revision #39, checked on
  2026-08-11, reported that a search for primitive terms up to
  \(n<10^{18}\) found only \(108\). This is a computation reported by
  the source; it does not mean this work independently re-ran that
  range.
- On the same day,
  [`63880.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/OEIS/63880.lean)
  at FormalConjectures main commit
  `9118d083ffca1536f521f9a7d103201f537ea670` marked both global
  statements — the unique primitive term and the congruence class — as
  `category research open`.
- This folder contains no computational certificate. The result
  completely classifies all numbers with \(\omega(C(n))\le2\) by the
  multiplicative local-ratio argument of [PROOF.md](PROOF.md), not by a
  finite search.
- The same public partial theorem could not be found on the open web,
  arXiv, math Q&A sites, SeqFan, or GitHub at the time, but this is
  only a negative search result. We do not assert novelty before peer
  review.

## Upstream Lean formalization

The FormalConjectures original and pinned provenance used for the audit
are preserved in the [upstream record](upstream/README.md) and in
[`63880.lean`](upstream/63880.lean). The global congruence and
uniqueness conjecture is a **statement** written with `by sorry`, not a
formal proof. This folder proves only the subfamily whose powerful core
has at most two prime factors.
