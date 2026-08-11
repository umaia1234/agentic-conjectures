**English** | [한국어](README.ko.md)

# OEIS A067720

## Partial theorem

The original problem asks whether \(k=8\) is the only solution of

\[
\varphi(k^2+1)=k\varphi(k+1)
\]

for which \(k+1\) is composite. This folder decides the following
subfamily in which \(k+1\) is a prime power.

> Let \(k+1=p^a\) with \(p\) prime and \(a\ge2\). If \(p=2\), there is
> no solution. If \(p\) is odd and
> \[
> V:=v_2(p^a-1)+v_2(p-1)\le5
> \]
> then the unique solution is \((p,a,k)=(3,2,8)\).

The proof is in [PROOF.md](PROOF.md). This result does not treat
general composite \(k+1\), and it also leaves open the prime-power
cases with odd \(p\) and \(V\ge6\). It is therefore not a resolution of
the full original conjecture.

## Status of the source and scope of verification

- [OEIS A067720](https://oeis.org/A067720) revision #18, checked on
  2026-08-11, asked "is \(8\) the only additional value?", and the
  [b-file](https://oeis.org/A067720/b067720.txt) provided the first
  10000 terms.
  The length of the b-file is not the range of the conjecture or of
  this proof.
- On the same day,
  [`67720.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/OEIS/67720.lean)
  at FormalConjectures main commit
  `9118d083ffca1536f521f9a7d103201f537ea670` likewise marked this
  statement as `category research open`.
- This folder contains no computational certificate. The conclusion is
  not the result of a finite search: the elementary inequalities and
  prime-factor structure arguments of [PROOF.md](PROOF.md) apply
  exactly to the specified subfamily.
- The same public partial theorem could not be found on the open web,
  arXiv, math Q&A sites, SeqFan, or GitHub at the time, but this is
  only a negative search result. We do not assert novelty before peer
  review.

## Upstream Lean formalization

The FormalConjectures original and pinned provenance used for the audit
are preserved in the [upstream record](upstream/README.md) and in
[`67720.lean`](upstream/67720.lean). The global statement that `k+1` is
prime except for `k=8` is a **conjecture statement** written as
`by sorry`, not a formal proof, and this folder treats only the
prime-power subfamily specified above.
