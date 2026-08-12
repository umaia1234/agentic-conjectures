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

## Lean formal proof of the power-of-two case

[`AgenticConjectures/OeisA067720.lean`](../../AgenticConjectures/OeisA067720.lean)
copies the upstream membership predicate exactly and proves, without `sorry`,
extra axioms, or `native_decide`:

```text
power_two_add_one_not_solution {k a : ℕ} (ha : 2 ≤ a)
    (hk : k + 1 = 2 ^ a) : ¬ A k
```

The proof writes \(k=2t+1\) and \(k^2+1=2N\) with \(N\) odd. It then uses
\(\varphi(2N)=\varphi(N)\le N\) and proves the strict inequality

\[
N < k\,2^{a-1}=k\varphi(2^a),
\]

contradicting the defining A067720 equation. The odd-prime \(V\le5\) branch
in [PROOF.md](PROOF.md) remains an informal proof and is not registered as a
Lean theorem.

### Statement faithfulness

- `A k` is exactly the upstream proposition
  `Nat.totient (k ^ 2 + 1) = k * Nat.totient (k + 1)`; there is no sequence
  indexing or subtraction convention to translate.
- The hypotheses `2 ≤ a` and `k + 1 = 2 ^ a` are precisely the \(p=2\),
  \(a\ge2\) subfamily. They exclude the prime boundary case \(a=1\).
- The theorem says nothing about odd prime powers, arbitrary composite
  \(k+1\), or the upstream universal claim that every member other than
  \(k=8\) has \(k+1\) prime.

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
- This folder contains no finite-search certificate. The power-of-two
  exclusion is kernel-checked in Lean; the elementary inequalities and
  prime-factor structure arguments of [PROOF.md](PROOF.md) apply exactly to
  the larger stated subfamily.
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

## Reproduction

From the repository root:

```bash
lake env lean AgenticConjectures/OeisA067720.lean
python3 scripts/check_imports.py
python3 scripts/check_sorry.py
lake build
python3 scripts/check_axioms.py
python3 scripts/verify_all.py --ci
python3 scripts/gen_readme.py --check
python3 scripts/gen_upstream_docs.py --check
python3 scripts/check_docs.py
```

On the development machine, direct module elaboration took 4.45 seconds. A
warm-cache run of the eight repository gates on 2026-08-12 took 84.87 seconds
in total: 0.02 seconds for import reachability, 0.03 for the banned-construct
scan, 6.60 for `lake build`, 3.42 for the axiom audit, 74.59 for the 42
CI-feasible certificate checks, 0.09 for dashboard freshness, 0.02 for
upstream-documentation freshness, and 0.10 for the documentation audit. The
certificate sweep used the existing `drat-trim` build under `/tmp`, exposed on
`PATH`; no binary was committed.
