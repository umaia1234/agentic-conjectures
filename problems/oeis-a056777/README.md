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
[PROOF.md](PROOF.md), and the theorem is **kernel-checked in Lean 4** in
[`AgenticConjectures/OeisA056777.lean`](../../AgenticConjectures/OeisA056777.lean)
(see [below](#lean-4-formalization)). This result rules out the opposite end of the
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
  [PROOF.md](PROOF.md), and that argument is machine-checked by the
  Lean module described below (CI rebuilds it with the no-`sorry` gate
  and the axiom audit).
- The same public partial theorem could not be found on the open web,
  arXiv, math Q&A sites, SeqFan, or GitHub as of 2026-08-11, but this
  is only a negative search result. We do not assert novelty before
  peer review.

## Lean 4 formalization

The partial theorem is formalized, `sorry`-free and against mathlib
only, in
[`AgenticConjectures/OeisA056777.lean`](../../AgenticConjectures/OeisA056777.lean)
(namespace `AgenticConjectures.OeisA056777`):

| Declaration | Content |
|---|---|
| `A n` | the upstream predicate `OeisA56777.A`, term for term: `¬ n.Prime ∧ 1 < n ∧ φ (n+12) = φ n + 12 ∧ σ 1 (n+12) = σ 1 n + 12` (upstream spells `φ` as `totient`) |
| `statement` | the open Choudhury–Wei Conjecture 1.1, `∀ n, A n → ComesFromPrimeQuadruple n` (a `Prop`, **not** proved) |
| `totient_mul_sigma_add_lt_of_not_isPrimePow` | the key inequality \(\varphi(m)\sigma(m)+m<m^2\) for every \(m>1\) that is not a prime power (inequality (7) of PROOF.md) |
| `add_twelve_ne_prime_pow` | **main theorem**: `A n → q.Prime → n + 12 ≠ q ^ ℓ` |
| `not_isPrimePow_add_twelve` | the same in mathlib's `IsPrimePow` form: `A n → ¬ IsPrimePow (n + 12)` |

Statement faithfulness. `A` is copied term for term from the upstream
snapshot (the only spelling difference is mathlib's notation `φ` for
`Nat.totient`), so "composite \(n\ge4\)" is encoded as
`¬ n.Prime ∧ 1 < n` (which forces \(n\ge4\)); both equations are
additive in `ℕ`, so no truncated-subtraction issue arises; \(\varphi\)
is `Nat.totient` and \(\sigma\) is `ArithmeticFunction.sigma 1`.
"Prime power" is `q ^ ℓ` with `q` prime and any `ℓ` (for `ℓ = 0` the
claim is trivial), equivalently mathlib's `IsPrimePow`.

The Lean proof follows PROOF.md case by case (\(q\ge5\), \(q=3\),
\(q=2\)) with one deliberate deviation: for \(q=2\) it does not use
"\(\sigma(n)\) odd ⇒ \(n\) is a square or twice a square"; instead,
writing \(n=4w\) with \(w\) odd and \(8\mid w+3\), the two equations
give \(\varphi(w)=w-3\) and \(7\sigma(w)=8w+11\). If \(w\) is a prime
power, \(\varphi(w)=w-3\) forces \(w=9\), but \(8\nmid12\); otherwise
the key inequality gives \(w\le9\), so \(8\mid w+3\) leaves only
\(w=5\), which \(7\sigma(w)=8w+11\) excludes (\(7\nmid51\)). The
theorem proved is the same.

Reproduce (from the repository root; `lake build` and `check_axioms.py`
need the mathlib cache, `lake exe cache get`):

```bash
lake build AgenticConjectures.OeisA056777   # this module alone, ~20 s once mathlib is cached
lake build                                  # whole library (needed by check_axioms.py)
python3 scripts/check_sorry.py
python3 scripts/check_axioms.py             # only propext / Classical.choice / Quot.sound
```

## Upstream Lean formalization

The FormalConjectures original and pinned provenance used for the audit
are preserved in the [upstream record](upstream/README.md) and in
[`56777.lean`](upstream/56777.lean). The central conjecture is a
**statement** closed with `by sorry`, not a formal proof, and the
prime-power exclusion theorem for \(n+12\) in this folder is not
formalized in that upstream file — it lives in this repository's own
module listed above, which restates the upstream predicate term for term
instead of importing the (non-standalone) snapshot.
