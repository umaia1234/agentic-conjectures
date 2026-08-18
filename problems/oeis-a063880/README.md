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

The detailed proof is in [PROOF.md](PROOF.md), and the theorem is
**kernel-checked in Lean 4** in
[`AgenticConjectures/OeisA063880.lean`](../../AgenticConjectures/OeisA063880.lean)
(see [below](#lean-4-formalization)). This theorem only shows
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
  completely classifies all solutions with \(\omega(C(n))\le2\) by the
  multiplicative local-ratio argument of [PROOF.md](PROOF.md), not by a
  finite search; the machine-checked artifact is the Lean module
  described below (CI rebuilds it with the no-`sorry` gate and the
  axiom audit).
- The same public partial theorem could not be found on the open web,
  arXiv, math Q&A sites, SeqFan, or GitHub at the time, but this is
  only a negative search result. We do not assert novelty before peer
  review.

## Lean 4 formalization

The partial theorem is formalized, `sorry`-free and against mathlib
only, in
[`AgenticConjectures/OeisA063880.lean`](../../AgenticConjectures/OeisA063880.lean)
(namespace `AgenticConjectures.OeisA063880`):

| Declaration | Content |
|---|---|
| `unitaryDivisors`, `usigma`, `A` | the upstream definitions `OeisA63880.unitaryDivisors / usigma / A`, term for term: `A n := 0 < n ∧ σ 1 n = 2 * usigma n` |
| `IsPrimitive`, `IsPrimitiveTerm`, `Powerful` | the upstream companions `Set.IsPrimitive`, `OeisA63880.IsPrimitiveTerm` and `Nat.Powerful` (= `Nat.Full 2`), copied / unfolded |
| `statement_mod_216`, `statement_unique_primitive` | the two open upstream conjectures `mod_216_of_a`, `unique_primitive_108` (`Prop`s, **not** proved) |
| `usigma_mul`, `usigma_prime_pow`, `usigma_eq_sigma_of_squarefree` | \(\sigma^*\) is multiplicative, \(\sigma^*(p^e)=1+p^e\) for \(e\ge1\), and \(\sigma^*=\sigma\) on squarefree numbers |
| `a_mul_iff` | reduction (4) of PROOF.md: for squarefree \(s\) coprime to \(m\), `A (m * s) ↔ A m` |
| `sigma_prime_pow_lt`, `not_a_prime_pow`, `sigma_mul_sigma_lt_of_odd` | the local-ratio bounds: one prime power is never a solution, nor is \(p^aq^b\) with \(p,q\) distinct odd primes |
| `eq_of_two_pow_mul_prime_pow` | the two-prime Diophantine classification: \(\sigma(2^a)\sigma(q^b)=2(1+2^a)(1+q^b)\) with \(q\) odd, \(a,b\ge2\) forces \(q=3,a=2,b=3\) |
| `eq_108_of_powerful` | a powerful solution with at most two prime factors is \(108\) |
| `exists_eq_108_mul_of_card_le_two` | **main theorem**: `A n` and at most two primes \(p\) with \(p^2\mid n\) ⇒ `n = 108 * s` with `s` squarefree and coprime to \(108\) (i.e. \(C(n)=108\)) |
| `mod_216_of_card_le_two`, `eq_108_of_isPrimitiveTerm_of_card_le_two` | corollaries: \(n\equiv108\pmod{216}\), and the only primitive term of the subfamily is \(108\) |
| `a_108_mul`, `primeFactors_filter_sq_dvd_108_mul` | conversely, for \(s\) squarefree and coprime to \(108\), \(108s\) is a term and lies in the subfamily (the primes \(p\) with \(p^2\mid108s\) are exactly \(2,3\)) — so the classification is an equivalence |
| `powerful_of_isPrimitiveTerm`, `a_of_primitive_mul_squarefree` | the two upstream `textbook` lemmas (sorry-backed upstream): primitive terms are powerful, and primitive × coprime squarefree is a term |
| `a_108`, `isPrimitiveTerm_108` | sanity checks: two of the upstream test theorems |

Statement faithfulness. `A`, `unitaryDivisors` and `usigma` are copied
term for term from the upstream snapshot (`σ 1` is
`ArithmeticFunction.sigma 1`; all equations are additive in `ℕ`, so no
truncated subtraction is involved). `Set.IsPrimitive` and `Nat.Powerful`
are not in mathlib; they are copied from the upstream companion files
(`FormalConjecturesForMathlib/NumberTheory/Primitive.lean`,
`…/Data/Nat/Full.lean` at the pinned commit) with `Nat.Full 2` unfolded
to `∀ p ∈ n.primeFactors, p ^ 2 ∣ n`. The hypothesis
\(\omega(C(n))\le2\) is encoded as
`(n.primeFactors.filter fun p => p ^ 2 ∣ n).card ≤ 2` — the primes
\(p\) with \(p^2\mid n\) are exactly the primes of the powerful core —
and the conclusion \(C(n)=108\) as
`∃ s, Squarefree s ∧ Nat.Coprime 108 s ∧ n = 108 * s`, which is
equivalent (for such \(s\), \(C(108s)=108\); conversely, if
\(C(n)=108\) then \(n/108\) is squarefree and coprime to \(108\)).

The Lean proof follows PROOF.md: multiplicativity of \(\sigma\) and
\(\sigma^*\) reduces `A` to the powerful core, the local-ratio bounds
exclude one prime and two odd primes, and the \(q\mid3\) argument plus
\((2^{a+1}-7)(3^{b}-3)=24\) (PROOF.md's equation (9) multiplied by 3)
settles \(2^aq^b\). Two presentational deviations: the solutions are
recovered by strong induction on \(n\), peeling off one exponent-1
prime at a time with `a_mul_iff`, instead of naming the core \(C(n)\)
explicitly; and the powerful case is split on the number of prime
factors (\(0,1,2\)) of \(n\).

Reproduce (from the repository root; `lake build` and `check_axioms.py`
need the mathlib cache, `lake exe cache get`):

```bash
lake build AgenticConjectures.OeisA063880   # this module alone, ~10 s once mathlib is cached
lake build                                  # whole library (needed by check_axioms.py)
python3 scripts/check_sorry.py
python3 scripts/check_axioms.py             # only propext / Classical.choice / Quot.sound
```

## Upstream Lean formalization

The FormalConjectures original and pinned provenance used for the audit
are preserved in the [upstream record](upstream/README.md) and in
[`63880.lean`](upstream/63880.lean). The global congruence and
uniqueness conjecture is a **statement** written with `by sorry`, not a
formal proof. This folder proves only the subfamily whose powerful core
has at most two prime factors; that proof lives in this repository's own
module listed above, which restates the upstream definitions term for
term instead of importing the (non-standalone) snapshot.
