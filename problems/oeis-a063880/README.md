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

> In every solution with \(\omega(C(n))\le3\), \(C(n)=108\). Hence the
> solutions in this subfamily are exactly
> \[
> n=108s,\qquad s\text{ squarefree},\qquad\gcd(s,108)=1
> \]
> and the unique primitive solution in this subfamily is \(108\), with
> every solution being \(108\pmod{216}\).

The case \(\omega(C(n))\le2\) is proved in [PROOF.md](PROOF.md); the
case of three primes is added in [THREE_PRIMES.md](THREE_PRIMES.md)
(see [Three-prime cores](#three-prime-cores)). Both are
**kernel-checked in Lean 4** in
[`AgenticConjectures/OeisA063880.lean`](../../AgenticConjectures/OeisA063880.lean)
(see [below](#lean-4-formalization)). The theorem only shows that the
powerful core of a hypothetical additional primitive solution must have
at least four distinct primes; it does not exclude that case. It is
therefore not a resolution of the full original conjecture.

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
- The classification of all solutions with \(\omega(C(n))\le3\) is a
  proof, not a search: the multiplicative local-ratio argument of
  [PROOF.md](PROOF.md) and the three-prime argument of
  [THREE_PRIMES.md](THREE_PRIMES.md), whose finitely many leftover
  cases are checked inside Lean. The machine-checked artifact is the
  Lean module described below (CI rebuilds it with the no-`sorry` gate
  and the axiom audit). The two Python searches of
  [THREE_PRIMES.md](THREE_PRIMES.md) (section 8) are an independent
  cross-check of part of the three-prime case, not a certificate.
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
lake build AgenticConjectures.OeisA063880   # this module alone, ~20 s once mathlib is cached
lake build                                  # whole library (needed by check_axioms.py)
python3 scripts/check_sorry.py
python3 scripts/check_axioms.py             # only propext / Classical.choice / Quot.sound
```

## Three-prime cores

**Result.** No powerful \(n=p^aq^br^c\) (\(p,q,r\) distinct primes,
\(a,b,c\ge2\)) satisfies \(\sigma(n)=2\sigma^*(n)\). Combined with the
two-prime theorem, every solution with \(\omega(C(n))\le3\) has
\(C(n)=108\). So in this larger subfamily, too, every term is
\(108\pmod{216}\) and \(108\) is the only primitive term. This is
kernel-checked in Lean against the same upstream predicate; the
informal proof is [THREE_PRIMES.md](THREE_PRIMES.md).

**Method.** Sort the primes as \(p<q<r\).

- No factor \(2\): the bounds \(\sigma(p^e)/(1+p^e)<p/(p-1)\) leave only
  \(\{3,5,r\}\) with \(r\le13\), which three finite boxes exclude.
- \(\{2,3,r\}\): ratio bounds settle every case except \(a=2\),
  \(b\in\{2,3\}\). There the equation forces either
  \(\sigma(r^c)=1+r^c\), which is impossible, or
  \(91\sigma(r^c)=100(1+r^c)\), which forces \(r\mid9\).
- \(2<5\le q<r\): with \(K=2^{a+1}-1\) the equation becomes the integer
  identity \(W_qW_r=K(K+3)t_qt_r\). A 2-adic valuation identity ties
  \(b\) to \(c\) (for example, \(c\) even forces \(b\equiv7\pmod{16}\)).
  Size bounds from the auxiliary integers \(\Omega,H,G\) then exclude
  every exponent pattern except finitely many cases: five boxes, and
  for 16 pairs \((a,q)\) a quadratic in \(r\) with no admissible root.
- The squarefree-part induction of the two-prime theorem, rerun with
  bound \(3\), lifts the powerful case to every \(n\).

**Reproduce.** The commands are run from the repository root, except
the searches, which are run in this folder. Times are measured on the
development machine:

```bash
lake build AgenticConjectures.OeisA063880   # ~20 s once mathlib is cached; checks the whole proof
lake build && python3 scripts/check_axioms.py   # only propext / Classical.choice / Quot.sound
cd problems/oeis-a063880
python3 three_prime_search.py --amax 22       # 4.0 s (CI)
python3 three_prime_search_int.py --amax 22   # 8.3 s (CI)
python3 three_prime_search.py --amax 28       # 5 min 06 s (machine under load)
python3 three_prime_search_int.py --amax 28   # 16 min 08 s (machine under load)
```

The two searches are independent exact cross-checks of the case
\(2<5\le q<r\) for \(2\le a\le\) `AMAX` (all \(q,b,r,c\)). Neither finds
a solution, and neither is part of the proof.

| Declaration | Content |
|---|---|
| `not_a_three_prime_pow` | for distinct primes \(p,q,r\) and \(a,b,c\ge2\): `¬ A (p ^ a * q ^ b * r ^ c)` |
| `three_prime_sorted`, `caseB`, `case23`, `caseA` | the sorted case split: no factor \(2\); \(\{2,3,r\}\); \(2<5\le q<r\) |
| `two_adic_rel`, `caseA_two_adic` | the 2-adic identity and its consequences for \((b,c)\) |
| `caseA_c7`, `caseA_c46`, `caseA_c2`, `caseA_c5b`, `caseA_c3a`, `caseA_c3b` | the size bounds of the case split on \(c\) |
| `caseA_c3b_finite`, `box_*` (eight boxes) | the finite checks |
| `eq_108_of_powerful_of_card_le_three` | a powerful solution with at most three prime factors is \(108\) |
| `exists_eq_108_mul_of_card_le` | the squarefree-part induction for any bound \(k\) under which powerful solutions are \(108\) |
| `exists_eq_108_mul_of_card_le_three` | **main theorem**: `A n` and at most three primes \(p\) with \(p^2\mid n\) ⇒ `n = 108 * s` with `s` squarefree and coprime to \(108\) |
| `mod_216_of_card_le_three`, `eq_108_of_isPrimitiveTerm_of_card_le_three` | corollaries: \(n\equiv108\pmod{216}\), and the only primitive term of the subfamily is \(108\) |

A full map from the proof steps to the Lean lemmas is in
[THREE_PRIMES.md](THREE_PRIMES.md), section 9.

Statement faithfulness. `not_a_three_prime_pow` is stated for the
upstream predicate `A` itself (copied term for term, as above), with
hypotheses `p.Prime`, `q.Prime`, `r.Prime`, pairwise `≠`, and
`2 ≤ a`, `2 ≤ b`, `2 ≤ c`. The hypothesis \(\omega(C(n))\le3\) is encoded
exactly like the two-prime one, as
`(n.primeFactors.filter fun p => p ^ 2 ∣ n).card ≤ 3`. The conclusion
\(C(n)=108\) is again
`∃ s, Squarefree s ∧ Nat.Coprime 108 s ∧ n = 108 * s`. The case
\(2<5\le q<r\) is argued over `ℤ` inside the proofs, after casting from
`ℕ`. In the new `ℕ` statements the only subtraction is `p - 1` with
`1 ≤ p`, which is exact. The two-prime theorems above are unchanged.

**Not claimed.** Cores with four or more distinct primes are not
treated, so both OEIS conjectures remain open. The OEIS search to
\(10^{18}\) was not rerun. We do not assert novelty.

## Upstream Lean formalization

The FormalConjectures original and pinned provenance used for the audit
are preserved in the [upstream record](upstream/README.md) and in
[`63880.lean`](upstream/63880.lean). The global congruence and
uniqueness conjecture is a **statement** written with `by sorry`, not a
formal proof. This folder proves only the subfamily whose powerful core
has at most three prime factors; that proof lives in this repository's own
module listed above, which restates the upstream definitions term for
term instead of importing the (non-standalone) snapshot.
