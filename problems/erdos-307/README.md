**English** | [한국어](README.ko.md)

# Erdős problem #307 audit

This directory contains a proof audit and exact computations for the question

\[
\left(\sum_{p\in P}\frac1p\right)
\left(\sum_{q\in Q}\frac1q\right)=1
\]

with finite prime sets `P,Q`.  The problem remains open; nothing here is
presented as a solution or as a proof of novelty.

## Main outcomes

- The forcing identities `A(P)=M(Q)`, `A(Q)=M(P)` and disjointness are
  re-proved from reduced fractions.
- For every odd `r in U=P union Q`, the stronger local condition
  `(M(U)/r | r)=1` is derived with an explicit square root from the opposite
  side's prime product.
- Multiplying these symbols verifies, including all signs:
  - if `2 notin U`, the count `u` of primes `3 mod 4` is `0 or 1 mod 4`;
  - if `2 in U`, `v+binom(u,2)` is even, where `v` counts odd primes
    `3 or 5 mod 8`.
- The `r=2` congruence is explicitly separated; no Legendre symbol with
  denominator 2 is used.
- Partition-dependent and union-only mod-8 conditions are proved.  When 3 is
  absent, they lift to stronger mod-24 conditions.
- An exact enumeration rules out a 59-prime union: 49,961 sets have enough
  reciprocal mass, 6,149 survive the cheap mod-8 and aggregate reciprocity
  filters, and none satisfies all local Legendre conditions.  Hence
  `|P union Q|>=60`, matching the current database statement.
- A slow exact enumeration checks 644,666 possible unions supported on the
  first 66 primes.  A separately formulated cached-symbol enumeration extends
  this to the first 68 primes: 9,926,250 reciprocal-feasible unions are checked
  and none passes the local conditions.  Thus `max(P union Q)>=347`, without
  claiming novelty.
- **2026-10-24 update.**  A meet-in-the-middle search extends the
  bounded-support exclusion to the first 90 primes: no union contained in the
  primes up to 463 passes the reciprocal-mass, cardinality and local Legendre
  conditions, so `max(P union Q)>=467`.  A separately written second
  implementation reproduces the frontier counts, and its brute-force mode
  checks every candidate union directly through 76 primes.
- The same update re-runs the 59-prime exclusion with the second
  implementation (now in CI) and formalizes the forcing identities, the local
  square/Legendre condition, the mod-8/mod-24 and parity conditions, and the
  bound `|P union Q|>=59` in Lean 4 (`AgenticConjectures/Erdos307.lean`,
  kernel-checked without `native_decide`).

The full argument is in `PROOF.md`.

## Bounded support to 90 primes (2026-10-24)

**Result.**  Let `F_90` be the first 90 primes, `2,...,463`.  No set
`U ⊆ F_90` satisfies all of

1. `sum_{r in U} 1/r >= 2`,
2. `|U| >= 60`,
3. for every odd `r in U`, `prod_{s in U, s != r} (s|r) = 1`.

Every solution `(P,Q)` gives such a `U=P union Q`: condition 1 and condition 3
are Lean theorems (`two_lt_sum_inv_union`, `prod_jacobiSym_eq_one`), and
condition 2 is the exact 59-prime exclusion.  Hence every solution contains a
prime `>= 467`, the next prime after 463.  This replaces the previous
computational bound `max(P union Q)>=347`.

**Method.**  `support_mitm.cpp` (C++17, `std::thread`) enumerates removal sets
`R=F_90-U` in integer arithmetic.  Condition 3 is linear over GF(2), so the
search fixes it first on the 33 smallest odd primes (the *key*), combining two
half-tables of removable primes by key lookup, and then tests the full
condition on every key-matched set.  The reduction, the budget arithmetic and
why each removal set is produced exactly once are written out in `PROOF.md`,
section 6, "Meet-in-the-middle extension to 90 primes".

| `K` | largest prime | key size | key-matched removal sets | survivors | wall time |
|---:|---:|---:|---:|---:|---:|
| 80 | 409 | 30 | 16,626 | 0 | 2.9 s (1 thread) |
| 84 | 433 | 30 | 1,054,762 | 0 | 33.6 s (1 thread) |
| 86 | 443 | 31 | 4,454,518 | 0 | 119.7 s (1 thread) |
| 88 | 457 | 32 | 18,447,093 | 0 | 171.4 s (3 threads) |
| 90 | 463 | 33 | 75,000,754 | 0 | 752.7 s (3 threads) |

No run reported an ambiguous budget case, so the key-matched counts are exact.
The `K=88` and `K=90` runs were made on a shared 18-core Apple machine under
heavy load (load average 40–70); the `K=90` run used 1,542 s of CPU time and
3.4 GB of memory.  The `K=80`–`86` rows are single-threaded re-runs on the
same machine at lower load.

**Cross-checks.**  `cross_check_support.py` is a separately written
implementation (numba).  It uses quadratic-residue tables, row bitsets, exact
`Fraction` budgets, sorted tables, the opposite half split and a different
weight boundary.

- `brute` mode enumerates every removal set without keys.  It reproduces the
  exact totals 644,666 (`K=66`) and 9,926,250 (`K=68`) of the earlier scripts
  and checks all 128,295,786,172 candidate unions for `K=76` in 529 s
  (3 threads).  It finds no survivor, which independently gives
  `max(P union Q)>=389`.
- For every even `K` from 66 to 76 and every key size in `{12,16,20,24,30}`,
  the key-matched counts of `brute` and `support_mitm.cpp` agree exactly
  (30 comparisons).
- `mitm` mode reproduces the `K=84` and `K=90` key-matched counts and their
  distributions by `|R|`, and finds no survivor (`K=90`: 1,578 s with 3
  threads under load, 6.9 GB).
- `fiftynine` mode re-enumerates the 49,961 reciprocal-feasible 59-prime
  unions (same counts by number of replacements as `enumerate_59.py`) and
  confirms that none passes the local conditions.

All counts and timings are recorded in `bounded_support_90_result.json`.

**Not claimed.**  This is a finite computer exclusion, not a nonexistence
proof.  It depends on the exact 59-prime enumeration for `|U|>=60`.  The two
search implementations share the mathematical reduction and the
meet-in-the-middle design.  The brute-force mode, which is a different
algorithm, only reaches 76 primes.  Pushing `|P union Q|>=61` by the same
method is not possible: the reciprocal-mass condition alone does not bound the
largest prime of a 60-prime union, so that case has no finite candidate list.
No novelty is claimed for either bound.

## Reproduction

Run the exact randomized/toy audit:

```bash
python3 problems/erdos-307/test_identities.py
```

It deterministically checks 2,000 random prime reciprocity identities, 1,000
pairwise-coprime composite Jacobi identities (half containing 2), 2,000 exact
forcing equivalences, and three generalized toy solutions.  The largest toy
contains the genuinely composite denominator `1805=5*19^2`:

\[
\left(1+\frac1{1805}\right)
\left(\frac12+\frac13+\frac17+\frac1{43}\right)=1.
\]

Run the finite exclusion:

```bash
python3 problems/erdos-307/enumerate_59.py
python3 problems/erdos-307/enumerate_bounded_union.py
python3 problems/erdos-307/enumerate_bounded_support_fast.py \
  --prime-count 68
```

The scripts use only the Python standard library and exact integer/Fraction
arithmetic.  Expected digests are summarized in `enumeration_59_result.json`,
`bounded_union_result.json`, and `bounded_support_68_result.json`.  At 66
primes the slow product-based and cached-bitset implementations give identical
counts in every column.  The 67-prime cached result was also reproduced by the
slow implementation; 5,000 deterministic 68-prime subsets were checked by
both local-symbol formulas.

Run the 90-prime exclusion and its cross-checks (from `problems/erdos-307`;
the `brute` and `mitm` modes need numpy and numba):

```bash
mkdir -p build && g++ -O3 -std=c++17 -pthread support_mitm.cpp -o build/support_mitm
build/support_mitm 80 --threads 2               # seconds; also run by CI
build/support_mitm 90 --key 33 --threads 3      # ~13 min under load, 3.4 GB
python3 cross_check_support.py fiftynine        # 0.7 s, standard library only; CI
python3 cross_check_support.py brute --K 76 --keys 12,16,20,24,30 --threads 3  # 529 s
python3 cross_check_support.py mitm --K 90 --key 33 --threads 3     # ~26 min, 6.9 GB
```

Each command prints one JSON object and exits with status 0 exactly when there
is no survivor.

Check a proposed prime pair, for example:

```bash
python3 problems/erdos-307/exact_checker.py \
  --P 2,5,11 --Q 3,7,13
```

The report includes exact reciprocal sums, forcing identities, every cross
congruence and local Legendre symbol, reciprocity counts, parity, mod-8,
conditional mod-24, and the known union square identity.

## FormalConjectures upstream

The exact Lean statement and immutable source metadata are preserved in the
local [upstream snapshot](upstream/README.md).  Its main declaration remains a
`sorry`-backed open statement; the stronger finite exclusions here do not
settle it.

## Lean formalization

`AgenticConjectures/Erdos307.lean` proves the elementary necessary conditions
for every witness of the upstream statement.  Here `M S = ∏ p ∈ S, p` and
`A S = ∑ p ∈ S, ∏ q ∈ S.erase p, q`, so `∑ p ∈ S, 1/p = A S / M S`.

| Declaration | Statement |
|---|---|
| `statement` | the right-hand side of upstream `erdos_307`, verbatim |
| `IsSolution P Q` | the body of that existential |
| `forcing`, `isSolution_of_forcing` | `IsSolution P Q ↔` (primes and `A P = M Q ∧ A Q = M P`) |
| `statement_iff_forcing` | `statement ↔ ∃ P Q`, primes with `A P = M Q ∧ A Q = M P` |
| `disjoint_of_isSolution` | `Disjoint P Q` |
| `union_identity` | `A (P ∪ Q) = M P ^ 2 + M Q ^ 2` |
| `two_lt_sum_inv_union` | `2 < ∑ r ∈ P ∪ Q, 1/r` |
| `isSquare_prod_erase` | for `r ∈ P ∪ Q`, `∏ ((P ∪ Q).erase r)` is a nonzero square in `ZMod r` |
| `prod_jacobiSym_eq_one` | `∏ s ∈ (P ∪ Q).erase r, J(s \| r) = 1` |
| `even_card_nonresidues` | an even number of `s ∈ (P ∪ Q).erase r` have `J(s \| r) = -1` (the search's pruning rule) |
| `sum_cast_eq_M`, `sum_cast_eq_of_two_mem` | (8a)–(8d) for any modulus in which the primes square to 1 |
| `mod_eight`, `mod_eight_of_two_mem` | (8a)–(8d) modulo 8 |
| `mod_twentyFour`, `mod_twentyFour_of_two_mem` | the mod-24 conditions when `3 ∉ P ∪ Q` |
| `odd_card_of_two_not_mem`, `even_card_of_two_mem` | the parity restrictions |
| `card_union_ge_59` | `59 ≤ #(P ∪ Q)` |

The case `2 ∈ Q` follows from `IsSolution.symm`.  The `59` bound compares any
58 primes with the first 58 primes and evaluates `∑ 1/p < 2` for the latter
as a natural-number inequality with `decide +kernel`; there is no
`native_decide`.  `#print axioms` shows only `propext`, `Classical.choice` and
`Quot.sound`.

**Statement faithfulness.**  `statement` and `IsSolution` copy the upstream
proposition exactly: `Finset ℕ` witnesses, `Nat.Prime` membership hypotheses
and the equation `1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)` in `ℚ`.
No other definitions or boundary conventions are involved, and every theorem
is a consequence of that equation.  `card_union_ge_59` is the left conjunct of
the upstream `erdos_307.barrier`.  Upstream also assumes `Q.Nonempty`, which
the equation already implies; the right conjunct, a lower bound for `∏ P`, is
not formalized here.  The `answer(sorry)` of `erdos_307` is untouched.  The
computational bounds `|P union Q|>=60` and `max(P union Q)>=467` are not
formalized.

## AlphaProof Nexus benchmark provenance

Google DeepMind's AlphaProof Nexus `science-submission` snapshot at commit
[`0647711a71183c1ea492ad60860776617ce1ea88`](https://github.com/google-deepmind/alphaproof-nexus-results/tree/0647711a71183c1ea492ad60860776617ce1ea88)
lists both `erdos_307` and
`erdos_307.variants.coprime_one_notMem` in its immutable
[attempted-problems list](https://github.com/google-deepmind/alphaproof-nexus-results/blob/0647711a71183c1ea492ad60860776617ce1ea88/erdos_problems_attempted.txt).
At that snapshot neither `APNOutputs/ErdosProblems` nor
`NaturalLanguageProofs/ErdosProblems` contains a result for #307.  This is
therefore attempt provenance, not a proof or counterexample.  In particular,
all three pairwise-coprime composite toy solutions checked here contain `1`,
so they do not settle the variant requiring `1 notin P union Q`.

## Literature audit

Primary and near-primary sources checked:

- Erdős and Graham's 1980 monograph states the question at the bottom of
  printed page 38 and attributes it to Barbeau:
  <https://www.math.ucsd.edu/~ronspubs/80_11_number_theory.pdf>
- The current problem page lists it as open and states `|P union Q|>=60`:
  <https://www.erdosproblems.com/307>
- I. O. Bado, *Structural Constraints for an Erdős Unit-Fraction Problem over
  Primes*, author-uploaded preprint, May 2026, DOI
  `10.13140/RG.2.2.32245.54245`:
  <https://www.researchgate.net/publication/404719794_STRUCTURAL_CONSTRAINTS_FOR_AN_ERDOS_UNIT-FRACTION_PROBLEM_OVER_PRIMES>
  It already contains the forcing theorem, cross-product/local zero-sum
  congruences, parity restrictions, exact one-sided test, and union
  discriminant/Pythagorean identity.  It is a preprint and the page reports no
  citations.
- A 2019 MathOverflow discussion records the monograph location and the raw
  reciprocal-sum lower bound `|U|>=59`:
  <https://mathoverflow.net/questions/320838/product-of-sum-of-reciprocals-of-prime-numbers>

Exact-phrase searches for this problem together with “Legendre symbol”,
“quadratic reciprocity”, and “mod 8” found no additional relevant primary
source as of 2026-08-11.  This is limited evidence only: the reciprocity,
mod-8, mod-24, and enumerative formulations must not be called new without a
broader expert literature review.
