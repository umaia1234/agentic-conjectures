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

The full argument is in `PROOF.md`.

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
