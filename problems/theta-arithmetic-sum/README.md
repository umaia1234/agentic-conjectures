**English** | [한국어](README.ko.md)

# Theta arithmetic sum: exact formulas, an upper bound and a check to 2·10⁶

For integers $h,k\ge1$ put

\[
S'(h,k)=\sum_{j=1}^{k-1}(-1)^{j+1+\lfloor hj/k\rfloor},\qquad
S(k)=\sum_{h=1}^{k-1}S'(h,k).
\]

B. C. Berndt, R. N. Bhat, J. L. Meyer, L. Xie and A. Zaharescu, *An arithmetic sum associated
with the classical theta function* ([arXiv:2501.03234](https://arxiv.org/abs/2501.03234);
Results Math. 81, no. 1, [doi:10.1007/s00025-025-02584-2](https://doi.org/10.1007/s00025-025-02584-2)),
write $S(h,k)$ for $S'(h,k)$; it is one of Berndt's Hardy sums. Their main conjecture
(Conjecture 1.1 of arXiv v1) reads:

> “If $k$ is an odd prime, then $S(k)>0$.”

The upstream formalization also states their Conjectures 4.1–4.4 (numbering of v1): for odd
primes $k$, $S(k)>k$ when $k>5$, $S(k)>2k$ when $k>233$, $S(k)>3k$ when $k>3119$, and, for
every $n$, $S(k)>nk$ for all sufficiently large $k$. Conjecture 3.3 first appears in arXiv v2;
v3 has the same text (p. 4). It is not in the upstream file, which follows v1:

> “Let $C_1$ and $C_2$ be any fixed positive numbers. Let $\epsilon>0$ be fixed. Then, for all
> primes $k$ sufficiently large, $C_1k<S(k)<C_2k^{1+\epsilon}$.”

So both inequalities should hold, for all sufficiently large primes $k$, for every
$C_1,C_2>0$ and every $\varepsilon>0$. Because $C_1$ is arbitrary, the first inequality is
equivalent to Conjecture 4.4 (Lean: `statement_3_3_lower_iff`).

## Verdict

**Partial.** None of the five upstream conjectures is resolved, and of Conjecture 3.3 only the
second inequality is proved, on paper. This directory adds three things.

1. **Lean (kernel-checked).**
   - Exact reductions of $S(k)$ for prime $k$.
   - The exact formula $S(k)=kH(k)-\tfrac{k-1}2+2V(k)$ for every odd prime $k$ (Theorem 4.3
     of [DETAILS.md](DETAILS.md)). Here $H(k)=\sum_{v\text{ odd},\,v\le k-2}1/v$, so
     $kH(k)=\tfrac12k\ln k+O(k)$, and $V(k)$ is a sum of Hardy sums. Every conjecture becomes
     a lower bound on $V(k)$; for Conjecture 1.1, Lean proves the equivalence.
   - Conjectures 1.1, 4.1 and 4.2 for every odd prime $k<300$.
   - A statement of Conjecture 3.3, with proofs that it is the conjunction of its two
     inequalities and that the first is equivalent to Conjecture 4.4. Neither inequality is
     proved in Lean.
2. **Mathematics (pen and paper, not machine-checked).** See [DETAILS.md](DETAILS.md).
   - The exact error term of the paper's lower bound (Proposition 5.1) and the exact divisor
     terms (Proposition 6.1).
   - The unconditional bound $|S(k)|<6k(1+\ln k)^2+8k$ for every odd prime $k$
     (Theorem 7.1). It proves the second inequality of Conjecture 3.3.
   - A character-sum form of $S(k)$ (Proposition 8.1).

   None of these proofs is formalized. Theorem 7.1 was reviewed independently: a separate AI
   review re-derived every step and found no gap. CI re-checks only the numerics: `verify.py`
   checks each step of Theorem 7.1 for every prime $k\le400$ and the bound on every row of the
   table, and the other identities on small ranges.
3. **Computation.** $S(k)$ for every odd prime $k\le2\cdot10^6$ by two different
   $O(k\log k)$ algorithms, which agree everywhere, and by the literal definition for every
   prime $k\le30000$ and every $k\le10000$. No odd prime $k\le2\cdot10^6$ violates
   Conjecture 1.1, 4.1, 4.2 or 4.3.

The upper bound is the only statement here that settles part of a published conjecture. Its
proof uses classical facts about Dedekind sums (DETAILS, Section 7) and is not machine-checked:
Lean states the inequality (`statement_3_3_upper`) but does not prove it. We have not seen the
bound stated, but this is not a claim of novelty.

## Source statements and prior-art check

- **Paper.** arXiv v1 (10 Dec 2024), v2 (2 Dec 2025) and v3 (9 Jan 2026); the texts of v2 and
  v3 differ only in the arXiv stamp. We cite v1 and v3 numbering; the upstream file follows
  v1. We did not check the journal version, which may number results differently.
  The paper proves elementary properties of $S'(h,k)$ and $S(k)$, among them $S'(h,k)=0$ for
  odd $h$ and prime $k$ (Lemma 5.7 of v1, Proposition 7.5 of v3). It also proves a lower bound
  (Theorem 6.4 of v1, Theorem 6.3 of v3) that is negative for large $k$. It computed $S(k)$
  for every $k\le10^4$ and every prime $k\le5\cdot10^4$.
- **Upstream formalization.**
  [`ArithmeticSumS.lean`](upstream/ArithmeticSumS.lean), from google-deepmind/formal-conjectures
  at commit `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`; see [upstream/README.md](upstream/README.md).
  All five conjectures close with `sorry` there.
- **Literature check (2026-10-24).** The arXiv listing, an OpenAlex full-text search and the
  paper's references show no work on $S(k)$ beyond the paper itself, and OpenAlex lists no
  citing works. $S'(h,k)$, $s_3$ and $s_4$ are Hardy sums, studied by Berndt (1978), Goldberg
  (1981), Berndt and Goldberg (1984) and Sitaramachandrarao (1987). Their mean values have been
  studied too, for example power means and hybrid means with Ramanujan sums (Zhang, 2003;
  Dağlı, 2020), but we found no evaluation of the plain sum over $h$. Known results used here:
  - Sitaramachandrarao's expression of $S'(h,k)$ through Dedekind sums gives the Dedekind form
    (D) of DETAILS at once.
  - The reciprocity law in Section 4 of DETAILS is of the same classical kind.
  - Zhang's character expansion of $S'(h,k)$ gives the character form of Section 8.

  We read Zhang (2003) and Dağlı (2020), but not the older papers themselves. Every formula
  quoted from them is checked numerically by `verify.py`. The continued-fraction formula
  (BHK) for Dedekind sums, which Theorem 7.1 uses, is attributed to Barkan, Hickerson and
  Knuth (1977); DETAILS proves it from Dedekind reciprocity instead of relying on those papers.
- Nothing here has been reported to the authors, to formal-conjectures or elsewhere.

## Lean results

Module [`ThetaArithmeticSum.lean`](../../AgenticConjectures/ThetaArithmeticSum.lean),
namespace `AgenticConjectures.ThetaArithmeticSum`. No `sorry`, no extra axioms, no
`native_decide`. The two kernel evaluations use `decide +kernel`.

| Declaration | Statement |
|---|---|
| `S'`, `S` | the upstream definitions, copied term for term |
| `statement_1_1`, `statement_4_1` … `statement_4_4` | the five upstream conjectures, as `Prop`s (not proved) |
| `floor_eq` | the $\mathbb Q$-floor in `S'` equals the natural-number quotient `h * j / k` |
| `S'_eq` | `S'` with that quotient in place of the floor |
| `S'_eq_zero_of_odd` | `S' h k = 0` for odd `h < k`, `k` an odd prime |
| `S'_sub_eq_s4` | `S' (k - v) k = s4 v k` for `0 < v < k`, `k` prime, where `s4 v k = ∑_{j=1}^{k-1} (-1)^⌊vj/k⌋` |
| `s4_eq_zero_of_even` | `s4 v k = 0` for even `0 < v < k`, `k` prime |
| `S_eq_sum_s4`, `S_eq_sum_sq` | `S k = ∑_{v=1}^{k-1} s4 v k = ∑_{a,b=1}^{k-1} (-1)^⌊ab/k⌋` for prime `k` |
| `S_eq_sum_odd` | `S k = ∑_{v<k, v odd} s4 v k` for prime `k` |
| `s4_eq_two_mul` | `s4 v k = 2 ∑_{j=1}^{(k-1)/2} (-1)^⌊vj/k⌋` for odd `v < k`, `k` an odd prime |
| `S_eq_fastS` | `S k = fastS k` for odd primes `k`, where `fastS` is a structurally recursive evaluation |
| `small_primes` | `0 < S k`, `k > 5 → k < S k` and `k > 233 → 2k < S k` for every odd prime `k < 300` |
| `S_fst_10` | the upstream test `List.map S (List.range 10) = [0, 0, 1, 2, 5, 4, 7, 10, 11, 8]` |
| `s3`, `H`, `V` | the Hardy sum $s_3(c,v)=\sum_{i=1}^{v-1}(-1)^i((ci/v))$, written with `c * i % v`; $H(k)$ and $V(k)$ as sums over odd $v<k$ |
| `s4_eq_reciprocity` | `s4 v k = k/v - 1 + 2 s3 (k % v) v` for odd `v` coprime to `k > 0` (Proposition 4.1) |
| `S_eq_exact` | `S k = k H(k) - (k - 1)/2 + 2 V(k)` for odd primes `k` (Theorem 4.3) |
| `statement_1_1_iff` | `statement_1_1 ↔ ∀ k, k.Prime → Odd k → (k - 1)/2 - k H(k) < 2 V(k)` |
| `statement_3_3`, `statement_3_3_lower`, `statement_3_3_upper` | Conjecture 3.3 of v2/v3 and its two inequalities, as `Prop`s (not upstream; not proved) |
| `statement_3_3_iff` | `statement_3_3 ↔ statement_3_3_lower ∧ statement_3_3_upper` |
| `statement_3_3_lower_iff` | `statement_3_3_lower ↔ statement_4_4` |

`small_primes` is a finite check. It covers the thresholds $5$ and $233$ of Conjectures 4.1
and 4.2, but proves none of the conjectures. `S_eq_exact` and `statement_1_1_iff` hold for
every odd prime; they turn Conjecture 1.1 into a lower bound on $V(k)$ but do not prove it.
`statement_3_3_upper` is the inequality that Theorem 7.1 settles on paper; Lean states it but
does not prove it.

## Computation

| Program | Formula | Cost per $k$ |
|---|---|---|
| [`s_dedekind.cpp`](s_dedekind.cpp) (A) | Dedekind form (D), continued-fraction evaluation (BHK) of Dedekind sums | $O(k\log k)$, exact `__int128` |
| [`s_hardy.cpp`](s_hardy.cpp) (B) | $\sum_{v\text{ odd}}s_4(v,k)$ with the reciprocity law (4.1) and Dedekind reciprocity | $O(k\log k)$, exact `int64_t` with overflow checks |
| [`s_literal.cpp`](s_literal.cpp) (C) | the definition | $O(k^2)$ |

Runs on an Apple M5 Max, one thread per job (logs in [`logs/`](logs/)); CPU times, for the
reason given in DETAILS, Section 9:

| Run | Range | CPU time |
|---|---|---|
| A | odd primes $3\le k\le10^6$ | 2055 s |
| B | odd primes $3\le k\le10^6$ | 1882 s |
| A | odd primes $10^6<k\le2\cdot10^6$ (two segments) | 2406 s + 3347 s |
| B | odd primes $10^6<k\le2\cdot10^6$ (two segments) | 2211 s + 3055 s |
| C | primes $k\le30000$ | 446 s |
| C | every $k\le10000$ | 162 s |

Results:

- A and B agree on every odd prime $k\le2\cdot10^6$; C agrees with them on every prime
  $k\le30000$.
- No odd prime $k\le2\cdot10^6$ violates Conjecture 1.1, 4.1, 4.2 or 4.3, or the bound of
  Theorem 7.1.
- The minimum of $S(k)/k$ over primes $k>5$ is $14/11$, at $k=11$. The largest prime with
  $S(k)\le3k$ is $3119$, as in the paper; the largest with $S(k)\le4k$ is $58013$, and the
  largest with $S(k)\le5k$ is $869399$. $S(k)\le6k$ still occurs at $k=1999619$.
- $E(k)=S(k)/k-\tfrac12\ln k$ stays within $[-2.2,2.4]$ for primes $10^3<k\le2\cdot10^6$.
  Both extremes occur where $2k-1$ or $2k+1$ is divisible by several small numbers, as
  Proposition 6.1 suggests.
- For $k\le10^4$, C reproduces the paper's count of 151 negative values (all at composite
  $k$), its lists of the 17 primes with $S(k)<2k$ and the 87 primes with $S(k)\le3k$, and the
  composite values it quotes.

Data: [`data/S_odd_primes.txt`](data/S_odd_primes.txt) (every odd prime $k\le2\cdot10^6$,
methods A and B) and [`data/S_all_k_le_10000.txt`](data/S_all_k_le_10000.txt) (every
$k\le10000$, method C), one `k S(k)` pair per line.

## Discrepancies in the paper

- Table 1 (v1 and v3) is shifted by one from $k=9$ on: for $9\le k\le20$ it prints $S(k-1)$
  in place of $S(k)$, so $11$ appears twice and $S(20)=29$ is missing. For example, it gives
  $S(9)=11$ and $S(17)=39$, but the definition gives $S(9)=8$ and $S(17)=24$. The correct
  values of $S(1),\dots,S(20)$ are 0, 1, 2, 5, 4, 7, 10, 11, 8, 17, 14, 21, 20, 15, 18, 39,
  24, 21, 38, 29. The upstream test `S_fst_10` agrees with the definition, and so do the
  paper's own lists: $17$ is listed among the primes with $S(k)<2k$.
- Section 3 of v3 says that for primes $k\le50000$ there are 8 pairs violating $S(k)>4k$, and
  lists them. Those 8 are exactly the primes in $(30000,50000]$ with $S(k)\le4k$. There are 79
  such primes in $(10^4,5\cdot10^4]$ and 508 odd primes up to $5\cdot10^4$. The sentence
  presumably refers to the range above 30000.

## Statement faithfulness

- `S'` and `S` are copied from the upstream file term for term, including the
  $\mathbb Q$-valued floor `⌊(h * j : ℚ) / k⌋₊`. `floor_eq` proves that it equals the
  natural-number quotient used by every program here.
- `Finset.Ico 1 k` is $\{1,\dots,k-1\}$, matching the paper's ranges $1\le j,h\le k-1$. For
  $k\le1$ the sums are empty, so `S 0 = S 1 = 0`; no statement uses these values.
- Each `statement_*` is the proposition of the upstream `conjecture_*`, with the same
  hypotheses `k.Prime → Odd k → …` and the same `ℕ → ℤ` coercions in `k < S k`,
  `2 * k < S k`, …. `Odd k` excludes $k=2$, as the paper's "odd prime" does.
- v1 states Conjectures 4.2 and 4.3 as "for $k>233$" and "for $k>3119$"; the context, v3 and
  upstream make $k$ an odd prime. v3 states Conjecture 1.1 for odd primes $k>5$; this is
  equivalent, since $S(3)=2$ and $S(5)=4$.
- `statement_4_4` reads `∀ n, ∀ᶠ k in atTop, k.Prime → Odd k → n * k < S k`, which is "for
  all primes $k$ sufficiently large, depending on $n$".
- `statement_3_3` has no upstream counterpart; it formalizes the text of v3 quoted above. It
  reads `∀ C₁ C₂ ε : ℝ, 0 < C₁ → 0 < C₂ → 0 < ε → ∀ᶠ k in atTop, k.Prime →
  C₁ * k < S k ∧ S k < C₂ * k ^ (1 + ε)`, with `k` and `S k` cast to ℝ and the real power
  `k ^ (1 + ε)`. "Any fixed" is read as "for every", and $k$ runs over all primes, as in the
  text ($k=2$ does not matter for "sufficiently large"). `statement_3_3_lower` and
  `statement_3_3_upper` are the two inequalities with the same quantifiers; the threshold may
  depend on all the constants in each.
- `s3 c v` writes the sawtooth $((ci/v))$ as `(c * i % v)/v - 1/2`. The two agree when
  $v\nmid ci$, so for every $i$ in the sum when $\gcd(c,v)=1$, the only case used. For odd
  $k$, `H k` and `V k` are the $H(k)$ and $V(k)$ of DETAILS; `V` also has the term $v=1$,
  which is $0$.

## Reproduction

From this directory:

```bash
python3 verify.py
```

This is the CI check (about 15 s; needs `g++` and Python 3 with `mpmath`, which comes with
`sympy`, as in CI). It checks every identity used, exactly, on small ranges, and each step of
Theorem 7.1 for every prime $k\le400$; recomputes the table with programs A and B for every odd
prime $k\le50000$ and with C for every prime $k\le2500$ and every $k\le1500$; and audits both
tables in full (conjectures, the bound of Theorem 7.1, the paper's lists).

```bash
python3 verify.py --full
```

This reruns A and B over the whole table and C for every prime $k\le30000$ and every
$k\le10000$. It takes several hours.

To regenerate the prime table directly:

```bash
g++ -O3 -std=c++17 s_dedekind.cpp -o s_dedekind && ./s_dedekind 3 2000000 > A.txt
```

and the same with `s_hardy.cpp` for method B; `s_literal lo hi all` gives every $k$ in a
range.

## What is not claimed

- No conjecture of the paper is proved or refuted, except the second inequality of
  Conjecture 3.3 (Theorem 7.1). That proof is pen-and-paper and not machine-checked. It was
  reviewed independently (one separate AI review, which found no gap), and CI re-checks only
  its numerics. Lean states the inequality (`statement_3_3_upper`) but does not prove it.
- Apart from Proposition 4.1 and Theorem 4.3 (Lean), the identities of DETAILS Sections 3–8
  are not formalized either. `verify.py` checks them exactly on small ranges (Proposition 8.1
  in floating point), and the agreement of methods A, B and C checks them on the whole
  computed range.
- The computation is evidence, not proof, beyond the range it covers.

## Files

- [DETAILS.md](DETAILS.md): definitions, proofs, the upper bound, the computation and
  references.
- [`verify.py`](verify.py): the CI check described above.
- [`s_dedekind.cpp`](s_dedekind.cpp), [`s_hardy.cpp`](s_hardy.cpp),
  [`s_literal.cpp`](s_literal.cpp): methods A, B and C.
- [`data/`](data/): the two tables; [`logs/`](logs/): run logs.
- [`upstream/`](upstream/): the byte-exact upstream Lean file and its provenance.
