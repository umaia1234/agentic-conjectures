import Mathlib

/-!
# An arithmetic sum associated with the classical theta function

Canonical source: B. C. Berndt, R. N. Bhat, J. L. Meyer, L. Xie, A. Zaharescu, *An arithmetic sum
associated with the classical theta function*, [arXiv:2501.03234](https://arxiv.org/abs/2501.03234).
Upstream formalization: `FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean` at
formal-conjectures commit `c094b979118b89adb77cf5f8d923ac9dd2e51b1d` (byte-exact snapshot in
`problems/theta-arithmetic-sum/upstream/`).

For `S' h k = ∑_{j=1}^{k-1} (-1)^(j + 1 + ⌊hj/k⌋)` and `S k = ∑_{h=1}^{k-1} S' h k`, the paper
conjectures `0 < S k` for every odd prime `k` (Conjecture 1.1; the main statement here is
`statement_1_1`), and the lower bounds `k < S k` for `k > 5`, `2k < S k` for `k > 233`,
`3k < S k` for `k > 3119`, and `nk < S k` for all large `k` (Conjectures 4.1–4.4,
`statement_4_1` … `statement_4_4`; numbering of arXiv v1, as upstream). arXiv v2 and v3 add
Conjecture 3.3: for every `C₁, C₂, ε > 0`, `C₁ k < S k < C₂ k^(1+ε)` for all large primes `k`
(`statement_3_3`, with its two inequalities `statement_3_3_lower` and `statement_3_3_upper`).

## Upstream correspondence

`S'` and `S` are copied term for term, including the `ℚ`-valued floor. Each `statement_*` is the
proposition of the upstream theorem `conjecture_*`, with the theorem's explicit arguments turned
into universally quantified variables in the same order; the coercions `ℕ → ℤ` in `k < S k`,
`2 * k < S k`, … are elaborated exactly as upstream. The only adaptations are those needed to
compile without the FormalConjectures utilities: the `module` / `public import
FormalConjecturesUtil` / `@[expose] public section` header is replaced by `import Mathlib`, the
`category`/`AMS` attributes are dropped, and the namespace `Arxiv.«2501.03234»` becomes
`AgenticConjectures.ThetaArithmeticSum`.

`statement_3_3`, `statement_3_3_lower` and `statement_3_3_upper` have no upstream counterpart: the
upstream file follows arXiv v1, which has no Conjecture 3.3. They are formalized here from the
text of v3, quoted in the docstring of `statement_3_3`.

## Results

No conjecture is proved here: neither the five upstream ones nor either inequality of
Conjecture 3.3 (`DETAILS.md` proves the second inequality on paper only). The module proves, for
a prime `k`, the exact reductions used by the fast algorithms in the problem directory and the
exact formula of `problems/theta-arithmetic-sum/DETAILS.md` (Section 4), checks small cases, and
relates the statements:

* `floor_eq`: the `ℚ`-floor in `S'` equals natural-number division `h * j / k`.
* `S'_eq_zero_of_odd`: `S' h k = 0` for odd `h < k` when `k` is an odd prime (the case of
  Lemma 5.7 of arXiv v1, Proposition 7.5 of v3, used here).
* `S'_sub_eq_s4`: `S' (k - v) k = s4 v k`, where `s4 v k = ∑_{j=1}^{k-1} (-1)^⌊vj/k⌋`.
* `s4_eq_zero_of_even`: `s4 v k = 0` for even `0 < v < k`.
* `S_eq_sum_s4`, `S_eq_sum_sq`: `S k = ∑_{a=1}^{k-1} ∑_{b=1}^{k-1} (-1)^⌊ab/k⌋`.
* `S_eq_sum_odd`: `S k = ∑_{v odd} s4 v k`, the form evaluated by the reciprocity algorithm.
* `s4_eq_two_mul`: `s4 v k = 2 * ∑_{j=1}^{(k-1)/2} (-1)^⌊vj/k⌋` for odd `v` and odd prime `k`.
* `S_eq_fastS`: `S k = fastS k`, a structurally recursive evaluation of the last two forms.
* `small_primes`: Conjectures 1.1, 4.1 and 4.2 hold for every odd prime `k < 300` (kernel
  evaluation of `fastS`, `fastS_small`).
* `S_fst_10`: the upstream test `List.map S (List.range 10) = [0, 0, 1, 2, 5, 4, 7, 10, 11, 8]`.
* `s4_eq_reciprocity`: `s4 v k = k/v - 1 + 2 s₃(k mod v, v)` for odd `v` coprime to `k > 0`,
  where `s₃ = s3` is a Hardy sum (Proposition 4.1 of `DETAILS.md`).
* `S_eq_exact`: `S k = k H(k) - (k - 1)/2 + 2 V(k)` for an odd prime `k`, with
  `H(k) = ∑_{v odd, v < k} 1/v` and `V(k) = ∑_{v odd, v < k} s₃(k mod v, v)` (Theorem 4.3).
* `statement_1_1_iff`: Conjecture 1.1 is equivalent to `(k - 1)/2 - k H(k) < 2 V(k)` for every
  odd prime `k`.
* `statement_3_3_iff`: Conjecture 3.3 is the conjunction of its two inequalities.
* `statement_3_3_lower_iff`: its first inequality is equivalent to Conjecture 4.4.
-/

namespace AgenticConjectures.ThetaArithmeticSum

open Finset

section SumS

open Nat Finset BigOperators in
/--
Define the sum
$$S'(h, k) := \sum_{j=1}^{k-1}(-1)^{j + 1 + \lfloor \frac{hj}{k}\rfloor}.$$
(Copied term for term from upstream.)
-/
def S' (h k : ℕ) : ℤ := ∑ j ∈ Finset.Ico 1 k, (-1 : ℤ) ^ (j + 1 + ⌊(h * j : ℚ) / k⌋₊)

/--
Define the sum
$$S(k) := \sum_{h=1}^{k-1}S'(h, k)$$
(Copied term for term from upstream.)
-/
def S (k : ℕ) : ℤ := ∑ h ∈ Finset.Ico 1 k, S' h k

end SumS

/-- **Conjecture 1.1** (main statement): `S k` is positive for every odd prime `k`. -/
def statement_1_1 : Prop := ∀ (k : ℕ), k.Prime → Odd k → 0 < S k

/-- **Conjecture 4.1**: `k < S k` for every odd prime `k > 5`. -/
def statement_4_1 : Prop := ∀ (k : ℕ), k.Prime → Odd k → k > 5 → k < S k

/-- **Conjecture 4.2**: `2k < S k` for every odd prime `k > 233`. -/
def statement_4_2 : Prop := ∀ (k : ℕ), k.Prime → Odd k → k > 233 → 2 * k < S k

/-- **Conjecture 4.3**: `3k < S k` for every odd prime `k > 3119`. -/
def statement_4_3 : Prop := ∀ (k : ℕ), k.Prime → Odd k → k > 3119 → 3 * k < S k

/-- **Conjecture 4.4**: for every `n`, `n * k < S k` for all sufficiently large odd primes `k`. -/
def statement_4_4 : Prop :=
  ∀ (n : ℕ), ∀ᶠ (k : ℕ) in Filter.atTop, k.Prime → Odd k → n * k < S k

/--
**Conjecture 3.3** of arXiv v2 and v3 (p. 4 of v3; v2 has the same text). It is not in the
upstream file, which follows v1. The paper states: "Let $C_1$ and $C_2$ be any fixed positive
numbers. Let $\epsilon > 0$ be fixed. Then, for all primes $k$ sufficiently large,
$$C_1 k < S(k) < C_2 k^{1+\epsilon}."$$
Since the constants are arbitrary, this is the conjunction of `statement_3_3_lower` and
`statement_3_3_upper` (`statement_3_3_iff`). Not proved here.
-/
def statement_3_3 : Prop :=
  ∀ C₁ C₂ ε : ℝ, 0 < C₁ → 0 < C₂ → 0 < ε → ∀ᶠ (k : ℕ) in Filter.atTop, k.Prime →
    C₁ * k < S k ∧ (S k : ℝ) < C₂ * (k : ℝ) ^ (1 + ε)

/--
The first inequality of Conjecture 3.3: for every `C₁ > 0`, `C₁ * k < S k` for all sufficiently
large primes `k`. It is equivalent to Conjecture 4.4 (`statement_3_3_lower_iff`). Not proved here.
-/
def statement_3_3_lower : Prop :=
  ∀ C₁ : ℝ, 0 < C₁ → ∀ᶠ (k : ℕ) in Filter.atTop, k.Prime → C₁ * k < S k

/--
The second inequality of Conjecture 3.3: for every `C₂ > 0` and `ε > 0`,
`S k < C₂ * k ^ (1 + ε)` for all sufficiently large primes `k`. Theorem 7.1 of
`problems/theta-arithmetic-sum/DETAILS.md`, `|S k| < 6k(1 + ln k)^2 + 8k` for every odd prime `k`,
implies it, but that proof is pen-and-paper only: this `Prop` is not proved here.
-/
def statement_3_3_upper : Prop :=
  ∀ C₂ ε : ℝ, 0 < C₂ → 0 < ε → ∀ᶠ (k : ℕ) in Filter.atTop, k.Prime →
    (S k : ℝ) < C₂ * (k : ℝ) ^ (1 + ε)

/-- The plain alternating sum `s4 v k = ∑_{j=1}^{k-1} (-1)^⌊vj/k⌋`. -/
def s4 (v k : ℕ) : ℤ := ∑ j ∈ Ico 1 k, (-1 : ℤ) ^ (v * j / k)

/-- The `ℚ`-floor in `S'` is natural-number division. -/
theorem floor_eq (h j k : ℕ) : ⌊(h * j : ℚ) / k⌋₊ = h * j / k := by
  rw [← Nat.cast_mul, Nat.floor_div_eq_div]

/-- `S'` with the floor written as natural-number division. -/
theorem S'_eq (h k : ℕ) : S' h k = ∑ j ∈ Ico 1 k, (-1 : ℤ) ^ (j + 1 + h * j / k) := by
  simp only [S', floor_eq]

lemma neg_one_pow_add_eq_zero {a b : ℕ} (h : Odd (a + b)) : (-1 : ℤ) ^ a + (-1) ^ b = 0 := by
  have h1 : (-1 : ℤ) ^ (a + b) = -1 := h.neg_one_pow
  rw [pow_add] at h1
  rcases neg_one_pow_eq_or ℤ a with ha | ha <;> rw [ha] at h1 ⊢ <;> linarith

lemma neg_one_pow_eq_of_even {a b : ℕ} (h : Even (a + b)) : (-1 : ℤ) ^ a = (-1) ^ b := by
  have h1 : (-1 : ℤ) ^ (a + b) = 1 := h.neg_one_pow
  rw [pow_add] at h1
  rcases neg_one_pow_eq_or ℤ a with ha | ha <;> rw [ha] at h1 ⊢ <;> linarith

/-- Reflection of floors: if `k ∤ h * j` and `j ≤ k`, then `⌊hj/k⌋ + ⌊h(k-j)/k⌋ = h - 1`. -/
lemma div_add_div_sub {h j k : ℕ} (hk : 0 < k) (hj : j ≤ k) (hnd : ¬ k ∣ h * j) :
    h * j / k + h * (k - j) / k + 1 = h := by
  have hsum : h * j + h * (k - j) = h * k := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hj]
  have hmod : k ≤ h * j % k + h * (k - j) % k := by
    by_contra hlt
    rw [not_le] at hlt
    have h0 : (h * j + h * (k - j)) % k = 0 := by rw [hsum, Nat.mul_mod_left]
    rw [Nat.add_mod, Nat.mod_eq_of_lt hlt] at h0
    exact hnd (Nat.dvd_of_mod_eq_zero (by omega))
  have := Nat.add_div_eq_of_le_mod_add_mod hmod hk
  rw [hsum, Nat.mul_div_cancel _ hk] at this
  omega

/-- A prime `k` divides no product of two numbers in `[1, k)`. -/
lemma not_dvd_mul {a b k : ℕ} (hk : k.Prime) (ha : 0 < a) (hak : a < k) (hb : 0 < b)
    (hbk : b < k) : ¬ k ∣ a * b := by
  intro hdvd
  rcases (Nat.Prime.dvd_mul hk).1 hdvd with h1 | h1
  · exact absurd (Nat.le_of_dvd ha h1) (by omega)
  · exact absurd (Nat.le_of_dvd hb h1) (by omega)

/-- Reindexing `j ↦ k - j` on `[1, k)`. -/
lemma sum_Ico_reflect_self (f : ℕ → ℤ) (k : ℕ) :
    ∑ j ∈ Ico 1 k, f (k - j) = ∑ j ∈ Ico 1 k, f j := by
  rw [Finset.sum_Ico_reflect f 1 (Nat.le_succ k), Nat.add_sub_cancel_left, Nat.add_sub_cancel]

/-- A sum over `[1, k)` that changes sign under `j ↦ k - j` vanishes. -/
lemma sum_eq_zero_of_reflect_neg (f : ℕ → ℤ) (k : ℕ)
    (hf : ∀ j ∈ Ico 1 k, f (k - j) = - f j) : ∑ j ∈ Ico 1 k, f j = 0 := by
  have h1 := Finset.sum_congr rfl hf
  rw [Finset.sum_neg_distrib, sum_Ico_reflect_self] at h1
  linarith

/--
Lemma 5.7 of arXiv v1 (Proposition 7.5 of v3), in the case used here: `S' h k = 0` for odd
`h < k` and an odd prime `k`.
-/
theorem S'_eq_zero_of_odd {h k : ℕ} (hk : k.Prime) (hko : Odd k) (hh : Odd h) (hhk : h < k) :
    S' h k = 0 := by
  rw [S'_eq]
  refine sum_eq_zero_of_reflect_neg (fun j => (-1 : ℤ) ^ (j + 1 + h * j / k)) k ?_
  intro j hj
  rw [Finset.mem_Ico] at hj
  have key := div_add_div_sub hk.pos hj.2.le (not_dvd_mul hk hh.pos hhk (by omega) hj.2)
  have hodd : Odd ((k - j + 1 + h * (k - j) / k) + (j + 1 + h * j / k)) := by
    have e : (k - j + 1 + h * (k - j) / k) + (j + 1 + h * j / k) = k + h + 1 := by omega
    rw [e]
    exact (hko.add_odd hh).add_one
  have := neg_one_pow_add_eq_zero hodd
  simp only
  linarith

/-- `S' (k - v) k` is the plain alternating sum `s4 v k`, for a prime `k` and `0 < v < k`. -/
theorem S'_sub_eq_s4 {v k : ℕ} (hk : k.Prime) (hv : 0 < v) (hvk : v < k) :
    S' (k - v) k = s4 v k := by
  rw [S'_eq, s4]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  have key := div_add_div_sub hk.pos hvk.le (not_dvd_mul hk (by omega) hj.2 hv hvk)
  apply neg_one_pow_eq_of_even
  rw [Nat.mul_comm (k - v) j, Nat.mul_comm v j]
  have e : j + 1 + j * (k - v) / k + j * v / k = 2 * j := by omega
  rw [e]
  exact even_two_mul j

/-- `s4 v k = 0` for even `0 < v < k` and a prime `k`. -/
theorem s4_eq_zero_of_even {v k : ℕ} (hk : k.Prime) (hv : Even v) (hv0 : 0 < v) (hvk : v < k) :
    s4 v k = 0 := by
  rw [s4]
  refine sum_eq_zero_of_reflect_neg (fun j => (-1 : ℤ) ^ (v * j / k)) k ?_
  intro j hj
  rw [Finset.mem_Ico] at hj
  have key := div_add_div_sub hk.pos hj.2.le (not_dvd_mul hk hv0 hvk (by omega) hj.2)
  obtain ⟨r, hr⟩ := hv
  have hodd : Odd (v * (k - j) / k + v * j / k) := ⟨r - 1, by omega⟩
  have := neg_one_pow_add_eq_zero hodd
  simp only
  linarith

/-- For a prime `k`, `S k = ∑_{v=1}^{k-1} s4 v k`. -/
theorem S_eq_sum_s4 {k : ℕ} (hk : k.Prime) : S k = ∑ v ∈ Ico 1 k, s4 v k := by
  rw [S, ← sum_Ico_reflect_self (fun h => S' h k)]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finset.mem_Ico] at hv
  exact S'_sub_eq_s4 hk (by omega) hv.2

/-- Symmetric square form: for a prime `k`, `S k = ∑_{a,b=1}^{k-1} (-1)^⌊ab/k⌋`. -/
theorem S_eq_sum_sq {k : ℕ} (hk : k.Prime) :
    S k = ∑ a ∈ Ico 1 k, ∑ b ∈ Ico 1 k, (-1 : ℤ) ^ (a * b / k) := by
  rw [S_eq_sum_s4 hk]
  rfl

/-- For a prime `k`, only odd `v` contribute: `S k = ∑_{v odd, 1 ≤ v < k} s4 v k`. -/
theorem S_eq_sum_odd {k : ℕ} (hk : k.Prime) :
    S k = ∑ v ∈ (Ico 1 k).filter Odd, s4 v k := by
  rw [S_eq_sum_s4 hk, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finset.mem_Ico] at hv
  split_ifs with hodd
  · rfl
  · exact s4_eq_zero_of_even hk (Nat.not_odd_iff_even.1 hodd) (by omega) hv.2

/-- For odd `v`, `s4 v k` is twice its half-range sum `∑_{j=1}^{(k-1)/2} (-1)^⌊vj/k⌋`. -/
theorem s4_eq_two_mul {v k : ℕ} (hk : k.Prime) (hko : Odd k) (hv : Odd v) (hvk : v < k) :
    s4 v k = 2 * ∑ j ∈ Ico 1 ((k - 1) / 2 + 1), (-1 : ℤ) ^ (v * j / k) := by
  obtain ⟨r, hr⟩ := hko
  have h1 : 1 ≤ (k - 1) / 2 + 1 := by omega
  have h2 : (k - 1) / 2 + 1 ≤ k := by omega
  rw [s4, ← Finset.sum_Ico_consecutive (fun j => (-1 : ℤ) ^ (v * j / k)) h1 h2]
  have hrefl := Finset.sum_Ico_reflect (fun j => (-1 : ℤ) ^ (v * j / k)) 1
    (show (k - 1) / 2 + 1 ≤ k + 1 by omega)
  have e : k + 1 - ((k - 1) / 2 + 1) = (k - 1) / 2 + 1 := by omega
  rw [e, Nat.add_sub_cancel] at hrefl
  rw [← hrefl]
  have hsym : ∀ j ∈ Ico 1 ((k - 1) / 2 + 1),
      (-1 : ℤ) ^ (v * (k - j) / k) = (-1 : ℤ) ^ (v * j / k) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have key := div_add_div_sub hk.pos (by omega : j ≤ k)
      (not_dvd_mul hk hv.pos hvk (by omega) (by omega))
    apply neg_one_pow_eq_of_even
    obtain ⟨t, ht⟩ := hv
    exact ⟨t, by omega⟩
  rw [Finset.sum_congr rfl hsym]
  ring

lemma neg_one_pow_eq_ite (n : ℕ) : (-1 : ℤ) ^ n = if n % 2 = 0 then 1 else -1 := by
  split_ifs with h
  · exact (Nat.even_iff.2 h).neg_one_pow
  · exact (Nat.odd_iff.2 (by omega)).neg_one_pow

/-- `halfRow v k n = ∑_{j=1}^{n} (-1)^⌊vj/k⌋`, by structural recursion (kernel friendly). -/
def halfRow (v k : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => halfRow v k n + if v * (n + 1) / k % 2 = 0 then 1 else -1

/-- `rowsRec k n m = ∑_{v=1}^{m} [v odd] 2 * halfRow v k n` (kernel friendly). -/
def rowsRec (k n : ℕ) : ℕ → ℤ
  | 0 => 0
  | m + 1 => rowsRec k n m + if (m + 1) % 2 = 1 then 2 * halfRow (m + 1) k ((k - 1) / 2) else 0

/-- A kernel-friendly evaluation of `S k` for odd primes `k` (see `S_eq_fastS`). -/
def fastS (k : ℕ) : ℤ := rowsRec k ((k - 1) / 2) (k - 1)

lemma halfRow_eq (v k n : ℕ) :
    halfRow v k n = ∑ j ∈ Ico 1 (n + 1), (-1 : ℤ) ^ (v * j / k) := by
  induction n with
  | zero => simp [halfRow]
  | succ n ih =>
    rw [halfRow, ih, Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1), neg_one_pow_eq_ite]

lemma rowsRec_eq (k n m : ℕ) :
    rowsRec k n m = ∑ v ∈ Ico 1 (m + 1),
      if v % 2 = 1 then 2 * halfRow v k ((k - 1) / 2) else 0 := by
  induction m with
  | zero => simp [rowsRec]
  | succ m ih => rw [rowsRec, ih, Finset.sum_Ico_succ_top (by omega : 1 ≤ m + 1)]

/-- For an odd prime `k`, `S k = fastS k`. -/
theorem S_eq_fastS {k : ℕ} (hk : k.Prime) (hko : Odd k) : S k = fastS k := by
  rw [S_eq_sum_odd hk, fastS, rowsRec_eq, Nat.sub_add_cancel hk.one_le, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finset.mem_Ico] at hv
  by_cases hodd : Odd v
  · rw [if_pos hodd, if_pos (Nat.odd_iff.1 hodd), s4_eq_two_mul hk hko hodd hv.2, halfRow_eq]
  · rw [if_neg hodd, if_neg (fun h => hodd (Nat.odd_iff.2 h))]

/-- Kernel computation behind `small_primes`. -/
theorem fastS_small : ∀ k < 300, k.Prime → Odd k →
    0 < fastS k ∧ (k > 5 → k < fastS k) ∧ (k > 233 → 2 * k < fastS k) := by
  decide +kernel

/--
Kernel-checked instances of Conjectures 1.1, 4.1 and 4.2: every odd prime `k < 300` satisfies
`0 < S k`, `k < S k` when `k > 5`, and `2k < S k` when `k > 233`.
-/
theorem small_primes (k : ℕ) (hk : k < 300) (hp : k.Prime) (ho : Odd k) :
    0 < S k ∧ (k > 5 → k < S k) ∧ (k > 233 → 2 * k < S k) := by
  rw [S_eq_fastS hp ho]
  exact fastS_small k hk hp ho

/--
The upstream test: the first ten values of `S`.
(Table 1 of arXiv:2501.03234v1 lists 11 twice; these are the correct values.)
-/
theorem S_fst_10 : List.map S (List.range 10) = [0, 0, 1, 2, 5, 4, 7, 10, 11, 8] := by
  unfold S
  decide +kernel

/--
The Hardy sum `s₃(c, v) = ∑_{i=1}^{v-1} (-1)^i ((ci/v))`, with the sawtooth `((x))` written as
`(ci mod v)/v - 1/2`. This is the sawtooth whenever `v ∤ ci`, so for every `i` in the range
when `gcd(c, v) = 1`.
-/
def s3 (c v : ℕ) : ℚ := ∑ i ∈ Ico 1 v, (-1 : ℚ) ^ i * ((c * i % v : ℕ) / (v : ℚ) - 1 / 2)

/-- `H k = ∑_{v odd, v < k} 1/v`; for odd `k` this is the `H(k)` of `DETAILS.md`. -/
def H (k : ℕ) : ℚ := ∑ v ∈ (Ico 1 k).filter Odd, 1 / (v : ℚ)

/--
`V k = ∑_{v odd, v < k} s₃(k mod v, v)`. For odd `k` this is the `V(k)` of `DETAILS.md`, whose
sum starts at `v = 3`: the term `v = 1` is `0`.
-/
def V (k : ℕ) : ℚ := ∑ v ∈ (Ico 1 k).filter Odd, s3 (k % v) v

/-- `(-1)^n = 1 + 2 ∑_{q=1}^{n} (-1)^q`. -/
lemma neg_one_pow_eq_one_add_sum (n : ℕ) :
    (-1 : ℚ) ^ n = 1 + 2 * ∑ q ∈ Ico 1 (n + 1), (-1 : ℚ) ^ q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1), pow_succ]
    linear_combination ih

/-- `∑_{q=1}^{v-1} (-1)^q = 0` for odd `v`. -/
lemma sum_neg_one_pow_of_odd {v : ℕ} (hv : Odd v) : ∑ q ∈ Ico 1 v, (-1 : ℚ) ^ q = 0 := by
  obtain ⟨m, rfl⟩ := hv
  have h := neg_one_pow_eq_one_add_sum (2 * m)
  rw [Even.neg_one_pow ⟨m, by ring⟩] at h
  linarith

/-- `∑_{q=1}^{v-1} (-1)^q q = (v - 1)/2` for odd `v`. -/
lemma sum_neg_one_pow_mul_of_odd {v : ℕ} (hv : Odd v) :
    ∑ q ∈ Ico 1 v, (-1 : ℚ) ^ q * q = ((v : ℚ) - 1) / 2 := by
  obtain ⟨m, rfl⟩ := hv
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring,
      Finset.sum_Ico_succ_top (by omega : 1 ≤ 2 * m + 1 + 1),
      Finset.sum_Ico_succ_top (by omega : 1 ≤ 2 * m + 1), ih,
      Odd.neg_one_pow ⟨m, rfl⟩, Even.neg_one_pow ⟨m + 1, by ring⟩]
    push_cast
    ring

/-- For coprime `v, k` and `0 < q < v`, exactly `k - (⌊qk/v⌋ + 1)` of the `j ∈ [1, k)` have
`q ≤ ⌊vj/k⌋`. -/
lemma card_le_div {v k q : ℕ} (hcop : Nat.Coprime v k) (hk : 0 < k) (hq : 0 < q)
    (hqv : q < v) : ((Ico 1 k).filter (fun j => q ≤ v * j / k)).card = k - (q * k / v + 1) := by
  have hv : 0 < v := by omega
  have hfilter : (Ico 1 k).filter (fun j => q ≤ v * j / k) = Ico (q * k / v + 1) k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ico]
    have hne : v * j ≠ q * k := by
      intro h
      have := Nat.le_of_dvd hq (hcop.dvd_of_dvd_mul_right ⟨j, h.symm⟩)
      omega
    have h1 : q * k / v < j ↔ q * k < v * j := by rw [Nat.div_lt_iff_lt_mul hv, mul_comm j v]
    rw [Nat.le_div_iff_mul_le hk]
    constructor
    · rintro ⟨⟨_, hjk⟩, hle⟩
      exact ⟨by have := h1.2 (by omega); omega, hjk⟩
    · rintro ⟨hlo, hjk⟩
      have := h1.1 (by omega)
      exact ⟨⟨(Nat.le_add_left 1 _).trans hlo, hjk⟩, by omega⟩
  rw [hfilter, Nat.card_Ico]

/--
Reciprocity (Proposition 4.1 of `DETAILS.md`): for odd `v` coprime to `k > 0`,
`s4 v k = k/v - 1 + 2 s₃(k mod v, v)`.
-/
theorem s4_eq_reciprocity {v k : ℕ} (hv : Odd v) (hcop : Nat.Coprime v k) (hk : 0 < k) :
    (s4 v k : ℚ) = k / v - 1 + 2 * s3 (k % v) v := by
  have hv0 : 0 < v := hv.pos
  -- Expand each sign over the thresholds `q ∈ [1, v)` and swap the sums.
  have hterm : ∀ j ∈ Ico 1 k, (-1 : ℚ) ^ (v * j / k) =
      1 + 2 * ∑ q ∈ Ico 1 v, if q ≤ v * j / k then (-1 : ℚ) ^ q else 0 := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hlt : v * j / k < v := Nat.div_lt_of_lt_mul (by nlinarith)
    rw [neg_one_pow_eq_one_add_sum, ← Finset.sum_filter]
    congr 3
    ext q
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  have hcount : ∀ q ∈ Ico 1 v, (∑ j ∈ Ico 1 k, if q ≤ v * j / k then (-1 : ℚ) ^ q else 0)
      = (k - 1 / 2 : ℚ) * (-1) ^ q - (k / v) * ((-1) ^ q * q)
        + (-1) ^ q * ((k % v * q % v : ℕ) / (v : ℚ) - 1 / 2) := by
    intro q hq
    rw [Finset.mem_Ico] at hq
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      card_le_div hcop hk (by omega) hq.2]
    have hle : q * k / v + 1 ≤ k := by
      have : q * k / v < k := Nat.div_lt_of_lt_mul (by nlinarith)
      omega
    have hmod : q * k % v = k % v * q % v := by
      rw [Nat.mul_mod, Nat.mod_eq_of_lt hq.2, mul_comm]
    have hdm := Nat.div_add_mod (q * k) v
    rw [← hmod]
    have hX : ((q * k / v : ℕ) : ℚ) = ((q : ℚ) * k - ((q * k % v : ℕ) : ℚ)) / v := by
      have : (v : ℚ) * ((q * k / v : ℕ) : ℚ) + ((q * k % v : ℕ) : ℚ) = q * k := by
        exact_mod_cast hdm
      field_simp
      linarith
    push_cast [Nat.cast_sub hle]
    rw [hX]
    field_simp
    ring
  rw [s4]
  push_cast
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm,
    Finset.sum_congr rfl hcount, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_neg_one_pow_of_odd hv,
    sum_neg_one_pow_mul_of_odd hv, Finset.sum_const, Nat.card_Ico, s3, nsmul_eq_mul, mul_one]
  generalize (∑ i ∈ Ico 1 v, (-1 : ℚ) ^ i * ((k % v * i % v : ℕ) / (v : ℚ) - 1 / 2)) = T
  have hk1 : 1 ≤ k := hk
  push_cast [Nat.cast_sub hk1]
  field_simp
  ring

/-- There are `(k - 1)/2` odd numbers in `[1, k)` for odd `k`. -/
lemma card_filter_odd {k : ℕ} (hk : Odd k) : ((Ico 1 k).filter Odd).card = (k - 1) / 2 := by
  obtain ⟨m, rfl⟩ := hk
  rw [Finset.card_filter]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring,
      Finset.sum_Ico_succ_top (by omega : 1 ≤ 2 * m + 1 + 1),
      Finset.sum_Ico_succ_top (by omega : 1 ≤ 2 * m + 1), ih,
      if_pos (show Odd (2 * m + 1) from ⟨m, rfl⟩),
      if_neg (show ¬ Odd (2 * m + 1 + 1) from Nat.not_odd_iff_even.2 ⟨m + 1, by ring⟩)]
    omega

/--
**Exact formula** (Theorem 4.3 of `DETAILS.md`): for an odd prime `k`,
`S k = k H(k) - (k - 1)/2 + 2 V(k)`.
-/
theorem S_eq_exact {k : ℕ} (hk : k.Prime) (hko : Odd k) :
    (S k : ℚ) = k * H k - ((k : ℚ) - 1) / 2 + 2 * V k := by
  have hterm : ∀ v ∈ (Ico 1 k).filter Odd,
      (s4 v k : ℚ) = k / v - 1 + 2 * s3 (k % v) v := by
    intro v hv
    rw [Finset.mem_filter, Finset.mem_Ico] at hv
    have hcop : Nat.Coprime v k := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hk).2
      fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega))
    exact s4_eq_reciprocity hv.2 hcop hk.pos
  have e1 : ∑ v ∈ (Ico 1 k).filter Odd, (k : ℚ) / v = k * H k := by
    rw [H, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have e2 : ∑ v ∈ (Ico 1 k).filter Odd, (1 : ℚ) = ((k : ℚ) - 1) / 2 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_filter_odd hko]
    obtain ⟨r, rfl⟩ := hko
    rw [show (2 * r + 1 - 1) / 2 = r by omega]
    push_cast
    ring
  rw [S_eq_sum_odd hk]
  push_cast
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, e1, e2, V,
    Finset.mul_sum]

/-- Conjecture 1.1 is equivalent to the lower bound `2 V(k) > (k - 1)/2 - k H(k)`. -/
theorem statement_1_1_iff : statement_1_1 ↔
    ∀ k : ℕ, k.Prime → Odd k → ((k : ℚ) - 1) / 2 - k * H k < 2 * V k := by
  refine forall_congr' fun k => imp_congr_right fun hk => imp_congr_right fun hko => ?_
  rw [← Int.cast_pos (R := ℚ), S_eq_exact hk hko]
  constructor <;> intro h <;> linarith

/-- Conjecture 3.3 is the conjunction of its two inequalities. -/
theorem statement_3_3_iff : statement_3_3 ↔ statement_3_3_lower ∧ statement_3_3_upper := by
  constructor
  · intro h
    refine ⟨fun C₁ hC₁ => ?_, fun C₂ ε hC₂ hε => ?_⟩
    · filter_upwards [h C₁ 1 1 hC₁ one_pos one_pos] with k hk hp using (hk hp).1
    · filter_upwards [h 1 C₂ ε one_pos hC₂ hε] with k hk hp using (hk hp).2
  · rintro ⟨hl, hu⟩ C₁ C₂ ε hC₁ hC₂ hε
    filter_upwards [hl C₁ hC₁, hu C₂ ε hC₂ hε] with k h1 h2 hp using ⟨h1 hp, h2 hp⟩

/-- The first inequality of Conjecture 3.3 is equivalent to Conjecture 4.4. -/
theorem statement_3_3_lower_iff : statement_3_3_lower ↔ statement_4_4 := by
  constructor
  · intro h n
    filter_upwards [h (n + 1) (by positivity)] with k hk hp _
    have h1 : ((n * k : ℤ) : ℝ) ≤ ((n : ℝ) + 1) * k := by
      push_cast
      nlinarith [k.cast_nonneg (α := ℝ)]
    exact_mod_cast h1.trans_lt (hk hp)
  · intro h C₁ hC₁
    filter_upwards [h ⌈C₁⌉₊, Filter.eventually_ge_atTop 3] with k hk hk3 hp
    have h1 : ((⌈C₁⌉₊ * k : ℕ) : ℤ) < S k := by
      exact_mod_cast hk hp (hp.odd_of_ne_two (by omega))
    have h2 : C₁ * k ≤ ((⌈C₁⌉₊ * k : ℕ) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_right (Nat.le_ceil C₁) k.cast_nonneg
    have h3 : (((⌈C₁⌉₊ * k : ℕ) : ℤ) : ℝ) < (S k : ℝ) := by exact_mod_cast h1
    push_cast at h2 h3 ⊢
    linarith

end AgenticConjectures.ThetaArithmeticSum
