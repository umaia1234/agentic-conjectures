import Mathlib

/-!
# Vieta jumping with `r = 2`: the values of `2(a+b)/gcd(a,b)^2`

Steven J. Miller, Dimitrios Nikolakopoulos and Anitha Srinivasan, *Fibonacci Numbers and Vieta
Jumping for a Rational Diophantine Equation* (arXiv:2605.19083v2), study the positive integer
solutions `(a, b)` of `(a+r)/b + (b+r)/a = k`, where `k` is an integer. Their Conjecture 4.2
(in §4.1) is about `r = 2`. It says that every solution has
`2(a+b)/gcd(a,b)^2 ∈ {1, 2, 3, 4, 5, 8}`. Moreover, the values are `1` and `5` when `k = 3`,
`2` and `3` when `k = 4`, and `4` and `8` when `k = 6`. `statement` formalizes the conjecture
and `statement_holds` proves it.

Canonical source (checked 2026-10-25): https://arxiv.org/abs/2605.19083v2

## Readings

There is no Formal Conjectures file for this conjecture, so `statement` is ours.

* `k` is an integer, as in the paper's setup in §1. For rational `k` the claim is false:
  `(a, b) = (1, 2)` gives `k = 11/2` and the value `6`.
* `a` and `b` are positive natural numbers. The two fractions and `2(a+b)/gcd(a,b)^2` are
  computed in `ℚ`, with `Nat.gcd`.
* "If `k = 3`, the values are `1` and `5`" is read as an equality of sets: the values taken
  over all solutions with `k = 3` are exactly `1` and `5`. This covers both the inclusion and
  the attainment readings. The same holds for `k = 4` and `k = 6`.

## Proof

`IsSolution.sol` clears denominators: the equation becomes `a^2 + 2a + b^2 + 2b = kab`, which
is `Sol 2 a b k`.

1. `k_cases` (the paper's Remark 4.1). If `a < b`, then `b' = ka - 2 - b` satisfies
   `b b' = a^2 + 2a < (a+1)^2`, so `0 < b' ≤ a` and `(a, b')` is a solution with a smaller
   sum. The descent ends on the diagonal, where `(k-2)a = 4`, so `k ∈ {3, 4, 6}`.
2. `key`. Write `a = gx` and `b = gy` with `g = gcd(a, b)`, and put `m = kxy - x^2 - y^2`.
   Then `gm = r(x+y)`, so `m` is the value `r(a+b)/g^2`. Since `x + y` is coprime to `xy`,
   `m ∣ r(k+2)`. For `r = 2` this leaves the divisors of `10`, `12` and `16`.
3. The identity `(x+y)^2 + m = (k+2)xy` excludes the other divisors. For `k = 3`, `m = 2` fails
   mod 5 and `m = 10` mod 25. For `k = 4`, `m = 1` and `m = 4` fail mod 3, and `m = 6` mod 9.
   For `k = 6`, `m = 1` and `m = 2` fail mod 8. The cases `k = 4, m = 12` and `k = 6, m = 16`
   force `x` and `y` to be odd, and then fail mod 4 and mod 16.
4. Witnesses: `(4,4)` and `(4,6)` give `1` and `5`; `(2,2)` and `(2,4)` give `2` and `3`;
   `(1,1)` and `(1,3)` give `4` and `8`.

## General `r` (namespace `GeneralR`; beyond the paper)

For `r > 0`, `Sol r a b k` is the cleared form of `(a+r)/b + (b+r)/a = k`.

* `k_ge_three`: `k ≥ 3`.
* `descent`: Vieta jumps take every solution to a *reduced* solution with the same `k`, that is,
  one with `a ≤ b` and `b^2 ≤ a^2 + ra`. The paper observes that its descent to the diagonal
  breaks down for `r ≥ 3`; reduced solutions take the place of the diagonal.
* `reduced_bounds`: a reduced solution has `2(b-a) ≤ r` and `a ≤ 2r`.
* `k_range` and `k_range_sharp`: `3 ≤ k ≤ 2r + 2`, and both ends occur.
* `key` (above, shared with the `r = 2` proof): `r(a+b)/gcd(a,b)^2` is a positive integer
  that divides `r(k+2)`.
* `thm12`: the paper's Theorem 1.2 (`r = 1`), in the coprime form, as a consistency check.
* `two_periodic`: on a Vieta chain `…, a, b, c, d, …`, where each term is `k` times the one
  before minus `r` minus the one before that, the pairs `(a, b)` and `(c, d)` have the same
  value `r(a+b)/gcd(a,b)^2` (`normVal`).
* `values_eq`: hence the values over all solutions with a given `k` are the values of the
  reduced solutions `(a, b)` with that `k` and of their neighbours `(a, ka - r - b)`
  (`chainVals`). By `reduced_bounds` there are finitely many reduced solutions, so this
  computes the set of values for each `r`.
* `values_one`, `values_two`, `values_three`: the sets of values for `r = 1, 2, 3`.
  `values_one` is the paper's Theorem 1.2 again, and `values_two` gives the value sets of the
  conjecture again, in the cleared form and without congruences.
* `eleven_three`: for `r = 11`, `(21, 28)` has `k = 3` and value `11`, so the values for a
  given `k` depend on `r`.

## Credit

The problem, the conjecture, the descent for `r = 2` with `k ∈ {3, 4, 6}`, the diagonal
analysis for general `r` and the observation that the descent breaks down for `r ≥ 3` are the
paper's. This file adds the divisibility step, the congruence eliminations, the reduced-solution
analysis for general `r` with the two-periodicity and the value tables (standard Vieta-jumping
arguments) and the Lean proofs. No novelty is claimed.
-/

namespace AgenticConjectures.VietaR2Gcd

/-- Integer form of `(a+r)/b + (b+r)/a = k` for positive `a` and `b`. -/
def Sol (r a b k : ℤ) : Prop := 0 < a ∧ 0 < b ∧ a ^ 2 + r * a + b ^ 2 + r * b = k * a * b

theorem Sol.symm {r a b k : ℤ} (h : Sol r a b k) : Sol r b a k := by
  obtain ⟨ha, hb, h⟩ := h
  exact ⟨hb, ha, by linear_combination h⟩

/-- One step along a chain: `(a, b) ↦ (b, k b - r - a)`. -/
theorem Sol.next {r a b k : ℤ} (hr : 0 ≤ r) (h : Sol r a b k) : Sol r b (k * b - r - a) k := by
  obtain ⟨ha, hb, h⟩ := h
  have hprod : a * (k * b - r - a) = b * (b + r) := by linear_combination -h
  have hpos : 0 < k * b - r - a := by
    by_contra hx
    push Not at hx
    nlinarith [mul_pos hb hb]
  exact ⟨hb, hpos, by linear_combination h⟩

/-! ### The descent for `r = 2` (the paper's Remark 4.1) -/

/-- A diagonal solution for `r = 2` has `(k - 2) a = 4`, so `k ∈ {3, 4, 6}`. -/
theorem diag {a k : ℤ} (h : Sol 2 a a k) : k = 3 ∨ k = 4 ∨ k = 6 := by
  obtain ⟨ha, -, h⟩ := h
  have h1 : (k - 2) * a = 4 := by
    have : a * ((k - 2) * a - 4) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h0 | h0
    · omega
    · linarith
  have hk : 0 < k - 2 := by
    by_contra hk
    push Not at hk
    nlinarith
  have ha4 : a ≤ 4 := by nlinarith
  interval_cases a <;> omega

private theorem k_cases_aux : ∀ n : ℕ, ∀ a b k : ℤ, a + b ≤ n → Sol 2 a b k →
    k = 3 ∨ k = 4 ∨ k = 6 := by
  intro n
  induction n with
  | zero =>
    intro a b k hn hs
    obtain ⟨ha, hb, -⟩ := hs
    omega
  | succ n ih =>
    intro a b k hn hs
    wlog hab : a ≤ b generalizing a b
    · exact this b a (by omega) hs.symm (by omega)
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact diag hs
    · obtain ⟨ha, hb, h⟩ := hs
      have hab1 : a + 1 ≤ b := hlt
      have hprod : b * (k * a - 2 - b) = a ^ 2 + 2 * a := by linear_combination -h
      have hpos : 0 < k * a - 2 - b := by nlinarith
      have hlt' : k * a - 2 - b < b := by nlinarith
      have hs' : Sol 2 a (k * a - 2 - b) k := ⟨ha, hpos, by linear_combination h⟩
      exact ih a (k * a - 2 - b) k (by omega) hs'

/-- The paper's Remark 4.1: for `r = 2` only `k = 3, 4, 6` occur. -/
theorem k_cases {a b k : ℤ} (h : Sol 2 a b k) : k = 3 ∨ k = 4 ∨ k = 6 := by
  have h0 := h
  obtain ⟨ha, hb, -⟩ := h0
  exact k_cases_aux (a + b).toNat a b k (by omega) h

/-! ### The divisibility step -/

/-- With `a = g x`, `b = g y` and `x, y` coprime, `m = k x y - x^2 - y^2` satisfies
`g m = r (x + y)` (so `m = r (a + b) / g^2`) and `m ∣ r (k + 2)`. -/
theorem key (r x y g k : ℤ) (hx : 0 < x) (hy : 0 < y) (hg : 0 < g) (hc : IsCoprime x y)
    (h : (g * x) ^ 2 + r * (g * x) + (g * y) ^ 2 + r * (g * y) = k * (g * x) * (g * y)) :
    g * (k * x * y - x ^ 2 - y ^ 2) = r * (x + y) ∧
      (k * x * y - x ^ 2 - y ^ 2) ∣ r * (k + 2) := by
  have h1 : g * (k * x * y - x ^ 2 - y ^ 2) = r * (x + y) := by
    have : g * (g * (k * x * y - x ^ 2 - y ^ 2) - r * (x + y)) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h0 | h0
    · omega
    · linarith
  refine ⟨h1, ?_⟩
  have h2 : (x + y) * (r + g * (x + y)) = ((k + 2) * g) * (x * y) := by linear_combination -h1
  have hcop : IsCoprime (x + y) (x * y) := by
    obtain ⟨u, v, huv⟩ := hc
    exact IsCoprime.mul_right ⟨v, u - v, by linear_combination huv⟩
      ⟨u, v - u, by linear_combination huv⟩
  obtain ⟨s, hs⟩ : (x + y) ∣ (k + 2) * g := hcop.dvd_of_dvd_mul_right ⟨_, h2.symm⟩
  refine ⟨s, ?_⟩
  have h3 : (x + y) * (r * (k + 2) - (k * x * y - x ^ 2 - y ^ 2) * s) = 0 := by
    linear_combination (k * x * y - x ^ 2 - y ^ 2) * hs - (k + 2) * h1
  rcases mul_eq_zero.mp h3 with h0 | h0
  · omega
  · linarith

/-! ### Congruence obstructions

`no_k_m` says that `(x + y)^2 + m = (k + 2) x y` has no solution; it excludes the value `m`
for this `k`. -/

theorem no_6_1 (x y : ℤ) : (x + y) ^ 2 + 1 ≠ 8 * x * y := by
  intro h
  have h' := congrArg (fun z : ℤ => (z : ZMod 8)) h
  push_cast at h'
  generalize (x : ZMod 8) = X at h'
  generalize (y : ZMod 8) = Y at h'
  revert X Y
  decide

theorem no_6_2 (x y : ℤ) : (x + y) ^ 2 + 2 ≠ 8 * x * y := by
  intro h
  have h' := congrArg (fun z : ℤ => (z : ZMod 8)) h
  push_cast at h'
  generalize (x : ZMod 8) = X at h'
  generalize (y : ZMod 8) = Y at h'
  revert X Y
  decide

theorem no_6_16 (x y : ℤ) (hc : IsCoprime x y) : (x + y) ^ 2 + 16 ≠ 8 * x * y := by
  intro h
  rcases Int.even_or_odd x with ⟨p, rfl⟩ | ⟨p, rfl⟩ <;>
    rcases Int.even_or_odd y with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · obtain ⟨u, v, huv⟩ := hc
    have : (2 : ℤ) ∣ 1 := ⟨u * p + v * q, by linear_combination -huv⟩
    omega
  all_goals
    have h' := congrArg (fun z : ℤ => (z : ZMod 16)) h
    push_cast at h'
    generalize (p : ZMod 16) = P at h'
    generalize (q : ZMod 16) = Q at h'
    revert P Q
    decide

theorem no_4_1 (x y : ℤ) : (x + y) ^ 2 + 1 ≠ 6 * x * y := by
  intro h
  have h' := congrArg (fun z : ℤ => (z : ZMod 3)) h
  push_cast at h'
  generalize (x : ZMod 3) = X at h'
  generalize (y : ZMod 3) = Y at h'
  revert X Y
  decide

theorem no_4_4 (x y : ℤ) : (x + y) ^ 2 + 4 ≠ 6 * x * y := by
  intro h
  have h' := congrArg (fun z : ℤ => (z : ZMod 3)) h
  push_cast at h'
  generalize (x : ZMod 3) = X at h'
  generalize (y : ZMod 3) = Y at h'
  revert X Y
  decide

theorem no_4_6 (x y : ℤ) : (x + y) ^ 2 + 6 ≠ 6 * x * y := by
  intro h
  have h' := congrArg (fun z : ℤ => (z : ZMod 9)) h
  push_cast at h'
  generalize (x : ZMod 9) = X at h'
  generalize (y : ZMod 9) = Y at h'
  revert X Y
  decide

theorem no_4_12 (x y : ℤ) (hc : IsCoprime x y) : (x + y) ^ 2 + 12 ≠ 6 * x * y := by
  intro h
  rcases Int.even_or_odd x with ⟨p, rfl⟩ | ⟨p, rfl⟩ <;>
    rcases Int.even_or_odd y with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · obtain ⟨u, v, huv⟩ := hc
    have : (2 : ℤ) ∣ 1 := ⟨u * p + v * q, by linear_combination -huv⟩
    omega
  all_goals
    have h' := congrArg (fun z : ℤ => (z : ZMod 4)) h
    push_cast at h'
    generalize (p : ZMod 4) = P at h'
    generalize (q : ZMod 4) = Q at h'
    revert P Q
    decide

theorem no_3_2 (x y : ℤ) : (x + y) ^ 2 + 2 ≠ 5 * x * y := by
  intro h
  have h' := congrArg (fun z : ℤ => (z : ZMod 5)) h
  push_cast at h'
  generalize (x : ZMod 5) = X at h'
  generalize (y : ZMod 5) = Y at h'
  revert X Y
  decide

theorem no_3_10 (x y : ℤ) : (x + y) ^ 2 + 10 ≠ 5 * x * y := by
  intro h
  have h' := congrArg (fun z : ℤ => (z : ZMod 25)) h
  push_cast at h'
  generalize (x : ZMod 25) = X at h'
  generalize (y : ZMod 25) = Y at h'
  revert X Y
  decide

/-! ### The statement -/

/-- `(a+2)/b + (b+2)/a = k` in `ℚ`, with `a, b` positive naturals and `k` an integer. -/
def IsSolution (a b : ℕ) (k : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ ((a : ℚ) + 2) / b + ((b : ℚ) + 2) / a = k

/-- `2(a+b)/gcd(a,b)^2`, as a rational number. -/
def normSum (a b : ℕ) : ℚ := 2 * ((a : ℚ) + b) / (Nat.gcd a b : ℚ) ^ 2

theorem IsSolution.sol {a b : ℕ} {k : ℤ} (h : IsSolution a b k) : Sol 2 a b k := by
  obtain ⟨ha, hb, h⟩ := h
  refine ⟨by exact_mod_cast ha, by exact_mod_cast hb, ?_⟩
  have ha' : (a : ℚ) ≠ 0 := by positivity
  have hb' : (b : ℚ) ≠ 0 := by positivity
  rw [div_add_div _ _ hb' ha', div_eq_iff (mul_ne_zero hb' ha')] at h
  have : (((a : ℤ) ^ 2 + 2 * a + (b : ℤ) ^ 2 + 2 * b : ℤ) : ℚ) = ((k * a * b : ℤ) : ℚ) := by
    push_cast
    linear_combination h
  exact_mod_cast this

private theorem div10 {m : ℤ} (h0 : 0 < m) (h : m ∣ 10) : m = 1 ∨ m = 2 ∨ m = 5 ∨ m = 10 := by
  have := Int.le_of_dvd (by norm_num) h
  interval_cases m <;> omega

private theorem div12 {m : ℤ} (h0 : 0 < m) (h : m ∣ 12) :
    m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 12 := by
  have := Int.le_of_dvd (by norm_num) h
  interval_cases m <;> omega

private theorem div16 {m : ℤ} (h0 : 0 < m) (h : m ∣ 16) :
    m = 1 ∨ m = 2 ∨ m = 4 ∨ m = 8 ∨ m = 16 := by
  have := Int.le_of_dvd (by norm_num) h
  interval_cases m <;> omega

/-- The possible `k` with the possible values of `normSum` for each. -/
theorem normSum_cases (a b : ℕ) (k : ℤ) (h : IsSolution a b k) :
    (k = 3 ∧ (normSum a b = 1 ∨ normSum a b = 5)) ∨
    (k = 4 ∧ (normSum a b = 2 ∨ normSum a b = 3)) ∨
    (k = 6 ∧ (normSum a b = 4 ∨ normSum a b = 8)) := by
  have hs := h.sol
  obtain ⟨ha, hb, -⟩ := h
  have hk := k_cases hs
  obtain ⟨g, x, y, hg, hcop, rfl, rfl⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_left b ha)
  have hgcd : Nat.gcd (x * g) (y * g) = g := by
    rw [Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul]
  have hx : 0 < x := Nat.pos_of_mul_pos_right ha
  have hy : 0 < y := Nat.pos_of_mul_pos_right hb
  obtain ⟨-, -, hs⟩ := hs
  have hc : IsCoprime (x : ℤ) (y : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨h1, hdvd⟩ := key 2 x y g k (by exact_mod_cast hx) (by exact_mod_cast hy)
    (by exact_mod_cast hg) hc (by push_cast at hs; linear_combination hs)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = k * x * y - x ^ 2 - y ^ 2 := ⟨_, rfl⟩
  rw [← hm] at h1 hdvd
  have hmpos : 0 < m := by
    have h2 : 0 < (g : ℤ) * m := by rw [h1]; positivity
    have hg' : (0 : ℤ) < g := by exact_mod_cast hg
    nlinarith
  have hid : ((x : ℤ) + y) ^ 2 + m = (k + 2) * x * y := by rw [hm]; ring
  have hnorm : normSum (x * g) (y * g) = m := by
    unfold normSum
    rw [hgcd, div_eq_iff (by positivity)]
    have h1q : (g : ℚ) * (m : ℚ) = 2 * ((x : ℚ) + y) := by exact_mod_cast h1
    push_cast
    linear_combination -(g : ℚ) * h1q
  rw [hnorm]
  rcases hk with rfl | rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    rcases div10 hmpos (by simpa using hdvd) with rfl | rfl | rfl | rfl
    · norm_num
    · exact absurd (by linear_combination hid) (no_3_2 x y)
    · norm_num
    · exact absurd (by linear_combination hid) (no_3_10 x y)
  · right; left
    refine ⟨rfl, ?_⟩
    rcases div12 hmpos (by simpa using hdvd) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by linear_combination hid) (no_4_1 x y)
    · norm_num
    · norm_num
    · exact absurd (by linear_combination hid) (no_4_4 x y)
    · exact absurd (by linear_combination hid) (no_4_6 x y)
    · exact absurd (by linear_combination hid) (no_4_12 x y hc)
  · right; right
    refine ⟨rfl, ?_⟩
    rcases div16 hmpos (by simpa using hdvd) with rfl | rfl | rfl | rfl | rfl
    · exact absurd (by linear_combination hid) (no_6_1 x y)
    · exact absurd (by linear_combination hid) (no_6_2 x y)
    · norm_num
    · norm_num
    · exact absurd (by linear_combination hid) (no_6_16 x y hc)

/-- Conjecture 4.2 of arXiv:2605.19083v2: for every solution, `2(a+b)/gcd(a,b)^2` lies in
`{1, 2, 3, 4, 5, 8}`, and the values for `k = 3`, `4`, `6` are exactly `{1, 5}`, `{2, 3}`,
`{4, 8}`. -/
def statement : Prop :=
  (∀ a b : ℕ, ∀ k : ℤ, IsSolution a b k → normSum a b ∈ ({1, 2, 3, 4, 5, 8} : Set ℚ)) ∧
    {q | ∃ a b, IsSolution a b 3 ∧ q = normSum a b} = {1, 5} ∧
    {q | ∃ a b, IsSolution a b 4 ∧ q = normSum a b} = {2, 3} ∧
    {q | ∃ a b, IsSolution a b 6 ∧ q = normSum a b} = {4, 8}

/-- Conjecture 4.2 of arXiv:2605.19083v2 holds. -/
theorem statement_holds : statement := by
  refine ⟨fun a b k h => ?_, ?_, ?_, ?_⟩
  · rcases normSum_cases a b k h with ⟨-, h | h⟩ | ⟨-, h | h⟩ | ⟨-, h | h⟩ <;> simp [h]
  · ext q
    constructor
    · rintro ⟨a, b, h, rfl⟩
      rcases normSum_cases a b 3 h with ⟨-, h | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp_all
    · rintro (rfl | rfl)
      · exact ⟨4, 4, by norm_num [IsSolution], by norm_num [normSum]⟩
      · exact ⟨4, 6, by norm_num [IsSolution], by norm_num [normSum]⟩
  · ext q
    constructor
    · rintro ⟨a, b, h, rfl⟩
      rcases normSum_cases a b 4 h with ⟨h, -⟩ | ⟨-, h | h⟩ | ⟨h, -⟩ <;> simp_all
    · rintro (rfl | rfl)
      · exact ⟨2, 2, by norm_num [IsSolution], by norm_num [normSum]⟩
      · exact ⟨2, 4, by norm_num [IsSolution], by norm_num [normSum]⟩
  · ext q
    constructor
    · rintro ⟨a, b, h, rfl⟩
      rcases normSum_cases a b 6 h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h | h⟩ <;> simp_all
    · rintro (rfl | rfl)
      · exact ⟨1, 1, by norm_num [IsSolution], by norm_num [normSum]⟩
      · exact ⟨1, 3, by norm_num [IsSolution], by norm_num [normSum]⟩

/-! ### General `r` -/

namespace GeneralR

/-- `k ≥ 3` for every solution with `r > 0`. -/
theorem k_ge_three {r a b k : ℤ} (hr : 0 < r) (h : Sol r a b k) : 3 ≤ k := by
  obtain ⟨ha, hb, h⟩ := h
  by_contra hk
  push Not at hk
  have hab : 0 < a * b := mul_pos ha hb
  have h2 : k * (a * b) ≤ 2 * (a * b) := mul_le_mul_of_nonneg_right (by omega) hab.le
  nlinarith [sq_nonneg (a - b), mul_pos hr ha, mul_pos hr hb]

/-- A reduced solution: `a ≤ b` and `b^2 ≤ a^2 + r a`. -/
def Reduced (r a b : ℤ) : Prop := a ≤ b ∧ b ^ 2 ≤ a ^ 2 + r * a

private theorem descent_aux (r : ℤ) (hr : 0 < r) : ∀ n : ℕ, ∀ a b k : ℤ, a + b ≤ n →
    Sol r a b k → ∃ a' b', Sol r a' b' k ∧ Reduced r a' b' := by
  intro n
  induction n with
  | zero =>
    intro a b k hn hs
    obtain ⟨ha, hb, -⟩ := hs
    omega
  | succ n ih =>
    intro a b k hn hs
    wlog hab : a ≤ b generalizing a b
    · exact this b a (by omega) hs.symm (by omega)
    by_cases hred : b ^ 2 ≤ a ^ 2 + r * a
    · exact ⟨a, b, hs, hab, hred⟩
    · push Not at hred
      obtain ⟨ha, hb, h⟩ := hs
      have hprod : b * (k * a - r - b) = a ^ 2 + r * a := by linear_combination -h
      have hpos : 0 < k * a - r - b := by
        by_contra hx
        push Not at hx
        nlinarith [mul_pos ha ha, mul_pos hr ha]
      have hlt : k * a - r - b < b := by nlinarith
      exact ih a (k * a - r - b) k (by omega) ⟨ha, hpos, by linear_combination h⟩

/-- Vieta descent: every solution leads to a reduced solution with the same `k`. -/
theorem descent {r a b k : ℤ} (hr : 0 < r) (h : Sol r a b k) :
    ∃ a' b', Sol r a' b' k ∧ Reduced r a' b' := by
  have h0 := h
  obtain ⟨ha, hb, -⟩ := h0
  exact descent_aux r hr (a + b).toNat a b k (by omega) h

/-- Reduced solutions satisfy `2 (b - a) ≤ r` and `a ≤ 2 r`. -/
theorem reduced_bounds {r a b k : ℤ} (hr : 0 < r) (h : Sol r a b k) (hred : Reduced r a b) :
    2 * (b - a) ≤ r ∧ a ≤ 2 * r := by
  have hk := k_ge_three hr h
  obtain ⟨ha, hb, h⟩ := h
  obtain ⟨hab, hb2⟩ := hred
  have hd : 2 * (b - a) ≤ r := by
    have : 2 * (b - a) * a ≤ r * a := by nlinarith
    exact le_of_mul_le_mul_right this ha
  refine ⟨hd, ?_⟩
  by_contra hcon
  push Not at hcon
  have e1 : a ≤ a * (a - 2 * r) := by nlinarith
  have e2 : 0 ≤ (b - a) * (a - (b - a) - r) := mul_nonneg (by omega) (by omega)
  have e3 : 0 ≤ (k - 3) * (a * b) := mul_nonneg (by omega) (mul_pos ha hb).le
  nlinarith

/-- On reduced solutions, `k ≤ 2 r + 2`. -/
theorem k_le_reduced {r a b k : ℤ} (hr : 0 < r) (h : Sol r a b k) (hred : Reduced r a b) :
    k ≤ 2 * r + 2 := by
  obtain ⟨ha, hb, h⟩ := h
  obtain ⟨hab, hb2⟩ := hred
  rcases eq_or_lt_of_le (show 1 ≤ a by omega) with rfl | ha2
  · have hb' : b ≤ r + 1 := by nlinarith
    have hq : (b - 1) * (b - r - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
    have : k * b ≤ (2 * r + 2) * b := by nlinarith
    exact le_of_mul_le_mul_right this hb
  · have p1 : a * a ≤ a * b := mul_le_mul_of_nonneg_left hab ha.le
    have p2 : r * a * 2 ≤ r * a * b :=
      mul_le_mul_of_nonneg_left (by omega) (mul_pos hr ha).le
    have p3 : r * b * 2 ≤ r * b * a :=
      mul_le_mul_of_nonneg_left (by omega) (mul_pos hr hb).le
    have h1 : (2 * k) * (a * b) ≤ (4 + 3 * r) * (a * b) := by nlinarith
    have := le_of_mul_le_mul_right h1 (mul_pos ha hb)
    omega

/-- `3 ≤ k ≤ 2 r + 2` for every solution with `r > 0`. -/
theorem k_range {r a b k : ℤ} (hr : 0 < r) (h : Sol r a b k) : 3 ≤ k ∧ k ≤ 2 * r + 2 := by
  refine ⟨k_ge_three hr h, ?_⟩
  obtain ⟨a', b', hs', hred⟩ := descent hr h
  exact k_le_reduced hr hs' hred

/-- Both ends of `k_range` occur: `(1, 1)` gives `k = 2 r + 2` and `(2 r, 2 r)` gives `k = 3`. -/
theorem k_range_sharp {r : ℤ} (hr : 0 < r) : Sol r 1 1 (2 * r + 2) ∧ Sol r (2 * r) (2 * r) 3 :=
  ⟨⟨by norm_num, by norm_num, by ring⟩, ⟨by omega, by omega, by ring⟩⟩

private theorem div5 {m : ℤ} (h0 : 0 < m) (h : m ∣ 5) : m = 1 ∨ m = 5 := by
  have := Int.le_of_dvd (by norm_num) h
  interval_cases m <;> omega

private theorem div6 {m : ℤ} (h0 : 0 < m) (h : m ∣ 6) : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by
  have := Int.le_of_dvd (by norm_num) h
  interval_cases m <;> omega

/-- The paper's Theorem 1.2 in the coprime form: for `r = 1`, `m = (a + b) / g^2` is `1` or
`5` when `k = 3` and `2` or `3` when `k = 4`, and no other `k` occurs. -/
theorem thm12 (x y g k : ℤ) (hx : 0 < x) (hy : 0 < y) (hg : 0 < g) (hc : IsCoprime x y)
    (h : (g * x) ^ 2 + 1 * (g * x) + (g * y) ^ 2 + 1 * (g * y) = k * (g * x) * (g * y)) :
    (k = 3 ∧ (k * x * y - x ^ 2 - y ^ 2 = 1 ∨ k * x * y - x ^ 2 - y ^ 2 = 5)) ∨
    (k = 4 ∧ (k * x * y - x ^ 2 - y ^ 2 = 2 ∨ k * x * y - x ^ 2 - y ^ 2 = 3)) := by
  have hs : Sol 1 (g * x) (g * y) k := ⟨mul_pos hg hx, mul_pos hg hy, h⟩
  have hk := k_range (by norm_num) hs
  obtain ⟨h1, hdvd⟩ := key 1 x y g k hx hy hg hc h
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = k * x * y - x ^ 2 - y ^ 2 := ⟨_, rfl⟩
  rw [← hm] at h1 hdvd ⊢
  have hmpos : 0 < m := by
    have h2 : 0 < g * m := by rw [h1]; omega
    nlinarith
  have hid : (x + y) ^ 2 + m = (k + 2) * x * y := by rw [hm]; ring
  have hk34 : k = 3 ∨ k = 4 := by omega
  rcases hk34 with rfl | rfl
  · left
    exact ⟨rfl, div5 hmpos (by simpa using hdvd)⟩
  · right
    refine ⟨rfl, ?_⟩
    rcases div6 hmpos (by simpa using hdvd) with rfl | rfl | rfl | rfl
    · exact absurd (by linear_combination hid) (no_4_1 x y)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd (by linear_combination hid) (no_4_6 x y)

/-! #### Two-periodicity and the values for fixed `r` -/

/-- `r (a + b) / gcd(a, b)^2`, as a rational number. -/
def normVal (r a b : ℤ) : ℚ := r * (a + b) / (Int.gcd a b : ℚ) ^ 2

theorem normVal_comm (r a b : ℤ) : normVal r a b = normVal r b a := by
  unfold normVal
  rw [Int.gcd_comm, add_comm (a : ℚ)]

/-- For `a = x g`, `b = y g` with `x, y` coprime, the value is `k x y - x^2 - y^2`. -/
theorem normVal_eq {r g x y k : ℤ} (hg : 0 < g) (hx : 0 < x) (hy : 0 < y) (hc : IsCoprime x y)
    (h : Sol r (x * g) (y * g) k) : normVal r (x * g) (y * g) = k * x * y - x ^ 2 - y ^ 2 := by
  obtain ⟨-, -, h⟩ := h
  obtain ⟨h1, -⟩ := key r x y g k hx hy hg hc (by linear_combination h)
  have hgcd : ((Int.gcd (x * g) (y * g) : ℕ) : ℚ) = (g : ℚ) := by
    have : ((Int.gcd (x * g) (y * g) : ℕ) : ℤ) = g := by
      rw [Int.gcd_mul_right, Int.isCoprime_iff_gcd_eq_one.mp hc, one_mul]
      exact Int.natAbs_of_nonneg hg.le
    exact_mod_cast this
  unfold normVal
  rw [hgcd, div_eq_iff (by positivity)]
  have h1q : (g : ℚ) * ((k : ℚ) * x * y - x ^ 2 - y ^ 2) = r * ((x : ℚ) + y) := by
    exact_mod_cast h1
  push_cast
  linear_combination -(g : ℚ) * h1q

/-- Two steps along a chain keep the value: if `c = k b - r - a` and `d = k c - r - b`, then
`(c, d)` has the same value `r (c + d) / gcd(c, d)^2` as `(a, b)`. -/
theorem two_periodic {r a b c d k : ℤ} (hr : 0 < r) (h : Sol r a b k)
    (hc : c = k * b - r - a) (hd : d = k * c - r - b) : normVal r c d = normVal r a b := by
  have hbc : Sol r b c k := hc ▸ h.next hr.le
  have hcd : Sol r c d k := hd ▸ hbc.next hr.le
  obtain ⟨ha, hb, hab⟩ := h
  obtain ⟨-, hc0, hbc⟩ := hbc
  obtain ⟨g, x, y, hg, hxy, rfl, rfl⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left b ha.ne')
  have hg' : (0 : ℤ) < g := by exact_mod_cast hg
  have hx : 0 < x := by
    by_contra hx
    push Not at hx
    nlinarith
  have hy : 0 < y := by
    by_contra hy
    push Not at hy
    nlinarith
  have hcop : IsCoprime x y := Int.isCoprime_iff_gcd_eq_one.mpr hxy
  have hcr : c + r = g * (k * y - x) := by rw [hc]; ring
  have hbd : y * g * d = c * (c + r) := by rw [hd]; linear_combination -hbc
  have hyd : y * d = c * (k * y - x) := by
    have : (g : ℤ) * (y * d - c * (k * y - x)) = 0 := by linear_combination hbd + c * hcr
    rcases mul_eq_zero.mp this with h0 | h0
    · omega
    · linarith
  have hcop' : IsCoprime y (k * y - x) := by
    obtain ⟨u, v, huv⟩ := hcop
    exact ⟨v + u * k, -u, by linear_combination huv⟩
  obtain ⟨t, rfl⟩ : y ∣ c := hcop'.dvd_of_dvd_mul_right ⟨d, hyd.symm⟩
  have hdt : d = (k * y - x) * t := by
    have : y * (d - (k * y - x) * t) = 0 := by linear_combination hyd
    rcases mul_eq_zero.mp this with h0 | h0
    · omega
    · linarith
  have ht : 0 < t := by
    by_contra ht
    push Not at ht
    nlinarith
  have hkyx : 0 < k * y - x := by
    by_contra hk
    push Not at hk
    nlinarith
  subst hdt
  rw [normVal_eq ht hy hkyx hcop' hcd, normVal_eq (k := k) hg' hx hy hcop ⟨ha, hb, hab⟩]
  push_cast
  ring

/-- The values on the chain through a solution `(a, b)`: that of `(a, b)` and that of its
neighbour `(a, k a - r - b)`. -/
def chainVals (r k a b : ℤ) : Set ℚ := {normVal r a b, normVal r a (k * a - r - b)}

theorem chainVals_jump (r k a b : ℤ) : chainVals r k a (k * a - r - b) = chainVals r k a b := by
  unfold chainVals
  rw [show k * a - r - (k * a - r - b) = b by ring, Set.pair_comm]

theorem chainVals_swap {r a b k : ℤ} (hr : 0 < r) (h : Sol r a b k) :
    chainVals r k b a = chainVals r k a b := by
  have hq : Sol r (k * a - r - b) a k := (h.symm.next hr.le).symm
  have h2 := two_periodic hr hq (c := b) (d := k * b - r - a) (by ring) rfl
  unfold chainVals
  rw [h2, normVal_comm r b a, normVal_comm r (k * a - r - b) a]

private theorem descent_chainVals_aux (r : ℤ) (hr : 0 < r) : ∀ n : ℕ, ∀ a b k : ℤ,
    a + b ≤ n → Sol r a b k →
    ∃ a' b', Sol r a' b' k ∧ Reduced r a' b' ∧ chainVals r k a b = chainVals r k a' b' := by
  intro n
  induction n with
  | zero =>
    intro a b k hn hs
    obtain ⟨ha, hb, -⟩ := hs
    omega
  | succ n ih =>
    intro a b k hn hs
    wlog hab : a ≤ b generalizing a b
    · obtain ⟨a', b', hs', hred, hv⟩ := this b a (by omega) hs.symm (by omega)
      exact ⟨a', b', hs', hred, (chainVals_swap hr hs.symm).trans hv⟩
    by_cases hred : b ^ 2 ≤ a ^ 2 + r * a
    · exact ⟨a, b, hs, ⟨hab, hred⟩, rfl⟩
    · push Not at hred
      have hs' := hs
      obtain ⟨ha, hb, h⟩ := hs'
      have hprod : b * (k * a - r - b) = a ^ 2 + r * a := by linear_combination -h
      have hpos : 0 < k * a - r - b := by
        by_contra hx
        push Not at hx
        nlinarith [mul_pos ha ha, mul_pos hr ha]
      have hlt : k * a - r - b < b := by nlinarith
      obtain ⟨a', b', hs', hred', hv⟩ :=
        ih a (k * a - r - b) k (by omega) ⟨ha, hpos, by linear_combination h⟩
      exact ⟨a', b', hs', hred', (chainVals_jump r k a b).symm.trans hv⟩

/-- Descent that keeps the chain values: every solution has the same `chainVals` as some
reduced solution with the same `k`. -/
theorem descent_chainVals {r a b k : ℤ} (hr : 0 < r) (h : Sol r a b k) :
    ∃ a' b', Sol r a' b' k ∧ Reduced r a' b' ∧ chainVals r k a b = chainVals r k a' b' := by
  have h0 := h
  obtain ⟨ha, hb, -⟩ := h0
  exact descent_chainVals_aux r hr (a + b).toNat a b k (by omega) h

/-- The values `r (a + b) / gcd(a, b)^2` over all solutions with a given `k` are exactly the
chain values of the reduced solutions with that `k`. -/
theorem values_eq {r k : ℤ} (hr : 0 < r) :
    {q | ∃ a b, Sol r a b k ∧ q = normVal r a b} =
      {q | ∃ a b, Sol r a b k ∧ Reduced r a b ∧ q ∈ chainVals r k a b} := by
  ext q
  constructor
  · rintro ⟨a, b, h, rfl⟩
    obtain ⟨a', b', h', hred, hv⟩ := descent_chainVals hr h
    exact ⟨a', b', h', hred, hv ▸ Set.mem_insert _ _⟩
  · rintro ⟨a, b, h, -, hq | hq⟩
    · exact ⟨a, b, h, hq⟩
    · exact ⟨a, k * a - r - b, h.symm.next hr.le, Set.mem_singleton_iff.mp hq⟩

theorem mem_values {r k : ℤ} (hr : 0 < r) (q : ℚ) :
    (∃ a b, Sol r a b k ∧ q = normVal r a b) ↔
      ∃ a b, Sol r a b k ∧ Reduced r a b ∧ q ∈ chainVals r k a b :=
  Set.ext_iff.mp (values_eq hr) q

/-! #### The tables for `r = 1, 2, 3` -/

theorem reduced_one {a b k : ℤ} (h : Sol 1 a b k) (hred : Reduced 1 a b) :
    (a = 1 ∧ b = 1 ∧ k = 4) ∨ (a = 2 ∧ b = 2 ∧ k = 3) := by
  obtain ⟨hd, ha⟩ := reduced_bounds (by norm_num) h hred
  obtain ⟨ha0, hb0, heq⟩ := h
  obtain ⟨hab, -⟩ := hred
  have hb1 : b ≤ a := by omega
  interval_cases a <;> interval_cases b <;> norm_num at heq <;> omega

theorem reduced_two {a b k : ℤ} (h : Sol 2 a b k) (hred : Reduced 2 a b) :
    (a = 1 ∧ b = 1 ∧ k = 6) ∨ (a = 2 ∧ b = 2 ∧ k = 4) ∨ (a = 4 ∧ b = 4 ∧ k = 3) := by
  obtain ⟨hd, ha⟩ := reduced_bounds (by norm_num) h hred
  obtain ⟨ha0, hb0, heq⟩ := h
  obtain ⟨hab, hb2⟩ := hred
  have hb1 : b ≤ a + 1 := by omega
  interval_cases a <;> interval_cases b <;> norm_num at heq <;> omega

theorem reduced_three {a b k : ℤ} (h : Sol 3 a b k) (hred : Reduced 3 a b) :
    (a = 1 ∧ b = 1 ∧ k = 8) ∨ (a = 1 ∧ b = 2 ∧ k = 7) ∨ (a = 2 ∧ b = 2 ∧ k = 5) ∨
      (a = 3 ∧ b = 3 ∧ k = 4) ∨ (a = 6 ∧ b = 6 ∧ k = 3) := by
  obtain ⟨hd, ha⟩ := reduced_bounds (by norm_num) h hred
  obtain ⟨ha0, hb0, heq⟩ := h
  obtain ⟨hab, hb2⟩ := hred
  have hb1 : b ≤ a + 1 := by omega
  interval_cases a <;> interval_cases b <;> norm_num at heq <;> omega

/-- `r = 1`: the values are `1, 5` for `k = 3` and `2, 3` for `k = 4`, and no other `k`
occurs (the paper's Theorem 1.2). -/
theorem values_one (k : ℤ) (q : ℚ) : (∃ a b, Sol 1 a b k ∧ q = normVal 1 a b) ↔
    (k = 3 ∧ (q = 1 ∨ q = 5)) ∨ (k = 4 ∧ (q = 2 ∨ q = 3)) := by
  rw [mem_values (by norm_num)]
  constructor
  · rintro ⟨a, b, h, hred, hq⟩
    rcases reduced_one h hred with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      norm_num [chainVals, normVal] at hq ⊢ <;> tauto
  · rintro (⟨rfl, hq⟩ | ⟨rfl, hq⟩)
    · exact ⟨2, 2, by norm_num [Sol], by norm_num [Reduced], by
        norm_num [chainVals, normVal]; tauto⟩
    · exact ⟨1, 1, by norm_num [Sol], by norm_num [Reduced], by
        norm_num [chainVals, normVal]; tauto⟩

/-- `r = 2`: the values are `1, 5` for `k = 3`, `2, 3` for `k = 4` and `4, 8` for `k = 6`, and no
other `k` occurs. This is Conjecture 4.2 again, by a second route (no congruences). -/
theorem values_two (k : ℤ) (q : ℚ) : (∃ a b, Sol 2 a b k ∧ q = normVal 2 a b) ↔
    (k = 3 ∧ (q = 1 ∨ q = 5)) ∨ (k = 4 ∧ (q = 2 ∨ q = 3)) ∨ (k = 6 ∧ (q = 4 ∨ q = 8)) := by
  rw [mem_values (by norm_num)]
  constructor
  · rintro ⟨a, b, h, hred, hq⟩
    rcases reduced_two h hred with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      norm_num [chainVals, normVal] at hq ⊢ <;> tauto
  · rintro (⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩)
    · exact ⟨4, 4, by norm_num [Sol], by norm_num [Reduced], by
        norm_num [chainVals, normVal]; tauto⟩
    · exact ⟨2, 2, by norm_num [Sol], by norm_num [Reduced], by
        norm_num [chainVals, normVal]; tauto⟩
    · exact ⟨1, 1, by norm_num [Sol], by norm_num [Reduced], by
        norm_num [chainVals, normVal]; tauto⟩

/-- `r = 3`: the values are `1, 5` for `k = 3`, `2, 3` for `k = 4`, `3, 21` for `k = 5`, `9` for
`k = 7` and `6, 15` for `k = 8`, and no other `k` occurs. -/
theorem values_three (k : ℤ) (q : ℚ) : (∃ a b, Sol 3 a b k ∧ q = normVal 3 a b) ↔
    (k = 3 ∧ (q = 1 ∨ q = 5)) ∨ (k = 4 ∧ (q = 2 ∨ q = 3)) ∨ (k = 5 ∧ (q = 3 ∨ q = 21)) ∨
      (k = 7 ∧ q = 9) ∨ (k = 8 ∧ (q = 6 ∨ q = 15)) := by
  rw [mem_values (by norm_num)]
  constructor
  · rintro ⟨a, b, h, hred, hq⟩
    rcases reduced_three h hred with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      norm_num [chainVals, normVal] at hq ⊢ <;> tauto
  · rintro (⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩)
    · exact ⟨6, 6, by norm_num [Sol], by norm_num [Reduced], by
        norm_num [chainVals, normVal]; tauto⟩
    · exact ⟨3, 3, by norm_num [Sol], by norm_num [Reduced], by
        norm_num [chainVals, normVal]; tauto⟩
    · exact ⟨2, 2, by norm_num [Sol], by norm_num [Reduced], by
        norm_num [chainVals, normVal]; tauto⟩
    · exact ⟨1, 2, by norm_num [Sol], by norm_num [Reduced], by
        norm_num [chainVals, normVal]; tauto⟩
    · exact ⟨1, 1, by norm_num [Sol], by norm_num [Reduced], by
        norm_num [chainVals, normVal]; tauto⟩

/-- For `r = 11` the value `11` occurs with `k = 3`, so the values for `k = 3` are not `{1, 5}`
for every `r`. -/
theorem eleven_three : Sol 11 21 28 3 ∧ normVal 11 21 28 = 11 :=
  ⟨by norm_num [Sol], by norm_num [normVal]⟩

end GeneralR

end AgenticConjectures.VietaR2Gcd
