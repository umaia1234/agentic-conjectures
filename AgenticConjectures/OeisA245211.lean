import Mathlib

/-!
# OEIS A245211 — necessary conditions for `a(n) = n`

A245211 is `a(n) = ∑_{d ∣ n, d < n} d τ(d)`, with `τ` the number of divisors. The OEIS entry
conjectures that `21` is the only solution of `a(n) = n`; that conjecture is open and is
recorded here as `statement` (a `Prop`, never proved).

This module formalizes the proved partial results of `problems/oeis-a245211/DETAILS.md`,
Sections 1–3, 5 and 6:

* `(A245-1)`, the product form: `a n = n ↔ W n = n (τ(n) + 1)`, where `W n = ∑_{d ∣ n} d τ(d)`
  is multiplicative with `W (p^k) = H_k(p) = ∑_{j ≤ k} (j + 1) p^j` (`a_eq_self_iff`, `W_mul`,
  `W_prime_pow`);
* `(A245-2)`, the lower bound: `τ(n / p) < p` for every prime factor `p` of a solution `n ≠ p`
  (`card_divisors_div_lt`, `lower_bound`);
* Section 3: no prime power is a solution (`a_prime_pow_ne`);
* Section 5, squarefree solutions: `21` is the only one with two prime factors
  (`a_mul_eq_self_iff`), none has three (`a_mul_mul_ne`) or an even number `≥ 4`
  (`squarefree_even`), so any other has an odd number `≥ 5` of prime factors (`squarefree_card`);
* Section 6, small prime factors: every solution is odd (`odd_of_a_eq_self`), `21` is the only
  solution divisible by `3` or by `7` (`eq_21_of_three_dvd`, `eq_21_of_seven_dvd`), none is
  divisible by `5` or `11` (`not_five_dvd`, `not_eleven_dvd`); hence `(A245-12)`: every solution
  other than `21` is coprime to `2310 = 2 · 3 · 5 · 7 · 11` (`coprime_2310`), and its least prime
  factor is at least `13` (`thirteen_le_minFac`).

The exact computations (all `n ≤ 10^9`; two prime factors with exponents `≤ 200`, Section 7) are
not formalized.

## Correspondence with the upstream snapshot

* `a` is the upstream definition of `problems/oeis-a245211/upstream/245211_cbf46b82.lean`, copied
  term for term: the sum of `d τ(d)` over all divisors minus the term `n τ(n)`, in `ℕ`. That
  subtraction never truncates (`self_mul_le_W`), so `a n` is the proper-divisor sum of the OEIS
  name (`a_eq_sum_properDivisors`). At `n = 0` every sum is empty; like upstream, `statement`
  quantifies over `0 < n`.
* `statement` is the upstream `oeis_245211_conjecture_0`, `∀ n, 0 < n → (a n = n ↔ n = 21)`.
  `a_21` checks `a 21 = 21` by `decide`.
* Every partial result is stated for the upstream `a`, from the hypothesis `a n = n` (and `0 < n`
  where it matters); no theorem changes the conjecture.

## Deviations from `DETAILS.md`

The statements are those of `DETAILS.md`; some proofs differ.

* Section 3 uses `H_k(p) ≡ 1 (mod p)` (`coprime_H`): `(A245-1)` for `n = p^k`, `k ≥ 1`, gives
  `p ∣ H_k(p)`. `DETAILS.md` bounds `(A245-4)` instead.
* Section 6 runs through one lemma, `reduce`, which peels prime factors off `n` and bounds the
  exponents with `(A245-2)`. `DETAILS.md` then filters the exponent patterns with the 2-adic
  condition `(A245-7)`; the Lean proof instead refutes every pattern that `(A245-2)` allows,
  using the linear equations for `q`, the divisibility `q^b ∣ H_a(p)` `(A245-14)`, and `(A245-1)`
  modulo 2. The 2-adic valuation identity `(A245-5)` of Section 4 is not formalized.
* For even `r ≥ 4`, `3 ∤ n` comes from Section 6 (a solution divisible by `3` is `21`, which has
  two prime factors) rather than from the bound `p_i > 2^(r-1)`.
-/

namespace AgenticConjectures.OeisA245211

open Nat Finset

/-- A245211, the upstream definition term for term: `∑_{d ∣ n} d τ(d) - n τ(n)` in `ℕ`. -/
noncomputable def a (n : ℕ) : ℕ :=
  let full_sum := (Nat.divisors n).sum (fun d => d * (Nat.divisors d).card)
  let self_term := n * (Nat.divisors n).card
  full_sum - self_term

/-- The A245211 conjecture (upstream `oeis_245211_conjecture_0`; open, not proved here):
`21` is the only positive `n` with `a n = n`. -/
def statement : Prop := ∀ n : ℕ, 0 < n → (a n = n ↔ n = 21)

/-- The full divisor sum `W n = ∑_{d ∣ n} d τ(d)`, so that `a n = W n - n τ(n)`. -/
def W (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d * #d.divisors

/-- `H k x = ∑_{j ≤ k} (j + 1) x^j`, written `H_k(x)` in `DETAILS.md`; `W (p^k) = H k p`. -/
def H (k x : ℕ) : ℕ := ∑ j ∈ range (k + 1), (j + 1) * x ^ j

theorem a_eq_W_sub (n : ℕ) : a n = W n - n * #n.divisors := rfl

theorem self_mul_le_W (n : ℕ) : n * #n.divisors ≤ W n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact single_le_sum (f := fun d => d * #d.divisors) (fun _ _ => Nat.zero_le _)
      (Nat.mem_divisors_self n hn.ne')

theorem a_eq_self_iff (n : ℕ) : a n = n ↔ W n = n * (#n.divisors + 1) := by
  have := self_mul_le_W n
  rw [a_eq_W_sub, mul_add, mul_one]
  omega

theorem a_eq_sum_properDivisors (n : ℕ) : a n = ∑ d ∈ n.properDivisors, d * #d.divisors := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a]
  · have h := sum_cons (f := fun d => d * #d.divisors) (Nat.self_notMem_properDivisors (n := n))
    rw [Nat.cons_self_properDivisors hn.ne'] at h
    rw [a_eq_W_sub, W, h]
    omega

/-- `W = (id · σ₀) * ζ` as an arithmetic function. -/
theorem W_eq (k : ℕ) : W k = ((ArithmeticFunction.id.pmul (ArithmeticFunction.sigma 0)) *
    ArithmeticFunction.zeta) k := by
  rw [ArithmeticFunction.mul_zeta_apply, W]
  simp [ArithmeticFunction.pmul_apply, ArithmeticFunction.sigma_zero_apply]

theorem isMultiplicative_W : ((ArithmeticFunction.id.pmul (ArithmeticFunction.sigma 0)) *
    ArithmeticFunction.zeta).IsMultiplicative :=
  (ArithmeticFunction.isMultiplicative_id.pmul ArithmeticFunction.isMultiplicative_sigma).mul
    ArithmeticFunction.isMultiplicative_zeta

theorem W_mul {m n : ℕ} (h : m.Coprime n) : W (m * n) = W m * W n := by
  rw [W_eq, W_eq, W_eq]
  exact isMultiplicative_W.map_mul_of_coprime h

theorem card_divisors_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : #(p ^ k).divisors = k + 1 := by
  rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hp]

theorem W_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : W (p ^ k) = H k p := by
  rw [W, Nat.divisors_prime_pow hp, sum_map, H]
  refine sum_congr rfl fun j _ => ?_
  simp only [Function.Embedding.coeFn_mk, card_divisors_prime_pow hp]
  ring

theorem W_pow_mul {p m : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) (k : ℕ) :
    W (p ^ k * m) = H k p * W m := by
  rw [W_mul ((hp.coprime_iff_not_dvd.2 hpm).pow_left k), W_prime_pow hp]

theorem card_divisors_pow_mul {p m : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) (k : ℕ) :
    #(p ^ k * m).divisors = (k + 1) * #m.divisors := by
  rw [Nat.Coprime.card_divisors_mul ((hp.coprime_iff_not_dvd.2 hpm).pow_left k),
    card_divisors_prime_pow hp]

theorem H_eq (k x : ℕ) : H k x = 1 + x * ∑ j ∈ range k, (j + 2) * x ^ j := by
  rw [H, sum_range_succ', mul_sum, add_comm, zero_add, pow_zero, mul_one]
  exact congrArg (1 + ·) (sum_congr rfl fun j _ => by ring)

theorem coprime_H (k x : ℕ) : x.Coprime (H k x) := by
  rw [H_eq, mul_comm x, Nat.coprime_add_mul_right_right]
  exact Nat.coprime_one_right x

theorem H_one (x : ℕ) : H 1 x = 1 + 2 * x := by
  simp [H, sum_range_succ]

theorem card_divisors_div_lt {n p : ℕ} (h : a n = n) (hp : p.Prime) (hpn : p ∣ n)
    (hnp : n ≠ p) : #(n / p).divisors < p := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hp.pos]
  obtain ⟨m, rfl⟩ := hpn
  have hp1 := hp.one_lt
  have hm : 0 < m := Nat.pos_of_mul_pos_left hn
  rw [Nat.mul_div_cancel_left m hp.pos]
  have hm1 : m ≠ 1 := by rintro rfl; simp at hnp
  have h1 : 1 ∈ (p * m).properDivisors := Nat.mem_properDivisors.2 ⟨one_dvd _, by nlinarith⟩
  have h2 : m ∈ (p * m).properDivisors :=
    Nat.mem_properDivisors.2 ⟨dvd_mul_left _ _, by nlinarith⟩
  have := add_le_sum (f := fun d => d * #d.divisors) (fun _ _ => Nat.zero_le _) h1 h2
    (Ne.symm hm1)
  rw [← a_eq_sum_properDivisors, h] at this
  simp only [Nat.divisors_one, card_singleton, mul_one] at this
  have : m * #m.divisors < m * p := by nlinarith
  exact Nat.lt_of_mul_lt_mul_left this

theorem a_prime_pow_ne {p : ℕ} (hp : p.Prime) (k : ℕ) : a (p ^ k) ≠ p ^ k := by
  intro h
  rw [a_eq_self_iff, W_prime_pow hp, card_divisors_prime_pow hp] at h
  rcases k with _ | k
  · simp [H] at h
  · have h1 : p ∣ H (k + 1) p := ⟨p ^ k * (k + 1 + 1 + 1), by rw [h]; ring⟩
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (coprime_H (k + 1) p) h1)

theorem lower_bound {p m k : ℕ} (h : a (p ^ (k + 1) * m) = p ^ (k + 1) * m) (hp : p.Prime)
    (hpm : ¬ p ∣ m) : (k + 1) * #m.divisors < p := by
  have hne : p ^ (k + 1) * m ≠ p := by
    rintro he
    rw [he] at h
    exact a_prime_pow_ne hp 1 (by simpa using h)
  have := card_divisors_div_lt h hp (dvd_mul_of_dvd_left (dvd_pow_self p k.succ_ne_zero) m) hne
  rwa [show p ^ (k + 1) * m / p = p ^ k * m by
    rw [pow_succ, mul_comm (p ^ k) p, mul_assoc, Nat.mul_div_cancel_left _ hp.pos],
    card_divisors_pow_mul hp hpm] at this

theorem a_21 : a 21 = 21 := by decide

theorem W_prime {p : ℕ} (hp : p.Prime) : W p = 1 + 2 * p := by
  simpa [H_one] using W_prime_pow hp 1

theorem card_divisors_prime {p : ℕ} (hp : p.Prime) : #p.divisors = 2 := by
  simpa using card_divisors_prime_pow hp 1

/-- Section 5, `r = 2`: the only squarefree semiprime solution is `21`. -/
theorem a_mul_eq_self_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    a (p * q) = p * q ↔ p * q = 21 := by
  refine ⟨fun h => ?_, fun h => by rw [h]; exact a_21⟩
  have hpq' : ¬ p ∣ q := fun hd => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 hd)
  have hW := W_pow_mul hp hpq' 1
  have hτ := card_divisors_pow_mul hp hpq' 1
  rw [pow_one] at hW hτ
  rw [a_eq_self_iff, hW, hτ, H_one, W_prime hq, card_divisors_prime hq] at h
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
  have key : p' * q' = 5 := by nlinarith
  rcases (Nat.dvd_prime (by norm_num)).1 (Dvd.intro q' key) with h1 | h1 <;> subst h1 <;> omega

theorem two_le_card_divisors {m : ℕ} (hm : 2 ≤ m) : 2 ≤ #m.divisors := by
  have : ({1, m} : Finset ℕ) ⊆ m.divisors := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp <;> omega
  have := card_le_card this
  rwa [card_pair (by omega)] at this

theorem one_le_card_divisors {m : ℕ} (hm : m ≠ 0) : 1 ≤ #m.divisors :=
  card_pos.2 ⟨1, by simp [hm]⟩

theorem W_one : W 1 = 1 := by simp [W]

theorem exists_pow_succ_mul {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn : n ≠ 0) :
    ∃ k m, ¬ p ∣ m ∧ n = p ^ (k + 1) * m := by
  obtain ⟨e, m, hpm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  rcases e with _ | k
  · rw [pow_zero, one_mul] at he
    exact absurd (he ▸ hpn) hpm
  · exact ⟨k, m, hpm, he⟩

theorem exists_peel {m : ℕ} (hm : 1 < m) :
    ∃ q b m', q.Prime ∧ ¬ q ∣ m' ∧ m = q ^ (b + 1) * m' := by
  obtain ⟨b, m', h1, h2⟩ :=
    exists_pow_succ_mul (Nat.minFac_prime hm.ne') (Nat.minFac_dvd m) (by omega)
  exact ⟨_, b, m', Nat.minFac_prime hm.ne', h1, h2⟩

/-- Every solution is odd (Section 6, prime factor 2). -/
theorem odd_of_a_eq_self {n : ℕ} (h : a n = n) (hn : 0 < n) : Odd n := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ho
  · exfalso
    have h2 : (m + m) ≠ 2 := fun he => by
      rw [he] at h; exact a_prime_pow_ne Nat.prime_two 1 (by simpa using h)
    have := card_divisors_div_lt h Nat.prime_two ⟨m, by ring⟩ h2
    rw [show (m + m) / 2 = m by omega, Nat.lt_succ_iff, ← not_lt] at this
    apply this
    rcases Nat.lt_or_ge m 2 with hm | hm
    · omega
    · exact two_le_card_divisors hm
  · exact ho

/-- Section 6, prime factor 3: a solution divisible by 3 is `21`. -/
theorem eq_21_of_three_dvd {n : ℕ} (h : a n = n) (hn : 0 < n) (h3 : 3 ∣ n) : n = 21 := by
  obtain ⟨k, m, h3m, rfl⟩ := exists_pow_succ_mul Nat.prime_three h3 hn.ne'
  have hb := lower_bound h Nat.prime_three h3m
  have hm0 : m ≠ 0 := by rintro rfl; simp at hn
  rcases (show m = 1 ∨ 1 < m by omega) with rfl | hm1
  · exact absurd (by simpa using h) (a_prime_pow_ne Nat.prime_three (k + 1))
  obtain ⟨q, b, m₁, hq, hqm₁, rfl⟩ := exists_peel hm1
  rw [card_divisors_pow_mul hq hqm₁] at hb
  have hm₁0 : m₁ ≠ 0 := by rintro rfl; simp at hm1
  have ht := one_le_card_divisors hm₁0
  have h2 := Nat.mul_le_mul_left (b + 1 + 1) ht
  have h4 := Nat.mul_le_mul_left (k + 1) (show 2 ≤ (b + 1 + 1) * #m₁.divisors by omega)
  obtain rfl : k = 0 := by omega
  obtain rfl : b = 0 := by omega
  have h1 : #m₁.divisors = 1 := by omega
  rw [Nat.divisors_card_eq_one_iff] at h1
  subst h1
  have hq3 : q ≠ 3 := by rintro rfl; exact h3m (by simp)
  simp only [zero_add, pow_one, mul_one] at h ⊢
  exact (a_mul_eq_self_iff Nat.prime_three hq (Ne.symm hq3)).1 h

/-- The case analysis of Section 6. Let `n` be an odd solution with `3 ∤ n`, and `p ≤ 11` a
prime factor of `n`. By `(A245-2)`, `n` is `p^(k+1) q^(b+1)`, `p^(k+1) q^(b+1) r^(c+1)` or
`p q r s` for distinct primes `q, r, s ≥ 5` prime to `3`, and `(A245-1)` becomes the equation in
`two`, `three` or `four` respectively; refuting these shapes refutes `p ∣ n`. -/
theorem reduce {n p : ℕ} (hp : p.Prime) (hp11 : p ≤ 11) (h : a n = n) (hn : 0 < n)
    (hpn : p ∣ n) (hodd : Odd n) (h3 : ¬ 3 ∣ n)
    (two : ∀ k b q, q.Prime → q ≠ p → 5 ≤ q → ¬ 3 ∣ q → (k + 1) * (b + 2) < p →
      H (k + 1) p * H (b + 1) q = p ^ (k + 1) * q ^ (b + 1) * ((k + 2) * (b + 2) + 1) → False)
    (three : ∀ k b c q r, q.Prime → r.Prime → q ≠ p → r ≠ p → q ≠ r → 5 ≤ q → 5 ≤ r →
      (k + 1) * ((b + 2) * (c + 2)) < p →
      H (k + 1) p * (H (b + 1) q * H (c + 1) r) =
        p ^ (k + 1) * (q ^ (b + 1) * r ^ (c + 1)) * ((k + 2) * ((b + 2) * (c + 2)) + 1) → False)
    (four : ∀ q r s, q.Prime → r.Prime → s.Prime → ¬ 3 ∣ q → ¬ 3 ∣ r → ¬ 3 ∣ s → 8 < p →
      H 1 p * (H 1 q * (H 1 r * H 1 s)) = p * (q * (r * s)) * 17 → False) : False := by
  have hdiv : ∀ q, q.Prime → q ∣ n → 5 ≤ q ∧ ¬ 3 ∣ q := fun q hq hqn => by
    have h3q : ¬ 3 ∣ q := fun h3q => h3 (h3q.trans hqn)
    have hq2 : q ≠ 2 := by rintro rfl; exact (Nat.not_even_iff_odd.2 (hodd.of_dvd_nat hqn)) even_two
    have := hq.two_le
    refine ⟨?_, h3q⟩
    by_contra hlt
    interval_cases q
    · exact hq2 rfl
    · exact h3q (dvd_refl 3)
    · norm_num at hq
  obtain ⟨k, m, hpm, rfl⟩ := exists_pow_succ_mul hp hpn hn.ne'
  have hb := lower_bound h hp hpm
  have hE := (a_eq_self_iff _).1 h
  rw [W_pow_mul hp hpm, card_divisors_pow_mul hp hpm] at hE
  have hm0 : m ≠ 0 := by rintro rfl; simp at hn
  rcases (show m = 1 ∨ 1 < m by omega) with rfl | hm1
  · exact absurd (by simpa using h) (a_prime_pow_ne hp (k + 1))
  obtain ⟨q, b, m₁, hq, hqm₁, rfl⟩ := exists_peel hm1
  have hqn : q ∣ p ^ (k + 1) * (q ^ (b + 1) * m₁) :=
    Dvd.dvd.mul_left (dvd_mul_of_dvd_left (dvd_pow_self q b.succ_ne_zero) _) _
  obtain ⟨hq5, hq3⟩ := hdiv q hq hqn
  have hqp : q ≠ p := by
    rintro rfl; exact hpm (dvd_mul_of_dvd_left (dvd_pow_self _ b.succ_ne_zero) _)
  have hpm₁ : ¬ p ∣ m₁ := fun hd => hpm (dvd_mul_of_dvd_right hd _)
  rw [W_pow_mul hq hqm₁, card_divisors_pow_mul hq hqm₁] at hE
  rw [card_divisors_pow_mul hq hqm₁] at hb
  have hm₁0 : m₁ ≠ 0 := by rintro rfl; simp at hm1
  rcases (show m₁ = 1 ∨ 1 < m₁ by omega) with rfl | hm₁1
  · simp only [W_one, mul_one, Nat.divisors_one, card_singleton] at hE hb
    exact two k b q hq hqp hq5 hq3 hb (by convert hE using 2)
  obtain ⟨r, c, m₂, hr, hrm₂, rfl⟩ := exists_peel hm₁1
  have hrn : r ∣ p ^ (k + 1) * (q ^ (b + 1) * (r ^ (c + 1) * m₂)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_mul_of_dvd_left (dvd_pow_self r c.succ_ne_zero) _) _) _
  obtain ⟨hr5, hr3⟩ := hdiv r hr hrn
  have hrp : r ≠ p := by
    rintro rfl; exact hpm₁ (dvd_mul_of_dvd_left (dvd_pow_self _ c.succ_ne_zero) _)
  have hqr : q ≠ r := by
    rintro rfl; exact hqm₁ (dvd_mul_of_dvd_left (dvd_pow_self _ c.succ_ne_zero) _)
  have hpm₂ : ¬ p ∣ m₂ := fun hd => hpm₁ (dvd_mul_of_dvd_right hd _)
  have hqm₂ : ¬ q ∣ m₂ := fun hd => hqm₁ (dvd_mul_of_dvd_right hd _)
  rw [W_pow_mul hr hrm₂, card_divisors_pow_mul hr hrm₂] at hE
  rw [card_divisors_pow_mul hr hrm₂] at hb
  have hm₂0 : m₂ ≠ 0 := by rintro rfl; simp at hm₁1
  rcases (show m₂ = 1 ∨ 1 < m₂ by omega) with rfl | hm₂1
  · simp only [W_one, mul_one, Nat.divisors_one, card_singleton] at hE hb
    exact three k b c q r hq hr hqp hrp hqr hq5 hr5 hb (by convert hE using 2)
  obtain ⟨s, d, m₃, hs, hsm₃, rfl⟩ := exists_peel hm₂1
  have hsn : s ∣ p ^ (k + 1) * (q ^ (b + 1) * (r ^ (c + 1) * (s ^ (d + 1) * m₃))) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left
      (dvd_mul_of_dvd_left (dvd_pow_self s d.succ_ne_zero) _) _) _) _
  obtain ⟨-, hs3⟩ := hdiv s hs hsn
  rw [W_pow_mul hs hsm₃, card_divisors_pow_mul hs hsm₃] at hE
  rw [card_divisors_pow_mul hs hsm₃] at hb
  have hm₃0 : m₃ ≠ 0 := by rintro rfl; simp at hm₂1
  have ht := one_le_card_divisors hm₃0
  have e1 := Nat.mul_le_mul_left (d + 1 + 1) ht
  have e2 := Nat.mul_le_mul_left (c + 1 + 1) (show 2 ≤ (d + 1 + 1) * #m₃.divisors by omega)
  have e3 := Nat.mul_le_mul_left (b + 1 + 1)
    (show 4 ≤ (c + 1 + 1) * ((d + 1 + 1) * #m₃.divisors) by omega)
  have e4 := Nat.mul_le_mul_left (k + 1)
    (show 8 ≤ (b + 1 + 1) * ((c + 1 + 1) * ((d + 1 + 1) * #m₃.divisors)) by omega)
  obtain rfl : k = 0 := by omega
  obtain rfl : b = 0 := by omega
  obtain rfl : c = 0 := by omega
  obtain rfl : d = 0 := by omega
  have h1 : #m₃.divisors = 1 := by omega
  rw [Nat.divisors_card_eq_one_iff] at h1
  subst h1
  simp only [W_one, mul_one, Nat.divisors_one, card_singleton, zero_add, pow_one] at hE hb
  exact four q r s hq hr hs hq3 hr3 hs3 (by omega) (by convert hE using 2)

/-- `(A245-14)`: in `H e p * H f q = p^e q^f D`, the factor `q^f` divides `H e p`. -/
theorem pow_dvd_of_eq {p q e f D : ℕ} (h : H e p * H f q = p ^ e * q ^ f * D) :
    q ^ f ∣ H e p :=
  ((coprime_H f q).pow_left f).dvd_of_dvd_mul_right ⟨p ^ e * D, by rw [h]; ring⟩

/-- Section 5, `r = 3`, after `z ∣ 2x + 1` forced `z = 2x + 1`: `(x - 6)(y - 4) = 27`. -/
theorem three_core {x y z : ℕ} (hx : x.Prime) (hz : z.Prime) (hy5 : 5 ≤ y) (hyz : y < z)
    (hzx : z = 1 + 2 * x) (h : (1 + 2 * y) * (3 + 4 * x) = 9 * x * y) : False := by
  subst hzx
  have hx7 : 7 ≤ x := by nlinarith
  have hx33 : x ≤ 33 := by nlinarith
  interval_cases x <;> first | omega | norm_num at hx

/-- Section 5, `r = 3`, with `z` the largest of the three primes. -/
theorem three_max {x y z : ℕ} (hx : x.Prime) (hy : y.Prime) (hz : z.Prime) (hx5 : 5 ≤ x)
    (hy5 : 5 ≤ y) (hxz : x < z) (hyz : y < z)
    (h : (1 + 2 * x) * (1 + 2 * y) * (1 + 2 * z) = x * y * z * 9) : False := by
  have hcop : z.Coprime (1 + 2 * z) := by
    rw [Nat.coprime_add_mul_right_right]; exact Nat.coprime_one_right z
  have hdvd : z ∣ (1 + 2 * x) * (1 + 2 * y) :=
    hcop.dvd_of_dvd_mul_right ⟨x * y * 9, by rw [h]; ring⟩
  rcases (Nat.Prime.dvd_mul hz).1 hdvd with ⟨c, hc⟩ | ⟨c, hc⟩
  · obtain rfl : c = 1 := by
      rcases c with _ | _ | c
      · omega
      · rfl
      · nlinarith
    rw [mul_one] at hc
    refine three_core hx hz hy5 hyz hc.symm (Nat.eq_of_mul_eq_mul_left (by omega : 0 < z) ?_)
    rw [← hc] at h ⊢
    nlinarith [h]
  · obtain rfl : c = 1 := by
      rcases c with _ | _ | c
      · omega
      · rfl
      · nlinarith
    rw [mul_one] at hc
    refine three_core hy hz hx5 hxz hc.symm (Nat.eq_of_mul_eq_mul_left (by omega : 0 < z) ?_)
    rw [← hc] at h ⊢
    nlinarith [h]

/-- Section 5, `r = 3`: three distinct primes `≥ 5` never satisfy
`(2x+1)(2y+1)(2z+1) = 9xyz`, the equation `(A245-10)`. -/
theorem three_prime_eq_false {x y z : ℕ} (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (hx5 : 5 ≤ x) (hy5 : 5 ≤ y) (hz5 : 5 ≤ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : (1 + 2 * x) * (1 + 2 * y) * (1 + 2 * z) = x * y * z * 9) : False := by
  have hy' : (1 + 2 * x) * (1 + 2 * z) * (1 + 2 * y) = x * z * y * 9 := by linarith [h]
  have hx' : (1 + 2 * y) * (1 + 2 * z) * (1 + 2 * x) = y * z * x * 9 := by linarith [h]
  rcases lt_or_gt_of_ne hxz with h1 | h1 <;> rcases lt_or_gt_of_ne hyz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hxy with h3 | h3
  · exact three_max hx hy hz hx5 hy5 h1 h2 h
  · exact three_max hx hy hz hx5 hy5 h1 h2 h
  · exact three_max hx hz hy hx5 hz5 h3 h2 hy'
  · omega
  · omega
  · exact three_max hy hz hx hy5 hz5 h3 h1 hx'
  · exact three_max hx hz hy hx5 hz5 h3 h2 hy'
  · exact three_max hy hz hx hy5 hz5 h3 h1 hx'

/-- Section 6, prime factor 11, pattern `(1; 1, 4)`: `n = 11 q r^4` is impossible. -/
theorem eleven_q_r4 {q r : ℕ} (hr : r.Prime)
    (h : 23 * ((1 + 2 * q) * H 4 r) = 11 * (q * r ^ 4) * 21) : False := by
  have hB : H 4 r = 1 + 2 * r + 3 * r ^ 2 + 4 * r ^ 3 + 5 * r ^ 4 := by
    simp only [H, sum_range_succ, sum_range_zero]; ring
  have key : q * r ^ 4 = 23 * H 4 r + q * (184 * r ^ 3 + 138 * r ^ 2 + 92 * r + 46) := by
    rw [hB] at h ⊢; nlinarith [h]
  have hr185 : 185 ≤ r := by
    by_contra hlt
    have h4 : r ^ 4 ≤ 184 * r ^ 3 := by
      calc r ^ 4 = r * r ^ 3 := by ring
        _ ≤ 184 * r ^ 3 := Nat.mul_le_mul_right _ (by omega)
    have := Nat.mul_le_mul_left q h4
    have : 1 ≤ H 4 r := by rw [hB]; omega
    nlinarith
  have hdvd : r ^ 4 ∣ 1 + 2 * q := by
    have h1 : r ^ 4 ∣ 23 * ((1 + 2 * q) * H 4 r) := ⟨11 * q * 21, by rw [h]; ring⟩
    have hc23 : (r ^ 4).Coprime 23 :=
      ((Nat.coprime_primes hr (by norm_num)).2 (by omega)).pow_left 4
    exact ((coprime_H 4 r).pow_left 4).dvd_of_dvd_mul_right (hc23.dvd_of_dvd_mul_left h1)
  have hle : r ^ 4 ≤ 1 + 2 * q := Nat.le_of_dvd (by omega) hdvd
  have h1 : 185 * r ≤ r ^ 2 := by nlinarith
  have h2 : 185 * r ^ 2 ≤ r ^ 3 := by
    calc 185 * r ^ 2 ≤ r * r ^ 2 := Nat.mul_le_mul_right _ hr185
      _ = r ^ 3 := by ring
  have h3 : 185 * r ^ 3 ≤ r ^ 4 := by
    calc 185 * r ^ 3 ≤ r * r ^ 3 := Nat.mul_le_mul_right _ hr185
      _ = r ^ 4 := by ring
  have hK : 184 * r ^ 3 + 138 * r ^ 2 + 92 * r + 46 + 1000 ≤ r ^ 4 := by omega
  have hB6 : H 4 r ≤ 6 * r ^ 4 := by rw [hB]; omega
  have := Nat.mul_le_mul_left q hK
  nlinarith

/-- Section 6, prime factor 11, pattern `(1; 1, 1, 1)`: the mod-3 argument of the even-`r`
squarefree case, for `n = 11 q r s` with `q, r, s` prime to 3. -/
theorem eleven_qrs {q r s : ℕ} (hq : ¬ 3 ∣ q) (hr : ¬ 3 ∣ r) (hs : ¬ 3 ∣ s)
    (h : 23 * ((1 + 2 * q) * ((1 + 2 * r) * (1 + 2 * s))) = 11 * (q * (r * s)) * 17) :
    False := by
  have h3 := congrArg (Nat.cast : ℕ → ZMod 3) h
  push_cast at h3
  have hq' : (q : ZMod 3) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hr' : (r : ZMod 3) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hs' : (s : ZMod 3) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  generalize (q : ZMod 3) = x at h3 hq'
  generalize (r : ZMod 3) = y at h3 hr'
  generalize (s : ZMod 3) = z at h3 hs'
  revert x y z
  decide

theorem cast_H_two {x : ℕ} (hx : Odd x) (k : ℕ) :
    ((H k x : ℕ) : ZMod 2) = ∑ j ∈ range (k + 1), ((j + 1 : ℕ) : ZMod 2) := by
  simp [H, hx.natCast_zmod_two]

/-- Section 6, prime factor 5: no solution is divisible by 5. -/
theorem not_five_dvd {n : ℕ} (h : a n = n) (hn : 0 < n) : ¬ 5 ∣ n := by
  intro h5
  have h3 : ¬ 3 ∣ n := fun h3 => by have := eq_21_of_three_dvd h hn h3; omega
  refine reduce (by norm_num) (by norm_num) h hn h5 (odd_of_a_eq_self h hn) h3 ?_ ?_ ?_
  · intro k b q hq _ hq5 _ hb hE
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · have : k ≤ 1 := by omega
      interval_cases k <;> norm_num [H, sum_range_succ] at hE <;> omega
    · have := Nat.mul_le_mul_left (k + 1) (show 3 ≤ b + 2 by omega)
      obtain rfl : k = 0 := by omega
      have hd := (pow_dvd_pow q (by omega : 2 ≤ b + 1)).trans (pow_dvd_of_eq hE)
      norm_num [H_one] at hd
      have := Nat.le_of_dvd (by norm_num) hd
      nlinarith
  · intro k b c q r hq hr hqp hrp hqr hq5 hr5 hb hE
    have := Nat.mul_le_mul_left (k + 1) (Nat.mul_le_mul (show 2 ≤ b + 2 by omega)
      (show 2 ≤ c + 2 by omega))
    obtain rfl : k = 0 := by omega
    have := Nat.mul_le_mul_right (c + 2) (show 2 ≤ b + 2 by omega)
    have := Nat.mul_le_mul_left (b + 2) (show 2 ≤ c + 2 by omega)
    obtain rfl : b = 0 := by omega
    obtain rfl : c = 0 := by omega
    norm_num [H_one] at hE
    exact three_prime_eq_false (by norm_num) hq hr le_rfl hq5 hr5 (Ne.symm hqp) (Ne.symm hrp)
      hqr (by linarith [hE])
  · intro q r s _ _ _ _ _ _ h8
    omega

/-- Section 6, prime factor 7: the only solution divisible by 7 is `21`. -/
theorem eq_21_of_seven_dvd {n : ℕ} (h : a n = n) (hn : 0 < n) (h7 : 7 ∣ n) : n = 21 := by
  by_contra h21
  have h3 : ¬ 3 ∣ n := fun h3 => h21 (eq_21_of_three_dvd h hn h3)
  refine reduce (by norm_num) (by norm_num) h hn h7 (odd_of_a_eq_self h hn) h3 ?_ ?_ ?_
  · intro k b q hq _ hq5 hq3 hb hE
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · have : k ≤ 2 := by omega
      interval_cases k <;> norm_num [H, sum_range_succ] at hE <;> omega
    · have := Nat.mul_le_mul_left (k + 1) (show 3 ≤ b + 2 by omega)
      have : k ≤ 1 := by omega
      have hd := (pow_dvd_pow q (by omega : 2 ≤ b + 1)).trans (pow_dvd_of_eq hE)
      interval_cases k
      · norm_num [H_one] at hd
        have := Nat.le_of_dvd (by norm_num) hd
        nlinarith
      · norm_num [H, sum_range_succ] at hd
        have := Nat.le_of_dvd (by norm_num) hd
        have : q ≤ 12 := by nlinarith
        interval_cases q <;> omega
  · intro k b c q r hq hr hqp hrp hqr hq5 hr5 hb hE
    have hqo := hq.odd_of_ne_two (by omega)
    have hro := hr.odd_of_ne_two (by omega)
    have := Nat.mul_le_mul_left (k + 1) (Nat.mul_le_mul (show 2 ≤ b + 2 by omega)
      (show 2 ≤ c + 2 by omega))
    obtain rfl : k = 0 := by omega
    have := Nat.mul_le_mul_right (c + 2) (show 2 ≤ b + 2 by omega)
    have := Nat.mul_le_mul_left (b + 2) (show 2 ≤ c + 2 by omega)
    have hb1 : b ≤ 1 := by omega
    have hc1 : c ≤ 1 := by omega
    interval_cases b <;> interval_cases c
    · norm_num [H_one] at hE
      exact three_prime_eq_false (by norm_num) hq hr (by norm_num) hq5 hr5 (Ne.symm hqp)
        (Ne.symm hrp) hqr (by linarith [hE])
    · have h2 := congrArg (Nat.cast : ℕ → ZMod 2) hE
      push_cast [cast_H_two hqo, cast_H_two hro, cast_H_two (by decide : Odd 7),
        hqo.natCast_zmod_two, hro.natCast_zmod_two] at h2
      revert h2
      decide
    · have h2 := congrArg (Nat.cast : ℕ → ZMod 2) hE
      push_cast [cast_H_two hqo, cast_H_two hro, cast_H_two (by decide : Odd 7),
        hqo.natCast_zmod_two, hro.natCast_zmod_two] at h2
      revert h2
      decide
    · omega
  · intro q r s _ _ _ _ _ _ h8
    omega

/-- Section 6, prime factor 11: no solution is divisible by 11. -/
theorem not_eleven_dvd {n : ℕ} (h : a n = n) (hn : 0 < n) : ¬ 11 ∣ n := by
  intro h11
  have h3 : ¬ 3 ∣ n := fun h3 => by have := eq_21_of_three_dvd h hn h3; omega
  refine reduce (by norm_num) le_rfl h hn h11 (odd_of_a_eq_self h hn) h3 ?_ ?_ ?_
  · intro k b q hq _ hq5 hq3 hb hE
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · have : k ≤ 4 := by omega
      interval_cases k <;> norm_num [H, sum_range_succ] at hE <;> omega
    · have := Nat.mul_le_mul_left (k + 1) (show 3 ≤ b + 2 by omega)
      have : k ≤ 2 := by omega
      have hd := (pow_dvd_pow q (by omega : 2 ≤ b + 1)).trans (pow_dvd_of_eq hE)
      interval_cases k
      · norm_num [H_one] at hd
        have := Nat.le_of_dvd (by norm_num) hd
        nlinarith
      · norm_num [H, sum_range_succ] at hd
        have := Nat.le_of_dvd (by norm_num) hd
        have : q ≤ 19 := by nlinarith
        interval_cases q <;> omega
      · norm_num [H, sum_range_succ] at hd
        have := Nat.le_of_dvd (by norm_num) hd
        have : q ≤ 75 := by nlinarith
        interval_cases q <;> omega
  · intro k b c q r hq hr hqp hrp hqr hq5 hr5 hb hE
    have hqo := hq.odd_of_ne_two (by omega)
    have hro := hr.odd_of_ne_two (by omega)
    have := Nat.mul_le_mul_left (k + 1) (Nat.mul_le_mul (show 2 ≤ b + 2 by omega)
      (show 2 ≤ c + 2 by omega))
    have := Nat.le_mul_of_pos_left ((b + 2) * (c + 2)) (by omega : 0 < k + 1)
    have := Nat.mul_le_mul_right (c + 2) (show 2 ≤ b + 2 by omega)
    have := Nat.mul_le_mul_left (b + 2) (show 2 ≤ c + 2 by omega)
    have hk : k ≤ 1 := by omega
    have hb3 : b ≤ 3 := by omega
    have hc3 : c ≤ 3 := by omega
    interval_cases k <;> interval_cases b <;> interval_cases c
    all_goals first
      | omega
      | exact three_prime_eq_false (by norm_num) hq hr (by norm_num) hq5 hr5 (Ne.symm hqp)
          (Ne.symm hrp) hqr (by norm_num [H_one] at hE; linarith)
      | exact eleven_q_r4 (q := q) hr (by norm_num [H_one] at hE; linarith)
      | exact eleven_q_r4 (q := r) hq (by norm_num [H_one] at hE; linarith)
      | have h2 := congrArg (Nat.cast : ℕ → ZMod 2) hE
        push_cast [cast_H_two hqo, cast_H_two hro, cast_H_two (by decide : Odd 11),
          hqo.natCast_zmod_two, hro.natCast_zmod_two] at h2
        revert h2
        decide
  · intro q r s _ _ _ hq3 hr3 hs3 _ hE
    simp only [H_one] at hE
    exact eleven_qrs hq3 hr3 hs3 (by linarith)

/-- `(A245-12)`: every solution other than `21` is coprime to `2310 = 2 * 3 * 5 * 7 * 11`. -/
theorem coprime_2310 {n : ℕ} (h : a n = n) (hn : 0 < n) (h21 : n ≠ 21) : n.Coprime 2310 := by
  have hp : ∀ {p}, p.Prime → ¬ p ∣ n → n.Coprime p := fun hp hpn =>
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn).symm
  have h2 : ¬ 2 ∣ n := fun h2 => by have := Nat.odd_iff.1 (odd_of_a_eq_self h hn); omega
  have h3 : ¬ 3 ∣ n := fun h3 => h21 (eq_21_of_three_dvd h hn h3)
  have h7 : ¬ 7 ∣ n := fun h7 => h21 (eq_21_of_seven_dvd h hn h7)
  exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.mul_right
    (Nat.Coprime.mul_right (hp Nat.prime_two h2) (hp Nat.prime_three h3))
    (hp (by norm_num) (not_five_dvd h hn))) (hp (by norm_num) h7))
    (hp (by norm_num) (not_eleven_dvd h hn))

/-- Section 6, conclusion: the least prime factor of a solution other than `21` is at least `13`. -/
theorem thirteen_le_minFac {n : ℕ} (h : a n = n) (hn : 0 < n) (h21 : n ≠ 21) : 13 ≤ n.minFac := by
  have hn1 : n ≠ 1 := by rintro rfl; exact absurd h (by decide)
  have hp := Nat.minFac_prime hn1
  refine Nat.le_of_not_lt fun hlt => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left (Nat.minFac_dvd n) (coprime_2310 h hn h21)) ?_)
  interval_cases n.minFac <;> first | exact absurd hp (by decide) | decide

theorem card_divisors_mul_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    #(p * q).divisors = 4 := by
  rw [Nat.Coprime.card_divisors_mul ((Nat.coprime_primes hp hq).2 hpq), card_divisors_prime hp,
    card_divisors_prime hq]

/-- `(A245-2)` for `n = pqr`: `τ(qr) = 4 < p`. -/
theorem five_le_of_mul_mul {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (h : a (p * (q * r)) = p * (q * r)) : 5 ≤ p := by
  have hpqr : ¬ p ∣ q * r := fun hd => (hp.dvd_mul.1 hd).elim
    (fun hd => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 hd))
    (fun hd => hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 hd))
  have := lower_bound (k := 0) (by rwa [zero_add, pow_one]) hp hpqr
  rw [card_divisors_mul_prime hq hr hqr] at this
  omega

/-- Section 5, `r = 3`: no product of three distinct primes is a solution. -/
theorem a_mul_mul_ne {x y z : ℕ} (hx : x.Prime) (hy : y.Prime) (hz : z.Prime) (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) : a (x * y * z) ≠ x * y * z := by
  intro h
  rw [mul_assoc] at h
  have hx5 := five_le_of_mul_mul hx hy hz hxy hxz hyz h
  have hy5 := five_le_of_mul_mul hy hx hz (Ne.symm hxy) hyz hxz
    (by rw [show y * (x * z) = x * (y * z) by ring]; exact h)
  have hz5 := five_le_of_mul_mul hz hx hy (Ne.symm hxz) (Ne.symm hyz) hxy
    (by rw [show z * (x * y) = x * (y * z) by ring]; exact h)
  have cxy := (Nat.coprime_primes hx hy).2 hxy
  have cxz := (Nat.coprime_primes hx hz).2 hxz
  rw [a_eq_self_iff, W_mul (cxy.mul_right cxz), W_mul ((Nat.coprime_primes hy hz).2 hyz),
    W_prime hx, W_prime hy, W_prime hz, Nat.Coprime.card_divisors_mul (cxy.mul_right cxz),
    card_divisors_mul_prime hy hz hyz, card_divisors_prime hx] at h
  exact three_prime_eq_false hx hy hz hx5 hy5 hz5 hxy hxz hyz (by linarith)

/-- `(A245-9)`, left side: for squarefree `n`, `W n = ∏ (2p + 1)` over its prime factors. -/
theorem W_squarefree {n : ℕ} (hn : Squarefree n) : W n = ∏ p ∈ n.primeFactors, (1 + 2 * p) := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hn]
  rw [W_eq, isMultiplicative_W.map_prod_of_prime _ fun p hp => Nat.prime_of_mem_primeFactors hp]
  exact prod_congr rfl fun p hp => by rw [← W_eq, W_prime (Nat.prime_of_mem_primeFactors hp)]

/-- `(A245-9)`, right side: a squarefree `n` with `r` prime factors has `τ(n) = 2^r`. -/
theorem card_divisors_squarefree {n : ℕ} (hn : Squarefree n) :
    #n.divisors = 2 ^ #n.primeFactors := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hn]
  rw [← ArithmeticFunction.sigma_zero_apply,
    ArithmeticFunction.isMultiplicative_sigma.map_prod_of_prime _
      fun p hp => Nat.prime_of_mem_primeFactors hp]
  exact prod_eq_pow_card fun p hp => by
    rw [ArithmeticFunction.sigma_zero_apply, card_divisors_prime (Nat.prime_of_mem_primeFactors hp)]

/-- Section 5, even `r ≥ 4`: the mod-3 argument. -/
theorem squarefree_even {n : ℕ} (h : a n = n) (hn : Squarefree n) (hr : Even #n.primeFactors)
    (hr4 : 4 ≤ #n.primeFactors) : False := by
  have h3 : ¬ 3 ∣ n := fun h3 => by
    have h21 := eq_21_of_three_dvd h (Nat.pos_of_ne_zero hn.ne_zero) h3
    rw [h21, show (21 : ℕ) = 3 * 7 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.prime_three.primeFactors, (by norm_num : (7 : ℕ).Prime).primeFactors] at hr4
    exact absurd hr4 (by decide)
  have hn3 : (n : ZMod 3) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hp0 : ∀ p ∈ n.primeFactors, (p : ZMod 3) ≠ 0 := fun p hp hp0 =>
    h3 (((ZMod.natCast_eq_zero_iff p 3).1 hp0).trans (Nat.dvd_of_mem_primeFactors hp))
  obtain ⟨m, hm⟩ := hr
  have h2r : (2 : ZMod 3) ^ #n.primeFactors = 1 := by
    rw [hm, ← two_mul, pow_mul, show (2 : ZMod 3) ^ 2 = 1 by decide, one_pow]
  rw [a_eq_self_iff, W_squarefree hn, card_divisors_squarefree hn] at h
  have h3' := congrArg (Nat.cast : ℕ → ZMod 3) h
  push_cast at h3'
  rw [h2r] at h3'
  by_cases hex : ∃ p ∈ n.primeFactors, (p : ZMod 3) = 1
  · obtain ⟨p, hp, hp1⟩ := hex
    rw [prod_eq_zero hp (by rw [hp1]; decide)] at h3'
    exact mul_ne_zero hn3 (by decide) h3'.symm
  · push Not at hex
    have hval : ∀ x : ZMod 3, x ≠ 0 → x ≠ 1 → x = 2 := by decide
    have h2 : ∀ p ∈ n.primeFactors, (p : ZMod 3) = 2 := fun p hp => hval _ (hp0 p hp) (hex p hp)
    have hcast : (n : ZMod 3) = ∏ p ∈ n.primeFactors, (p : ZMod 3) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]
    rw [prod_eq_pow_card (b := 2) fun p hp => by rw [h2 p hp]; decide, hcast,
      prod_eq_pow_card h2, h2r] at h3'
    exact absurd h3' (by decide)

/-- Section 5 in summary: a squarefree solution other than `21` has an odd number `≥ 5` of
distinct prime factors. -/
theorem squarefree_card {n : ℕ} (h : a n = n) (hn : Squarefree n) (h21 : n ≠ 21) :
    Odd #n.primeFactors ∧ 5 ≤ #n.primeFactors := by
  have hprod := Nat.prod_primeFactors_of_squarefree hn
  have hpr : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  rcases Nat.even_or_odd #n.primeFactors with he | ho
  · exfalso
    obtain h0 | h2 | h4 : #n.primeFactors = 0 ∨ #n.primeFactors = 2 ∨ 4 ≤ #n.primeFactors := by
      obtain ⟨m, hm⟩ := he; omega
    · rw [Finset.card_eq_zero, Nat.primeFactors_eq_empty] at h0
      rcases h0 with h0 | rfl
      · exact hn.ne_zero h0
      · exact absurd h (by decide)
    · obtain ⟨p, q, hpq, hs⟩ := card_eq_two.1 h2
      rw [hs, prod_pair hpq] at hprod
      subst hprod
      exact h21 ((a_mul_eq_self_iff (hpr p (by simp [hs])) (hpr q (by simp [hs])) hpq).1 h)
    · exact squarefree_even h hn he h4
  · refine ⟨ho, ?_⟩
    obtain h1 | h3 | h5 : #n.primeFactors = 1 ∨ #n.primeFactors = 3 ∨ 5 ≤ #n.primeFactors := by
      obtain ⟨m, hm⟩ := ho; omega
    · obtain ⟨p, hs⟩ := card_eq_one.1 h1
      rw [hs, prod_singleton] at hprod
      subst hprod
      exact absurd (by simpa using h) (a_prime_pow_ne (hpr p (by simp [hs])) 1)
    · obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ := card_eq_three.1 h3
      rw [hs, prod_insert (by simp [hxy, hxz]), prod_pair hyz] at hprod
      subst hprod
      exact absurd (by rwa [← mul_assoc] at h) (a_mul_mul_ne (hpr x (by simp [hs]))
        (hpr y (by simp [hs])) (hpr z (by simp [hs])) hxy hxz hyz)
    · exact h5

end AgenticConjectures.OeisA245211
