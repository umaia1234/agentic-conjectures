import Mathlib

/-!
# OEIS A007406: the Eldar–Ordowski gcd conjecture (partial results)

`a n` is the numerator of `H2 n = ∑_{k=1}^n 1/k^2` (OEIS A007406, Wolstenholme numbers).
Amiram Eldar and Thomas Ordowski conjectured (OEIS A007406, Jul 28 2019) that
`gcd(n, a(n-1)) = A089026(n)` for every `n > 3`, i.e. `n` when `n` is prime and `1` otherwise.

## Upstream correspondence

* `a` is `OeisA7406.a` of google-deepmind/formal-conjectures, copied term for term.
* `a089026` is `OeisA89026.a`, copied term for term and renamed so that both definitions can
  live in one namespace.
* `statement` is the proposition of `OeisA7406.conjecture` with the binders `(n) (hn : 3 < n)`
  turned into `∀ n : ℕ, 3 < n → …`. With `3 < n` the natural-number subtraction `n - 1` is
  ordinary subtraction. As upstream, `a 0 = 0` (empty sum) and `a089026 0 = 1`; neither value
  enters `statement`.
* Upstream proves its test values with `decide +native`; here `a_zero` … `a_five` are proved
  by exact rational arithmetic instead.

## Results (all unconditional unless a hypothesis says otherwise)

* `prime_dvd_a_pred`, `statement_at_prime`: the prime half (classical, Wolstenholme type).
* `two_not_dvd_a`, `three_not_dvd_a`, `padicValRat_five_H2_le_two`: the `2`-, `3`- and
  `5`-parts; `statement_at_of_five_smooth`: the conjecture for every `5`-smooth `n > 3`
  (including `statement_at_two_pow`).
* `dvd_a_iff`: for primes `q ≥ 5` and `t ≥ 2`, `q ∣ a (q t - 1) ↔ 3 ≤ v_q(H2 (t - 1))`.
* `statement_iff`: the conjecture is equivalent to `v_q(H2 m) ≤ 2` for all primes `q ≥ 5`
  and all `m ≥ 1`.
* `padicValRat_H2_le_two_of_tree`: the interface used by the Boyd-tree certificate in
  `problems/oeis-a007406/`, and `statement_le_of_padicValRat_le_two`: bounds for all primes
  `5 ≤ q ≤ Q` give the conjecture for all `3 < n ≤ 2 Q + 1`.
* Families: `statement_at_two_mul` … `statement_at_six_mul` (`n = t q`, `2 ≤ t ≤ 6`, every
  prime `q`); `statement_at_mul` (`n = q t`, `t` `5`-smooth, `q^3 ∤ a (t - 1)`);
  `statement_at_sq` (`n = q^2`, `q^3 ∤ a (q - 1)`); `statement_at_prime_pow`
  (`n = q^k`, `k ≥ 2`, `q^2 ∤ a (q - 1)`).

The conjecture itself (`statement`) is not proved here.
-/

namespace AgenticConjectures.OeisA007406

open Finset

/-- OEIS A007406 (Wolstenholme numbers): the numerator of `∑_{k=1}^n 1/k^2`.
Term for term the upstream `OeisA7406.a`. -/
def a (n : ℕ) : ℕ :=
  (∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ) ^ 2).num.natAbs

/-- OEIS A089026: `n` if `n` is prime, otherwise `1`.
Term for term the upstream `OeisA89026.a`, renamed. -/
def a089026 (n : ℕ) : ℕ :=
  if n.Prime then n else 1

/-- The Eldar–Ordowski conjecture (upstream `OeisA7406.conjecture`): for `n > 3`,
`gcd(n, a(n-1)) = A089026(n)`. Open; not proved here. -/
def statement : Prop :=
  ∀ n : ℕ, 3 < n → Nat.gcd n (a (n - 1)) = a089026 n

/-- `H2 m = ∑_{k=1}^m 1/k^2`; `a m` is the absolute value of its numerator. -/
def H2 (m : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 m, (1 : ℚ) / (k : ℚ) ^ 2

/-- `a m` is the absolute value of the numerator of `H2 m`. -/
theorem a_eq_natAbs_num (m : ℕ) : a m = (H2 m).num.natAbs := rfl

/-- The empty sum. -/
theorem H2_zero : H2 0 = 0 := by simp [H2]

/-- One more term of `H2`. -/
theorem H2_succ (m : ℕ) : H2 (m + 1) = H2 m + 1 / ((m + 1 : ℕ) : ℚ) ^ 2 := by
  rw [H2, Finset.sum_Icc_succ_top (by omega), H2]

/-- `H2 m > 0` for `m ≥ 1`. -/
theorem H2_pos {m : ℕ} (hm : 1 ≤ m) : 0 < H2 m := by
  apply Finset.sum_pos
  · intro k hk
    have hk0 : (0 : ℚ) < k := Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hk).1; omega)
    positivity
  · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hm⟩⟩

/-- `U q m`: the terms of `H2 m` with `q ∤ k` (`q`-integral when `q` is prime). -/
def U (q m : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 m, if q ∣ k then 0 else (1 : ℚ) / (k : ℚ) ^ 2

/-- One more term of `U q`. -/
theorem U_succ (q m : ℕ) :
    U q (m + 1) = U q m + if q ∣ m + 1 then 0 else 1 / ((m + 1 : ℕ) : ℚ) ^ 2 := by
  rw [U, Finset.sum_Icc_succ_top (by omega), U]

/-- Splitting off the multiples of `q`: `H2 m = U q m + H2 (m / q) / q ^ 2`. -/
theorem H2_eq_U_add {q : ℕ} (hq : 0 < q) (m : ℕ) :
    H2 m = U q m + H2 (m / q) / (q : ℚ) ^ 2 := by
  induction m with
  | zero => simp [H2, U]
  | succ m ih =>
    rw [H2_succ, U_succ, Nat.succ_div, ih]
    by_cases h : q ∣ m + 1
    · obtain ⟨c, hc⟩ := h
      have hc' : m / q + 1 = c := by
        have h1 := Nat.succ_div (a := m) (b := q)
        rw [if_pos ⟨c, hc⟩, hc, Nat.mul_div_cancel_left c hq] at h1
        omega
      rw [if_pos ⟨c, hc⟩, if_pos ⟨c, hc⟩, H2_succ, hc', hc]
      have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
      have hc0 : (c : ℚ) ≠ 0 := by
        have : c ≠ 0 := by
          rintro rfl
          simp at hc
        exact_mod_cast this
      push_cast
      field_simp
      ring
    · rw [if_neg h, if_neg h]
      simp only [add_zero]
      ring

/-- Helper: `1 / k ^ 2` as the inverse of a natural number. -/
theorem one_div_sq_eq (k : ℕ) : (1 : ℚ) / (k : ℚ) ^ 2 = ((k ^ 2 : ℕ) : ℚ)⁻¹ := by
  push_cast
  rw [one_div]

/-- A finite sum of `q`-integral rationals is `q`-integral (`q` prime). -/
theorem not_dvd_den_sum {q : ℕ} (hq : q.Prime) (s : Finset ℕ) (f : ℕ → ℚ)
    (h : ∀ k ∈ s, ¬ q ∣ (f k).den) : ¬ q ∣ (∑ k ∈ s, f k).den := by
  induction s using Finset.induction_on with
  | empty => simpa using hq.ne_one
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    intro hdvd
    have h1 := h b (Finset.mem_insert_self b s)
    have h2 := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    rcases (Nat.Prime.dvd_mul hq).mp (hdvd.trans (Rat.add_den_dvd _ _)) with h' | h'
    · exact h1 h'
    · exact h2 h'

/-- `U q m` is `q`-integral for prime `q`. -/
theorem not_dvd_den_U {q : ℕ} (hq : q.Prime) (m : ℕ) : ¬ q ∣ (U q m).den := by
  apply not_dvd_den_sum hq
  intro k hk
  by_cases h : q ∣ k
  · rw [if_pos h]
    simpa using hq.ne_one
  · have hk1 : 0 < k ^ 2 := pow_pos (by have := (Finset.mem_Icc.mp hk).1; omega) 2
    rw [if_neg h, one_div_sq_eq, Rat.inv_natCast_den_of_pos hk1]
    exact fun h' => h (hq.dvd_of_dvd_pow h')

/-- A `q`-integral rational has nonnegative `q`-adic valuation. -/
theorem padicValRat_nonneg_of_not_dvd_den {q : ℕ} {x : ℚ} (h : ¬ q ∣ x.den) :
    0 ≤ padicValRat q x := by
  unfold padicValRat
  rw [padicValNat.eq_zero_of_not_dvd h]
  simp

/-- `q` divides the numerator of `x ≠ 0` iff `v_q(x) > 0`. -/
theorem dvd_natAbs_num_iff {q : ℕ} [hq : Fact q.Prime] {x : ℚ} (hx : x ≠ 0) :
    q ∣ x.num.natAbs ↔ 0 < padicValRat q x := by
  have hnum : x.num.natAbs ≠ 0 := by simpa using hx
  unfold padicValRat padicValInt
  constructor
  · intro h
    have hden : ¬ q ∣ x.den := fun h' =>
      hq.out.ne_one ((Nat.Coprime.coprime_dvd_left h x.reduced).eq_one_of_dvd h')
    rw [padicValNat.eq_zero_of_not_dvd hden]
    have := one_le_padicValNat_of_dvd hnum h
    omega
  · intro h
    by_contra hnd
    rw [padicValNat.eq_zero_of_not_dvd hnd] at h
    omega

/-- If `q ^ (e + 1)` does not divide the numerator of `x`, then `v_q(x) ≤ e`. -/
theorem padicValRat_le_of_not_pow_dvd {q : ℕ} {x : ℚ} {e : ℕ}
    (h : ¬ q ^ (e + 1) ∣ x.num.natAbs) : padicValRat q x ≤ e := by
  unfold padicValRat padicValInt
  have : padicValNat q x.num.natAbs ≤ e := by
    by_contra hlt
    exact h ((pow_dvd_pow q (by omega)).trans pow_padicValNat_dvd)
  omega

/-- Pruning lemma: if `s ≥ 1`, `r < q` and `v_q(H2 s) ≤ 1`, then
`v_q(H2 (q * s + r)) = v_q(H2 s) - 2`. -/
theorem padicValRat_H2_mul_add {q : ℕ} [hq : Fact q.Prime] {s r : ℕ} (hs : 1 ≤ s)
    (hr : r < q) (hv : padicValRat q (H2 s) ≤ 1) :
    padicValRat q (H2 (q * s + r)) = padicValRat q (H2 s) - 2 := by
  have hq0 : 0 < q := hq.out.pos
  have hdiv : (q * s + r) / q = s := by
    rw [Nat.mul_add_div hq0, Nat.div_eq_of_lt hr, add_zero]
  have hdec := H2_eq_U_add hq0 (q * s + r)
  rw [hdiv] at hdec
  have hH2s : H2 s ≠ 0 := (H2_pos hs).ne'
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hX : padicValRat q (H2 s / (q : ℚ) ^ 2) = padicValRat q (H2 s) - 2 := by
    rw [padicValRat.div hH2s (pow_ne_zero 2 hqQ), padicValRat.pow hqQ,
      padicValRat.self hq.out.one_lt]
    ring
  have hU := padicValRat_nonneg_of_not_dvd_den (not_dvd_den_U hq.out (q * s + r))
  have hpos : 0 < H2 (q * s + r) := H2_pos (by nlinarith)
  rw [hdec]
  by_cases hU0 : U q (q * s + r) = 0
  · rw [hU0, zero_add, hX]
  · rw [add_comm, padicValRat.add_eq_of_lt ?_ (div_ne_zero hH2s (pow_ne_zero 2 hqQ)) hU0 ?_, hX]
    · rw [add_comm, ← hdec]
      exact hpos.ne'
    · rw [hX]
      omega

/-- If `v_q(H2 m) ≤ 0` for `1 ≤ m < q`, then `v_q(H2 m) ≤ 0` for all `m ≥ 1`. -/
theorem padicValRat_H2_nonpos_of_roots {q : ℕ} [hq : Fact q.Prime]
    (hroots : ∀ m, 1 ≤ m → m < q → padicValRat q (H2 m) ≤ 0) :
    ∀ m, 1 ≤ m → padicValRat q (H2 m) ≤ 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases hmq : m < q
    · exact hroots m hm hmq
    · have hq0 : 0 < q := hq.out.pos
      have hs : 1 ≤ m / q := (Nat.one_le_div_iff hq0).mpr (by omega)
      have hlt : m / q < m := Nat.div_lt_self (by omega) hq.out.one_lt
      have hih := ih (m / q) hlt hs
      have h := padicValRat_H2_mul_add (q := q) hs (Nat.mod_lt m hq0) (by omega)
      rw [Nat.div_add_mod m q] at h
      omega

/-- `v_q(H2 m) ≤ 0` means `q ∤ a m`. -/
theorem not_dvd_a_of_nonpos {q m : ℕ} [Fact q.Prime] (hm : 1 ≤ m)
    (hv : padicValRat q (H2 m) ≤ 0) : ¬ q ∣ a m := by
  rw [a_eq_natAbs_num, dvd_natAbs_num_iff (H2_pos hm).ne']
  omega

/-- `H2 1 = 1`. -/
theorem H2_one : H2 1 = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, H2_succ, H2_zero]
  norm_num

/-- `H2 2 = 5/4`. -/
theorem H2_two : H2 2 = 5 / 4 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, H2_succ, H2_one]
  norm_num

/-- `H2 3 = 49/36`. -/
theorem H2_three : H2 3 = 49 / 36 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, H2_succ, H2_two]
  norm_num

/-- `H2 4 = 205/144`. -/
theorem H2_four : H2 4 = 205 / 144 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, H2_succ, H2_three]
  norm_num

/-- The `2`-part: `a m` is odd for every `m ≥ 1`. -/
theorem two_not_dvd_a {m : ℕ} (hm : 1 ≤ m) : ¬ 2 ∣ a m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply not_dvd_a_of_nonpos hm
  apply padicValRat_H2_nonpos_of_roots _ m hm
  intro k hk1 hk2
  obtain rfl : k = 1 := by omega
  rw [H2_one, padicValRat.one]

/-- The `3`-part: `3 ∤ a m` for every `m ≥ 1`. -/
theorem three_not_dvd_a {m : ℕ} (hm : 1 ≤ m) : ¬ 3 ∣ a m := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply not_dvd_a_of_nonpos hm
  apply padicValRat_H2_nonpos_of_roots _ m hm
  intro k hk1 hk2
  interval_cases k
  · rw [H2_one, padicValRat.one]
  · rw [H2_two, show (5 / 4 : ℚ) = ((5 : ℕ) : ℚ) / ((4 : ℕ) : ℚ) by norm_num,
      padicValRat.div (by norm_num) (by norm_num), padicValRat.of_nat, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 5),
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 4)]
    simp

section ZModPart

variable {q : ℕ} [hq : Fact q.Prime]

/-- Casting a sum of `q`-integral rationals to `ZMod q`. -/
theorem cast_sum_zmod (s : Finset ℕ) (f : ℕ → ℚ) (h : ∀ k ∈ s, ¬ q ∣ (f k).den) :
    ((∑ k ∈ s, f k : ℚ) : ZMod q) = ∑ k ∈ s, ((f k : ℚ) : ZMod q) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    have h1 : ((f b).den : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact h b (Finset.mem_insert_self b s)
    have h2 : ((∑ k ∈ s, f k).den : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact not_dvd_den_sum hq.out s f (fun k hk => h k (Finset.mem_insert_of_mem hk))
    rw [Rat.cast_add_of_ne_zero h1 h2, ih (fun k hk => h k (Finset.mem_insert_of_mem hk))]

/-- `U q m` in `ZMod q` is `∑_{k=1}^m (k ^ 2)⁻¹`. -/
theorem cast_U (m : ℕ) : ((U q m : ℚ) : ZMod q) = ∑ k ∈ Icc 1 m, ((k : ZMod q) ^ 2)⁻¹ := by
  rw [U, cast_sum_zmod]
  · apply Finset.sum_congr rfl
    intro k _
    by_cases h : q ∣ k
    · rw [if_pos h, Rat.cast_zero, (ZMod.natCast_eq_zero_iff k q).mpr h]
      simp
    · rw [if_neg h, one_div_sq_eq, Rat.cast_inv_nat]
      push_cast
      rfl
  · intro k hk
    by_cases h : q ∣ k
    · rw [if_pos h]
      simpa using hq.out.ne_one
    · have hk1 : 0 < k ^ 2 := pow_pos (by have := (Finset.mem_Icc.mp hk).1; omega) 2
      rw [if_neg h, one_div_sq_eq, Rat.inv_natCast_den_of_pos hk1]
      exact fun h' => h (hq.out.dvd_of_dvd_pow h')

/-- `∑_{x ∈ ZMod q} (x ^ 2)⁻¹ = 0` for primes `q ≥ 5`. -/
theorem sum_inv_sq_zmod (h5 : 5 ≤ q) : ∑ x : ZMod q, (x ^ 2)⁻¹ = 0 := by
  have h : ∑ x : ZMod q, (x ^ 2)⁻¹ = ∑ x : ZMod q, x ^ 2 := by
    simp_rw [← inv_pow]
    exact Equiv.sum_comp (Equiv.inv (ZMod q)) (fun x => x ^ 2)
  rw [h]
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [ZMod.card]
  omega

/-- A sum over `range q` as a sum over `ZMod q`. -/
theorem sum_range_eq_sum_zmod (g : ZMod q → ZMod q) :
    ∑ k ∈ range q, g (k : ZMod q) = ∑ x : ZMod q, g x := by
  apply Finset.sum_nbij' (fun k : ℕ => (k : ZMod q)) (fun x : ZMod q => x.val)
  · intro k _
    exact Finset.mem_univ _
  · intro x _
    exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro k hk
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp hk)
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro k _
    rfl

/-- Periodicity of a sum over `range (q * t)` of a function of `k mod q`. -/
theorem sum_range_mul (g : ZMod q → ZMod q) (t : ℕ) :
    ∑ k ∈ range (q * t), g (k : ZMod q) = t * ∑ k ∈ range q, g (k : ZMod q) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have hx : ∀ x : ℕ, ((q * t + x : ℕ) : ZMod q) = (x : ZMod q) := by
      intro x
      push_cast
      rw [ZMod.natCast_self]
      ring
    simp_rw [hx]
    push_cast
    ring

/-- Adding the (zero) `k = 0` term to the sum. -/
theorem sum_Icc_inv_sq_eq_sum_range (n : ℕ) :
    ∑ k ∈ Icc 1 n, ((k : ZMod q) ^ 2)⁻¹ = ∑ k ∈ range (n + 1), ((k : ZMod q) ^ 2)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ _ (n + 1)]

/-- Block vanishing: `U q (q * t) ≡ 0 (mod q)` for primes `q ≥ 5`. -/
theorem cast_U_mul (h5 : 5 ≤ q) (t : ℕ) : ((U q (q * t) : ℚ) : ZMod q) = 0 := by
  rw [cast_U, sum_Icc_inv_sq_eq_sum_range, Finset.sum_range_succ,
    sum_range_mul (fun x => (x ^ 2)⁻¹) t, sum_range_eq_sum_zmod (fun x => (x ^ 2)⁻¹),
    sum_inv_sq_zmod h5]
  have h0 : ((q * t : ℕ) : ZMod q) = 0 := by
    push_cast
    rw [ZMod.natCast_self, zero_mul]
  rw [h0]
  simp

/-- A `q`-integral rational that is `0` in `ZMod q` has numerator divisible by `q`. -/
theorem dvd_num_of_cast_eq_zero {x : ℚ} (hden : ¬ q ∣ x.den) (hx : (x : ZMod q) = 0) :
    q ∣ x.num.natAbs := by
  rw [Rat.cast_def] at hx
  have hd : (x.den : ZMod q) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hn : (x.num : ZMod q) = 0 := by
    rcases div_eq_zero_iff.mp hx with h | h
    · exact h
    · exact absurd h hd
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hn
  exact Int.natCast_dvd.mp hn

/-- `v_q(U q (q * t)) ≥ 1` for primes `q ≥ 5` (when nonzero). -/
theorem one_le_padicValRat_U_mul (h5 : 5 ≤ q) (t : ℕ) (h0 : U q (q * t) ≠ 0) :
    1 ≤ padicValRat q (U q (q * t)) := by
  have := (dvd_natAbs_num_iff h0).mp
    (dvd_num_of_cast_eq_zero (not_dvd_den_U hq.out _) (cast_U_mul h5 t))
  omega

end ZModPart

/-- `U q (q * t - 1) = U q (q * t)`. -/
theorem U_mul_sub_one (q t : ℕ) (ht : 1 ≤ q * t) : U q (q * t - 1) = U q (q * t) := by
  obtain ⟨m, hm⟩ : ∃ m, q * t = m + 1 := ⟨q * t - 1, by omega⟩
  have hdvd : q ∣ m + 1 := hm ▸ dvd_mul_right q t
  rw [hm, Nat.add_sub_cancel, U_succ, if_pos hdvd, add_zero]

/-- `H2 (q * t - 1) = U q (q * t) + H2 (t - 1) / q ^ 2`. -/
theorem H2_mul_sub_one {q t : ℕ} (hq : 0 < q) (ht : 1 ≤ t) :
    H2 (q * t - 1) = U q (q * t) + H2 (t - 1) / (q : ℚ) ^ 2 := by
  have hqt : 1 ≤ q * t := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hdiv : (q * t - 1) / q = t - 1 := by
    apply Nat.div_eq_of_lt_le
    · have : (t - 1) * q = q * t - q := by
        rw [Nat.sub_one_mul, mul_comm]
      omega
    · have : (t - 1 + 1) * q = q * t := by
        rw [Nat.sub_add_cancel ht, mul_comm]
      omega
  rw [H2_eq_U_add hq (q * t - 1), hdiv, U_mul_sub_one q t hqt]

/-- Wolstenholme-type congruence (classical): `p ∣ a (p - 1)` for every prime `p ≥ 5`. -/
theorem prime_dvd_a_pred {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : p ∣ a (p - 1) := by
  haveI := Fact.mk hp
  have h1 : H2 (p - 1) = U p (p * 1) := by
    rw [show p - 1 = p * 1 - 1 by rw [mul_one], H2_mul_sub_one hp.pos le_rfl]
    simp [H2_zero]
  rw [a_eq_natAbs_num, h1]
  exact dvd_num_of_cast_eq_zero (not_dvd_den_U hp _) (cast_U_mul h5 1)

/-- Exact reduction of the `q`-part: for a prime `q ≥ 5` and `t ≥ 2`,
`q ∣ a (q * t - 1) ↔ 3 ≤ v_q(H2 (t - 1))`. -/
theorem dvd_a_iff {q t : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (ht : 2 ≤ t) :
    q ∣ a (q * t - 1) ↔ 3 ≤ padicValRat q (H2 (t - 1)) := by
  haveI := Fact.mk hq
  have hdec := H2_mul_sub_one hq.pos (by omega : 1 ≤ t)
  have hpos : 0 < H2 (q * t - 1) := H2_pos (by
    have : 2 * 2 ≤ q * t := Nat.mul_le_mul (by omega) ht
    omega)
  have hH : H2 (t - 1) ≠ 0 := (H2_pos (by omega)).ne'
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hXne : H2 (t - 1) / (q : ℚ) ^ 2 ≠ 0 := div_ne_zero hH (pow_ne_zero 2 hqQ)
  have hX : padicValRat q (H2 (t - 1) / (q : ℚ) ^ 2) = padicValRat q (H2 (t - 1)) - 2 := by
    rw [padicValRat.div hH (pow_ne_zero 2 hqQ), padicValRat.pow hqQ,
      padicValRat.self hq.one_lt]
    ring
  rw [a_eq_natAbs_num, dvd_natAbs_num_iff hpos.ne', hdec]
  by_cases h0 : U q (q * t) = 0
  · rw [h0, zero_add, hX]
    omega
  · have h1 := one_le_padicValRat_U_mul h5 t h0
    have hsum : U q (q * t) + H2 (t - 1) / (q : ℚ) ^ 2 ≠ 0 := by
      rw [← hdec]
      exact hpos.ne'
    constructor
    · intro hv
      by_contra hlt
      rw [add_comm, padicValRat.add_eq_of_lt (by rwa [add_comm]) hXne h0 (by omega), hX] at hv
      omega
    · intro hv
      have hmin := padicValRat.min_le_padicValRat_add (p := q) hsum
      have : 1 ≤ min (padicValRat q (U q (q * t))) (padicValRat q (H2 (t - 1) / (q : ℚ) ^ 2)) :=
        le_min h1 (by omega)
      omega

/-- The numerator of a reduced fraction `m / d`. -/
theorem natAbs_num_div {m d : ℕ} (hd : 0 < d) (h : Nat.Coprime m d) :
    ((m : ℚ) / (d : ℚ)).num.natAbs = m := by
  have h' := Rat.num_div_eq_of_coprime (a := (m : ℤ)) (b := (d : ℤ)) (by exact_mod_cast hd)
    (by simpa using h)
  push_cast at h'
  rw [h']
  simp

/-- `a 0 = 0` (upstream test value). -/
theorem a_zero : a 0 = 0 := by
  rw [a_eq_natAbs_num, H2_zero]
  rfl

/-- `a 1 = 1` (upstream test value). -/
theorem a_one : a 1 = 1 := by
  rw [a_eq_natAbs_num, H2_one]
  rfl

/-- `a 2 = 5` (upstream test value). -/
theorem a_two : a 2 = 5 := by
  rw [a_eq_natAbs_num, H2_two, show (5 / 4 : ℚ) = ((5 : ℕ) : ℚ) / ((4 : ℕ) : ℚ) by norm_num,
    natAbs_num_div (by norm_num) (by norm_num)]

/-- `a 3 = 49` (upstream test value). -/
theorem a_three : a 3 = 49 := by
  rw [a_eq_natAbs_num, H2_three, show (49 / 36 : ℚ) = ((49 : ℕ) : ℚ) / ((36 : ℕ) : ℚ) by norm_num,
    natAbs_num_div (by norm_num) (by norm_num)]

/-- `a 4 = 205` (upstream test value). -/
theorem a_four : a 4 = 205 := by
  rw [a_eq_natAbs_num, H2_four,
    show (205 / 144 : ℚ) = ((205 : ℕ) : ℚ) / ((144 : ℕ) : ℚ) by norm_num,
    natAbs_num_div (by norm_num) (by norm_num)]

/-- `H2 5 = 5269/3600`. -/
theorem H2_five : H2 5 = 5269 / 3600 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, H2_succ, H2_four]
  norm_num

/-- `a 5 = 5269`. -/
theorem a_five : a 5 = 5269 := by
  rw [a_eq_natAbs_num, H2_five,
    show (5269 / 3600 : ℚ) = ((5269 : ℕ) : ℚ) / ((3600 : ℕ) : ℚ) by norm_num,
    natAbs_num_div (by norm_num) (by norm_num)]

/-- A prime other than `2` and `3` is at least `5`. -/
theorem five_le_of_prime {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) (h3 : q ≠ 3) : 5 ≤ q := by
  have := hq.two_le
  by_contra h
  obtain rfl : q = 4 := by omega
  exact absurd hq (by decide)

/-- The prime half of the conjecture (classical): `gcd(p, a(p - 1)) = p` for primes `p > 3`. -/
theorem statement_at_prime {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    Nat.gcd p (a (p - 1)) = a089026 p := by
  rw [a089026, if_pos hp]
  exact Nat.gcd_eq_left (prime_dvd_a_pred hp (five_le_of_prime hp (by omega) (by omega)))

/-- For composite `n`, the conjecture at `n` says that no prime factor of `n` divides
`a (n - 1)`. -/
theorem gcd_eq_a089026_iff {n : ℕ} (hn : ¬ n.Prime) :
    Nat.gcd n (a (n - 1)) = a089026 n ↔ ∀ q, q.Prime → q ∣ n → ¬ q ∣ a (n - 1) := by
  rw [a089026, if_neg hn]
  constructor
  · intro h q hq hqn hqa
    have := Nat.dvd_gcd hqn hqa
    rw [h] at this
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  · intro h
    exact Nat.coprime_of_dvd h

/-- The conjecture at `n > 3` follows from `v_q(H2 m) ≤ 2` for all `m ≥ 1` and all primes
`q ≥ 5` dividing `n`. -/
theorem statement_at_of_padicValRat_le_two {n : ℕ} (hn : 3 < n)
    (hv : ∀ q, q.Prime → q ∣ n → 5 ≤ q → ∀ m, 1 ≤ m → padicValRat q (H2 m) ≤ 2) :
    Nat.gcd n (a (n - 1)) = a089026 n := by
  by_cases hp : n.Prime
  · exact statement_at_prime hp hn
  · rw [gcd_eq_a089026_iff hp]
    intro q hq hqn hqa
    by_cases h2 : q = 2
    · subst h2
      exact two_not_dvd_a (by omega) hqa
    by_cases h3 : q = 3
    · subst h3
      exact three_not_dvd_a (by omega) hqa
    have h5 := five_le_of_prime hq h2 h3
    obtain ⟨t, rfl⟩ := hqn
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp at hn
    have ht1 : t ≠ 1 := by
      rintro rfl
      rw [mul_one] at hp
      exact hp hq
    have ht : 2 ≤ t := by omega
    have h1 := (dvd_a_iff hq h5 ht).mp hqa
    have h2' := hv q hq (dvd_mul_right q t) h5 (t - 1) (by omega)
    omega

/-- The conjecture is equivalent to `v_q(H2 m) ≤ 2` for all primes `q ≥ 5` and all `m ≥ 1`. -/
theorem statement_iff :
    statement ↔ ∀ q m : ℕ, q.Prime → 5 ≤ q → 1 ≤ m → padicValRat q (H2 m) ≤ 2 := by
  constructor
  · intro hs q m hq h5 hm
    by_contra hv
    have hdvd : q ∣ a (q * (m + 1) - 1) :=
      (dvd_a_iff hq h5 (by omega : 2 ≤ m + 1)).mpr (by rw [Nat.add_sub_cancel]; omega)
    have hn : 3 < q * (m + 1) := by
      have : 5 * 1 ≤ q * (m + 1) := Nat.mul_le_mul h5 (by omega)
      omega
    have hnp : ¬ (q * (m + 1)).Prime := Nat.not_prime_mul (by omega) (by omega)
    exact (gcd_eq_a089026_iff hnp).mp (hs _ hn) q hq (dvd_mul_right q _) hdvd
  · intro hv n hn
    exact statement_at_of_padicValRat_le_two hn (fun q hq _ h5 m hm => hv q m hq h5 hm)

/-- Certificate interface for the Boyd-tree search: a set `T` that contains `1, …, q - 1`,
is closed under `s ↦ q * s + r` (`r < q`) at its nodes with `v_q(H2 s) ≥ 2`, and satisfies
`v_q(H2 m) ≤ 2` on `T`, forces `v_q(H2 m) ≤ 2` for every `m ≥ 1`. -/
theorem padicValRat_H2_le_two_of_tree {q : ℕ} (hq : q.Prime) (T : Set ℕ)
    (hroots : ∀ m, 1 ≤ m → m < q → m ∈ T)
    (hclosed : ∀ s ∈ T, 2 ≤ padicValRat q (H2 s) → ∀ r, r < q → q * s + r ∈ T)
    (hT : ∀ m ∈ T, padicValRat q (H2 m) ≤ 2) :
    ∀ m, 1 ≤ m → padicValRat q (H2 m) ≤ 2 := by
  haveI := Fact.mk hq
  have key : ∀ m, 1 ≤ m → m ∈ T ∨ padicValRat q (H2 m) < 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      by_cases hmq : m < q
      · exact Or.inl (hroots m hm hmq)
      · have hq0 : 0 < q := hq.pos
        have hs : 1 ≤ m / q := (Nat.one_le_div_iff hq0).mpr (by omega)
        have hlt : m / q < m := Nat.div_lt_self (by omega) hq.one_lt
        have hdm := Nat.div_add_mod m q
        by_cases hv : padicValRat q (H2 (m / q)) ≤ 1
        · right
          have h := padicValRat_H2_mul_add (q := q) hs (Nat.mod_lt m hq0) hv
          rw [hdm] at h
          omega
        · left
          rcases ih (m / q) hlt hs with hT' | hneg
          · rw [← hdm]
            exact hclosed _ hT' (by omega) _ (Nat.mod_lt m hq0)
          · omega
  intro m hm
  rcases key m hm with h | h
  · exact hT m h
  · omega

/-- The `5`-part: `v_5(H2 m) ≤ 2` for every `m ≥ 1` (a tree certificate without expanded
nodes: `v_5(H2 m) ≤ 1` for the roots `m = 1, …, 4`). -/
theorem padicValRat_five_H2_le_two : ∀ m, 1 ≤ m → padicValRat 5 (H2 m) ≤ 2 := by
  have hroot : ∀ m, 1 ≤ m → m < 5 → padicValRat 5 (H2 m) ≤ 1 := by
    intro m h1 h2
    apply padicValRat_le_of_not_pow_dvd
    rw [← a_eq_natAbs_num]
    interval_cases m
    · rw [a_one]
      decide
    · rw [a_two]
      decide
    · rw [a_three]
      decide
    · rw [a_four]
      decide
  apply padicValRat_H2_le_two_of_tree Nat.prime_five {m | 1 ≤ m ∧ m < 5}
  · intro m h1 h2
    exact ⟨h1, h2⟩
  · rintro s ⟨h1, h2⟩ hv
    have := hroot s h1 h2
    exfalso
    omega
  · rintro m ⟨h1, h2⟩
    have := hroot m h1 h2
    omega

/-- `5 ∤ a (5 * t - 1)` for every `t ≥ 2`. -/
theorem five_not_dvd_a {t : ℕ} (ht : 2 ≤ t) : ¬ 5 ∣ a (5 * t - 1) := by
  intro h
  have h1 := (dvd_a_iff Nat.prime_five le_rfl ht).mp h
  have h2 := padicValRat_five_H2_le_two (t - 1) (by omega)
  omega

/-- If `v_q(H2 m) ≤ 2` for all `m ≥ 1` and all primes `5 ≤ q ≤ Q` (what the Boyd-tree
certificate checks, prime by prime), then the conjecture holds for every `3 < n ≤ 2 * Q + 1`. -/
theorem statement_le_of_padicValRat_le_two {Q : ℕ}
    (hv : ∀ q, q.Prime → 5 ≤ q → q ≤ Q → ∀ m, 1 ≤ m → padicValRat q (H2 m) ≤ 2) :
    ∀ n, 3 < n → n ≤ 2 * Q + 1 → Nat.gcd n (a (n - 1)) = a089026 n := by
  intro n hn hnQ
  by_cases hp : n.Prime
  · exact statement_at_prime hp hn
  apply statement_at_of_padicValRat_le_two hn
  intro q hq hqn h5
  apply hv q hq h5
  obtain ⟨t, rfl⟩ := hqn
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at hn
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [mul_one] at hp
    exact hp hq
  have : q * 2 ≤ q * t := Nat.mul_le_mul_left q (by omega)
  omega

/-- The conjecture for every `5`-smooth `n > 3`. -/
theorem statement_at_of_five_smooth {n : ℕ} (hn : 3 < n)
    (hs : ∀ q, q.Prime → q ∣ n → q ≤ 5) : Nat.gcd n (a (n - 1)) = a089026 n := by
  apply statement_at_of_padicValRat_le_two hn
  intro q hq hqn h5
  obtain rfl : q = 5 := le_antisymm (hs q hq hqn) h5
  exact padicValRat_five_H2_le_two

/-- The conjecture at `n = 2 ^ k`, `k ≥ 2`. -/
theorem statement_at_two_pow {k : ℕ} (hk : 2 ≤ k) :
    Nat.gcd (2 ^ k) (a (2 ^ k - 1)) = a089026 (2 ^ k) := by
  apply statement_at_of_five_smooth
  · calc 3 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  · intro q hq hqn
    have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hqn)
    omega

/-- The conjecture at `n = q * t` for a prime `q`, a `5`-smooth `t ≥ 2`, and
`q ^ 3 ∤ a (t - 1)` when `q ≥ 5`. -/
theorem statement_at_mul {q t : ℕ} (hq : q.Prime) (ht : 2 ≤ t)
    (hs : ∀ r, r.Prime → r ∣ t → r ≤ 5) (hc : 5 ≤ q → ¬ q ^ 3 ∣ a (t - 1)) :
    Nat.gcd (q * t) (a (q * t - 1)) = a089026 (q * t) := by
  have hn : 3 < q * t := by
    have : 2 * 2 ≤ q * t := Nat.mul_le_mul hq.two_le ht
    omega
  by_cases h5 : 5 ≤ q
  · have hnp : ¬ (q * t).Prime := Nat.not_prime_mul (by omega) (by omega)
    rw [gcd_eq_a089026_iff hnp]
    intro r hr hrn hra
    by_cases hrq : r = q
    · subst hrq
      have h1 := (dvd_a_iff hr h5 ht).mp hra
      have h2 := padicValRat_le_of_not_pow_dvd (q := r) (e := 2) (x := H2 (t - 1)) (hc h5)
      omega
    · have hrt : r ∣ t := ((Nat.Prime.dvd_mul hr).mp hrn).resolve_left
        (fun h => hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp h))
      have h3 := hs r hr hrt
      have h2 := hr.two_le
      interval_cases r
      · exact two_not_dvd_a (by omega) hra
      · exact three_not_dvd_a (by omega) hra
      · exact absurd hr (by decide)
      · obtain ⟨u, hu⟩ := hrn
        have h10 : 5 * 2 ≤ q * t := Nat.mul_le_mul h5 ht
        rw [hu] at hra
        exact five_not_dvd_a (by omega) hra
  · apply statement_at_of_five_smooth hn
    intro r hr hrn
    rcases (Nat.Prime.dvd_mul hr).mp hrn with h | h
    · have := Nat.le_of_dvd hq.pos h
      omega
    · exact hs r hr h

/-- No cube of a number `≥ 5` divides a positive `x < 125`. -/
theorem not_cube_dvd_of_lt {q x : ℕ} (h5 : 5 ≤ q) (hx0 : 0 < x) (hx : x < 125) :
    ¬ q ^ 3 ∣ x := by
  intro h
  have h1 := Nat.le_of_dvd hx0 h
  have h2 : 5 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left h5 3
  omega

/-- The conjecture at `n = 2 q` for every prime `q`. -/
theorem statement_at_two_mul {q : ℕ} (hq : q.Prime) :
    Nat.gcd (2 * q) (a (2 * q - 1)) = a089026 (2 * q) := by
  rw [mul_comm 2 q]
  apply statement_at_mul hq le_rfl
  · intro r hr hrt
    exact Nat.le_of_dvd (by norm_num) hrt |>.trans (by norm_num)
  · intro h5
    rw [show 2 - 1 = 1 from rfl, a_one]
    exact not_cube_dvd_of_lt h5 (by norm_num) (by norm_num)

/-- The conjecture at `n = 3 q` for every prime `q`. -/
theorem statement_at_three_mul {q : ℕ} (hq : q.Prime) :
    Nat.gcd (3 * q) (a (3 * q - 1)) = a089026 (3 * q) := by
  rw [mul_comm 3 q]
  apply statement_at_mul hq (by norm_num)
  · intro r hr hrt
    exact Nat.le_of_dvd (by norm_num) hrt |>.trans (by norm_num)
  · intro h5
    rw [show 3 - 1 = 2 from rfl, a_two]
    exact not_cube_dvd_of_lt h5 (by norm_num) (by norm_num)

/-- The conjecture at `n = 4 q` for every prime `q`. -/
theorem statement_at_four_mul {q : ℕ} (hq : q.Prime) :
    Nat.gcd (4 * q) (a (4 * q - 1)) = a089026 (4 * q) := by
  rw [mul_comm 4 q]
  apply statement_at_mul hq (by norm_num)
  · intro r hr hrt
    have : r ∣ 2 := hr.dvd_of_dvd_pow (show r ∣ 2 ^ 2 by simpa using hrt)
    exact Nat.le_of_dvd (by norm_num) this |>.trans (by norm_num)
  · intro h5
    rw [show 4 - 1 = 3 from rfl, a_three]
    exact not_cube_dvd_of_lt h5 (by norm_num) (by norm_num)

/-- The conjecture at `n = 5 q` for every prime `q`. -/
theorem statement_at_five_mul {q : ℕ} (hq : q.Prime) :
    Nat.gcd (5 * q) (a (5 * q - 1)) = a089026 (5 * q) := by
  rw [mul_comm 5 q]
  apply statement_at_mul hq (by norm_num)
  · intro r hr hrt
    exact Nat.le_of_dvd (by norm_num) hrt
  · intro h5 h
    rw [show 5 - 1 = 4 from rfl, a_four] at h
    have h1 := Nat.le_of_dvd (by norm_num) h
    have h2 : q ≤ 5 := by
      by_contra h6
      have : 6 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
      omega
    obtain rfl : q = 5 := by omega
    norm_num at h

/-- The conjecture at `n = 6 q` for every prime `q`. -/
theorem statement_at_six_mul {q : ℕ} (hq : q.Prime) :
    Nat.gcd (6 * q) (a (6 * q - 1)) = a089026 (6 * q) := by
  rw [mul_comm 6 q]
  apply statement_at_mul hq (by norm_num)
  · intro r hr hrt
    have := Nat.le_of_dvd (by norm_num) hrt
    by_contra h
    obtain rfl : r = 6 := by omega
    exact absurd hr (by decide)
  · intro h5 h
    rw [show 6 - 1 = 5 from rfl, a_five] at h
    have h1 := Nat.le_of_dvd (by norm_num) h
    have h2 : q ≤ 17 := by
      by_contra h6
      have : 18 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
      omega
    interval_cases q <;> norm_num at h

/-- The conjecture at `n = q ^ 2` for primes `q ≥ 5` with `q ^ 3 ∤ a (q - 1)`. -/
theorem statement_at_sq {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (hc : ¬ q ^ 3 ∣ a (q - 1)) :
    Nat.gcd (q ^ 2) (a (q ^ 2 - 1)) = a089026 (q ^ 2) := by
  have hnp : ¬ (q ^ 2).Prime := Nat.Prime.not_prime_pow' (by norm_num)
  rw [gcd_eq_a089026_iff hnp]
  intro r hr hrn hra
  have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow hrn)
  subst hrq
  rw [sq] at hra
  have h1 := (dvd_a_iff hr h5 (by omega)).mp hra
  have h2 := padicValRat_le_of_not_pow_dvd (q := r) (e := 2) (x := H2 (r - 1)) hc
  omega

/-- If `v_q(H2 (q - 1)) ≤ 1`, then `v_q(H2 (q ^ j - 1)) ≤ 1` for all `j ≥ 1`. -/
theorem padicValRat_H2_pow_sub_one {q : ℕ} [hq : Fact q.Prime]
    (hw : padicValRat q (H2 (q - 1)) ≤ 1) :
    ∀ j, 1 ≤ j → padicValRat q (H2 (q ^ j - 1)) ≤ 1 := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => simpa using hw
  | succ j hj ih =>
    have hq1 := hq.out.one_lt
    have hqj : q ≤ q ^ j := by
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ j := Nat.pow_le_pow_right (by omega) hj
    have hm : q * (q ^ j - 1) = q * q ^ j - q := Nat.mul_sub_one q (q ^ j)
    have hqq : q ≤ q * q ^ j := Nat.le_mul_of_pos_right q (by omega)
    have heq : q ^ (j + 1) - 1 = q * (q ^ j - 1) + (q - 1) := by
      rw [pow_succ', hm]
      omega
    have hs : 1 ≤ q ^ j - 1 := by omega
    rw [heq, padicValRat_H2_mul_add hs (by omega) ih]
    omega

/-- The conjecture at `n = q ^ k` (`k ≥ 2`) for primes `q ≥ 5` with `q ^ 2 ∤ a (q - 1)`. -/
theorem statement_at_prime_pow {q k : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (hk : 2 ≤ k)
    (hw : ¬ q ^ 2 ∣ a (q - 1)) :
    Nat.gcd (q ^ k) (a (q ^ k - 1)) = a089026 (q ^ k) := by
  haveI := Fact.mk hq
  have hnp : ¬ (q ^ k).Prime := Nat.Prime.not_prime_pow' (by omega)
  rw [gcd_eq_a089026_iff hnp]
  intro r hr hrn hra
  have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow hrn)
  subst hrq
  have hk' : r ^ k = r * r ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have ht : 2 ≤ r ^ (k - 1) := by
    calc 2 ≤ r := hr.two_le
      _ = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ (k - 1) := Nat.pow_le_pow_right hr.pos (by omega)
  rw [hk'] at hra
  have h1 := (dvd_a_iff hr h5 ht).mp hra
  have h2 := padicValRat_H2_pow_sub_one
    (padicValRat_le_of_not_pow_dvd (q := r) (e := 1) (x := H2 (r - 1)) hw) (k - 1) (by omega)
  omega

end AgenticConjectures.OeisA007406
