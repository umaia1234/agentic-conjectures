import Mathlib

/-!
# OEIS A046969, Conjecture I: `a(p) = 12 (2p - 1)`

OEIS A046969 lists the denominators of the coefficients `B_{2n} / (2n (2n - 1))` of Stirling's
series for `log Γ(z)`. Lorenzo Sauras Altuzarra (2020) conjectured: "if n > 2, then
a(A005382(n))/12 is prime", where A005382 lists the primes `p` with `2p - 1` prime
(2, 3, 7, 19, 31, ...). We prove the stronger formula `a p = 12 * (2 * p - 1)` for every prime
`p > 3` with `2p - 1` prime (`a_eq`), hence the conjecture (`conjecture1_holds`).

## Upstream correspondence

`a` is copied term for term from `FormalConjectures/OEIS/46969.lean` in
google-deepmind/formal-conjectures at commit `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
(snapshot in `problems/oeis-a046969/upstream/`). `statement` is the universal closure of the
upstream theorem `OeisA46969.conjecture1`, and `conjecture1` below repeats its signature
verbatim. Truncated subtraction is harmless: `2 * p - 1` and `m - 1 = 2p - 1` only occur with
`p ≥ 1`, where they agree with integer subtraction, and the `n = 0` branch of `a` is never used
because `p` is prime. `a p / 12` is truncating division in `ℕ`, exact here since `12 ∣ a p`.
Conjecture II of the same entry (refuted upstream at `n = 236791`) is out of scope.

## Proof outline

Write `q = 2p - 1`.
1. von Staudt–Clausen (`Bernoulli.vonStaudt_clausen`): `p ≡ 1 (mod 3)`, so the only primes `r`
   with `(r - 1) ∣ 2p` are 2 and 3, and `B_{2p} = N / 6` with `N = 6z - 5` coprime to 6.
2. Faulhaber (`sum_range_pow`) and the denominator bound from von Staudt–Clausen give, for every
   prime `ℓ ≥ 5` and even `m`, `∑_{k<ℓ} k^m ≡ ℓ B_m (mod ℓ²)` in `ℤ_(ℓ)`
   (`padicNorm_sum_pow_sub_le`).
3. Doubling `k ↦ 2k mod ℓ` (Voronoi's congruence with multiplier 2, `voronoi_two`) gives
   `(2^m - 1) ∑_{k<ℓ} k^m ≡ ℓ m ∑_{j<(ℓ-1)/2} (2j+1)^(m-1) (mod ℓ²)` in `ℤ`.
4. Adams half (`prime_dvd_num`): for `ℓ = p`, `m = 2p` the right side vanishes mod `p²` and
   `2^(2p) - 1 ≡ 3 (mod p)` is a unit, so `p² ∣ ∑_{k<p} k^(2p)` and therefore `p ∣ N`.
5. Kummer half (`not_dvd_num`): for `ℓ = q`, `m = q + 1 = 2p`, Fermat's little theorem gives
   `∑_{j<p-1} (2j+1)^q ≡ (p - 1)² ≢ 0 (mod q)`, so `q² ∤ ∑_{k<q} k^(2p)` and therefore `q ∤ N`.
6. With `N = p M`, `B_{2p} / (2p q) = M / (12 q)` and `gcd(M, 12 q) = 1`, so `a p = 12 q`.

Canonical source (checked 2026-10-24): https://oeis.org/A046969
-/

open Finset

namespace AgenticConjectures.OeisA046969

/-- Denominators of coefficients in Stirling's expansion for `log Γ(z)` (OEIS A046969); copied
term for term from the upstream definition `OeisA46969.a`. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let m := 2 * n
    let k := m * (m - 1)
    (bernoulli m / (k : ℚ)).den

/-- OEIS A046969 Conjecture I: `a(p) / 12` is prime for every prime `p > 3` such that `2p - 1`
is prime (the universal closure of the upstream theorem `OeisA46969.conjecture1`). -/
def statement : Prop :=
  ∀ p : ℕ, p.Prime → (2 * p - 1).Prime → 3 < p → (a p / 12).Prime

/-! ### Power sums with the multiplier 2 -/

/-- Splits `range (2h+1)` into its even and odd elements. -/
private theorem sum_range_two_mul_add_one {M : Type*} [AddCommMonoid M] (f : ℕ → M) (h : ℕ) :
    ∑ k ∈ range (2 * h + 1), f k =
      ∑ k ∈ range (h + 1), f (2 * k) + ∑ j ∈ range h, f (2 * j + 1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show 2 * (h + 1) + 1 = 2 * h + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (fun k => f (2 * k)) (h + 1), sum_range_succ (fun j => f (2 * j + 1)) h,
      show 2 * (h + 1) = 2 * h + 1 + 1 by ring]
    abel

/-- Voronoi's congruence with multiplier 2, in integers: for `ℓ = 2h + 1`,
`(2^m - 1) ∑_{k<ℓ} k^m ≡ ℓ m ∑_{j<h} (2j+1)^(m-1) (mod ℓ²)`. -/
theorem voronoi_two (h m : ℕ) :
    ((2 * h + 1 : ℕ) : ℤ) ^ 2 ∣ ((2 : ℤ) ^ m - 1) * ∑ k ∈ range (2 * h + 1), (k : ℤ) ^ m -
      ∑ j ∈ range h, ((2 * j + 1 : ℕ) : ℤ) ^ (m - 1) * ((2 * h + 1 : ℕ) : ℤ) * m := by
  have e1 : (2 : ℤ) ^ m * ∑ k ∈ range (2 * h + 1), (k : ℤ) ^ m =
      ∑ k ∈ range (2 * h + 1), ((2 * k : ℕ) : ℤ) ^ m := by
    rw [mul_sum]; refine sum_congr rfl fun k _ => ?_; push_cast; ring
  have e2 : ∑ k ∈ range (2 * h + 1), ((2 * k : ℕ) : ℤ) ^ m =
      ∑ k ∈ range (h + 1), ((2 * k : ℕ) : ℤ) ^ m +
        ∑ j ∈ range h, (((2 * j + 1 : ℕ) : ℤ) + ((2 * h + 1 : ℕ) : ℤ)) ^ m := by
    rw [show 2 * h + 1 = (h + 1) + h by ring, sum_range_add]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    push_cast; ring
  have e3 := sum_range_two_mul_add_one (fun k => (k : ℤ) ^ m) h
  have key : ((2 : ℤ) ^ m - 1) * ∑ k ∈ range (2 * h + 1), (k : ℤ) ^ m =
      ∑ j ∈ range h, ((((2 * j + 1 : ℕ) : ℤ) + ((2 * h + 1 : ℕ) : ℤ)) ^ m -
        ((2 * j + 1 : ℕ) : ℤ) ^ m) := by
    rw [sub_mul, one_mul, e1, e2, sum_sub_distrib]
    simp only at e3
    rw [e3]
    push_cast
    ring
  rw [key, ← sum_sub_distrib]
  refine dvd_sum fun j _ => ?_
  have := sq_dvd_add_pow_sub_sub ((2 * h + 1 : ℕ) : ℤ) ((2 * j + 1 : ℕ) : ℤ) m
  convert this using 1
  ring

/-- Adams side: `p²` divides `∑_{k<p} k^(2p)` for a prime `p ≥ 5`. -/
theorem sq_dvd_sum_pow_two_mul (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ) ^ 2 ∣ ∑ k ∈ range p, (k : ℤ) ^ (2 * p) := by
  haveI := Fact.mk hp
  obtain ⟨h, hh⟩ : ∃ h, p = 2 * h + 1 := (hp.odd_of_ne_two (by omega)).exists_bit1
  have hv := voronoi_two h (2 * p)
  rw [← hh] at hv
  have h2 : (p : ℤ) ^ 2 ∣ ∑ j ∈ range h, ((2 * j + 1 : ℕ) : ℤ) ^ (2 * p - 1) * (p : ℤ) *
      ((2 * p : ℕ) : ℤ) := by
    refine dvd_sum fun j _ => ⟨((2 * j + 1 : ℕ) : ℤ) ^ (2 * p - 1) * 2, ?_⟩
    push_cast; ring
  have h3 : (p : ℤ) ^ 2 ∣ ((2 : ℤ) ^ (2 * p) - 1) * ∑ k ∈ range p, (k : ℤ) ^ (2 * p) := by
    have := dvd_add hv h2
    rwa [sub_add_cancel] at this
  have hndvd : ¬ (p : ℤ) ∣ (2 : ℤ) ^ (2 * p) - 1 := by
    intro hd
    have h0 : (((2 : ℤ) ^ (2 * p) - 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
    have h4 : (2 : ZMod p) ^ (2 * p) = 4 := by
      rw [mul_comm, pow_mul, ZMod.pow_card]; norm_num
    push_cast at h0
    rw [h4] at h0
    have h3' : ((3 : ℕ) : ZMod p) = 0 := by
      rw [show (3 : ℕ) = 4 - 1 from rfl]; push_cast; linear_combination h0
    rw [ZMod.natCast_eq_zero_iff] at h3'
    have := Nat.le_of_dvd (by norm_num) h3'
    omega
  have hcop : IsCoprime ((p : ℤ) ^ 2) ((2 : ℤ) ^ (2 * p) - 1) := by
    apply IsCoprime.pow_left
    exact ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd).mpr hndvd
  exact hcop.dvd_of_dvd_mul_left h3

private theorem sum_range_odd (h : ℕ) : ∑ j ∈ range h, (2 * j + 1) = h ^ 2 := by
  induction h with
  | zero => simp
  | succ h ih => rw [sum_range_succ, ih]; ring

/-- Kummer side: `q²` does not divide `∑_{k<q} k^(q+1)` when `q = 2h + 1` is prime, `h ≥ 1`. -/
theorem not_sq_dvd_sum_pow_succ (h : ℕ) (hh : 1 ≤ h) (hq : (2 * h + 1).Prime) :
    ¬ ((2 * h + 1 : ℕ) : ℤ) ^ 2 ∣ ∑ k ∈ range (2 * h + 1), (k : ℤ) ^ (2 * h + 2) := by
  set q := 2 * h + 1 with hqdef
  haveI := Fact.mk hq
  intro hS
  have hv := voronoi_two h (2 * h + 2)
  rw [← hqdef, show 2 * h + 2 - 1 = q by omega] at hv
  have h1 : (q : ℤ) ^ 2 ∣ ∑ j ∈ range h, ((2 * j + 1 : ℕ) : ℤ) ^ q * (q : ℤ) *
      ((2 * h + 2 : ℕ) : ℤ) := by
    have := dvd_sub (dvd_mul_of_dvd_right hS ((2 : ℤ) ^ (2 * h + 2) - 1)) hv
    rwa [sub_sub_cancel] at this
  have h2 : (q : ℤ) ∣ ((2 * h + 2 : ℕ) : ℤ) * ∑ j ∈ range h, ((2 * j + 1 : ℕ) : ℤ) ^ q := by
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
    rw [pow_two] at h1
    refine (mul_dvd_mul_iff_left hq0).mp ?_
    convert h1 using 1
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring
  have h3 : ((((2 * h + 2 : ℕ) : ℤ) * ∑ j ∈ range h, ((2 * j + 1 : ℕ) : ℤ) ^ q : ℤ) : ZMod q)
      = ((h ^ 2 : ℕ) : ZMod q) := by
    have hqz : ((2 * h + 2 : ℕ) : ZMod q) = 1 := by
      rw [show 2 * h + 2 = q + 1 by omega, Nat.cast_succ, ZMod.natCast_self, zero_add]
    simp only [Int.cast_mul, Int.cast_sum, Int.cast_pow, Int.cast_natCast, hqz, one_mul,
      ZMod.pow_card, ← sum_range_odd h, Nat.cast_sum]
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2, eq_comm,
    ZMod.natCast_eq_zero_iff] at h3
  have := Nat.le_of_dvd (by omega) (hq.dvd_of_dvd_pow h3)
  omega

/-! ### The power-sum congruence `∑_{k<ℓ} k^m ≡ ℓ B_m (mod ℓ²)` -/

private theorem padicNorm_pow_self (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    padicNorm ℓ ((ℓ : ℚ) ^ n) = (ℓ : ℚ) ^ (-(n : ℤ)) := by
  rw [IsAbsoluteValue.abv_pow (padicNorm ℓ), padicNorm.padicNorm_p_of_prime, zpow_neg,
    zpow_natCast, inv_pow]

private theorem padicNorm_two (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) : padicNorm ℓ (2 : ℚ) = 1 := by
  have h := (padicNorm.nat_eq_one_iff (p := ℓ) 2).mpr fun hd =>
    hℓ ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd)
  exact_mod_cast h

private theorem padicNorm_bernoulli_one (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) :
    padicNorm ℓ (bernoulli 1) = 1 := by
  rw [bernoulli_one, neg_div, padicNorm.neg, padicNorm.div, padicNorm.one, padicNorm_two ℓ hℓ,
    div_one]

/-- von Staudt–Clausen bound: `ℓ² ∤ den(B_n)` for every odd prime `ℓ`, in the form
`|B_n|_ℓ ≤ ℓ`. -/
theorem padicNorm_bernoulli_le (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) (n : ℕ) :
    padicNorm ℓ (bernoulli n) ≤ ℓ := by
  have hℓ1 : (1 : ℚ) ≤ ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt.le
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
    rw [← two_mul, eq_sub_of_add_eq hz.symm]
    refine padicNorm.sub.trans (max_le ((padicNorm.of_int z).trans hℓ1) ?_)
    refine padicNorm.sum_le' (fun r hr => ?_) (by positivity)
    rw [mem_filter] at hr
    haveI := Fact.mk hr.2.1
    rw [padicNorm.div, padicNorm.one]
    by_cases hrl : r = ℓ
    · subst hrl
      rw [padicNorm.padicNorm_p_of_prime, one_div, inv_inv]
    · rw [padicNorm.padicNorm_of_prime_of_ne (Ne.symm hrl), div_one]
      exact hℓ1
  · rcases k with _ | k
    · rw [show 2 * 0 + 1 = 1 from rfl, padicNorm_bernoulli_one ℓ hℓ]
      exact hℓ1
    · rw [bernoulli_eq_zero_of_odd ⟨k + 1, rfl⟩ (by omega), padicNorm.zero]
      positivity

private theorem lt_five_pow (n : ℕ) : n + 3 < 5 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

private theorem padicValNat_add_three_le (ℓ j : ℕ) [Fact ℓ.Prime] (hℓ : 5 ≤ ℓ) (hj : 3 ≤ j) :
    padicValNat ℓ j + 3 ≤ j := by
  have h1 : ℓ ^ padicValNat ℓ j ≤ j := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have h2 : j < ℓ ^ (j - 2) :=
    calc j = (j - 3) + 3 := by omega
      _ < 5 ^ (j - 3 + 1) := lt_five_pow _
      _ ≤ ℓ ^ (j - 3 + 1) := Nat.pow_le_pow_left hℓ _
      _ = ℓ ^ (j - 2) := by congr 1; omega
  have h3 : padicValNat ℓ j < j - 2 :=
    (Nat.pow_lt_pow_iff_right (by omega)).mp (h1.trans_lt h2)
  omega

private theorem padicNorm_pow_div_le (ℓ j : ℕ) [Fact ℓ.Prime] (hℓ : 5 ≤ ℓ) (hj : 3 ≤ j) :
    padicNorm ℓ ((ℓ : ℚ) ^ j / j) ≤ (ℓ : ℚ) ^ (-3 : ℤ) := by
  have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  rw [padicNorm.div, padicNorm_pow_self, padicNorm.eq_zpow_of_nonzero hj0, padicValRat.of_nat,
    ← zpow_sub₀ hℓ0]
  apply zpow_le_zpow_right₀ (by exact_mod_cast (Fact.out : ℓ.Prime).one_lt.le)
  have := padicValNat_add_three_le ℓ j hℓ hj
  omega

/-- Each non-leading Faulhaber term `B_i C(m+1,i) ℓ^(m+1-i) / (m+1)` is `≡ 0 (mod ℓ²)`. -/
private theorem term_bound (ℓ m i : ℕ) [Fact ℓ.Prime] (hℓ : 5 ≤ ℓ) (hm : Even m) (hi : i < m) :
    padicNorm ℓ (bernoulli i * ((m + 1).choose i : ℕ) * (ℓ : ℚ) ^ (m + 1 - i) / (m + 1)) ≤
      (ℓ : ℚ) ^ (-2 : ℤ) := by
  have hℓ2 : ℓ ≠ 2 := by omega
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  set j := m + 1 - i with hj
  have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hm0 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hchoose : ((m.choose i : ℕ) : ℚ) * ((m : ℚ) + 1) = ((m + 1).choose i : ℕ) * (j : ℚ) := by
    exact_mod_cast Nat.choose_mul_succ_eq m i
  have hterm : bernoulli i * ((m + 1).choose i : ℕ) * (ℓ : ℚ) ^ j / (m + 1) =
      bernoulli i * (m.choose i : ℕ) * ((ℓ : ℚ) ^ j / j) := by
    have h' : (((m + 1).choose i : ℕ) : ℚ) / ((m : ℚ) + 1) = ((m.choose i : ℕ) : ℚ) / j := by
      rw [div_eq_div_iff hm0 hj0]
      exact hchoose.symm
    calc bernoulli i * ((m + 1).choose i : ℕ) * (ℓ : ℚ) ^ j / (m + 1)
        = bernoulli i * (ℓ : ℚ) ^ j * ((((m + 1).choose i : ℕ) : ℚ) / ((m : ℚ) + 1)) := by ring
      _ = bernoulli i * (ℓ : ℚ) ^ j * (((m.choose i : ℕ) : ℚ) / j) := by rw [h']
      _ = bernoulli i * (m.choose i : ℕ) * ((ℓ : ℚ) ^ j / j) := by ring
  rw [hterm, padicNorm.mul, padicNorm.mul]
  have hC : padicNorm ℓ ((m.choose i : ℕ) : ℚ) ≤ 1 := padicNorm.of_nat _
  by_cases hij : i + 1 = m
  · have hj2 : j = 2 := by omega
    have hB : padicNorm ℓ (bernoulli i) ≤ 1 := by
      have hodd : Odd i := by
        rcases hm with ⟨k, hk⟩
        exact ⟨k - 1, by omega⟩
      rcases Nat.lt_or_ge i 2 with h | h
      · have : i = 1 := by rcases hodd with ⟨k, hk⟩; omega
        rw [this, padicNorm_bernoulli_one ℓ hℓ2]
      · rw [bernoulli_eq_zero_of_odd hodd (by omega), padicNorm.zero]
        norm_num
    have hP : padicNorm ℓ ((ℓ : ℚ) ^ j / j) = (ℓ : ℚ) ^ (-2 : ℤ) := by
      rw [hj2, padicNorm.div, padicNorm_pow_self]
      have h2 : padicNorm ℓ ((2 : ℕ) : ℚ) = 1 := by exact_mod_cast padicNorm_two ℓ hℓ2
      rw [h2, div_one]
      norm_num
    rw [hP]
    calc padicNorm ℓ (bernoulli i) * padicNorm ℓ ((m.choose i : ℕ) : ℚ) * (ℓ : ℚ) ^ (-2 : ℤ)
        ≤ 1 * 1 * (ℓ : ℚ) ^ (-2 : ℤ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul hB hC (padicNorm.nonneg _) zero_le_one
      _ = (ℓ : ℚ) ^ (-2 : ℤ) := by ring
  · have hj3 : 3 ≤ j := by omega
    have hB := padicNorm_bernoulli_le ℓ hℓ2 i
    have hP := padicNorm_pow_div_le ℓ j hℓ hj3
    calc padicNorm ℓ (bernoulli i) * padicNorm ℓ ((m.choose i : ℕ) : ℚ) *
          padicNorm ℓ ((ℓ : ℚ) ^ j / j)
        ≤ (ℓ : ℚ) * 1 * (ℓ : ℚ) ^ (-3 : ℤ) := by
          apply mul_le_mul _ hP (padicNorm.nonneg _) (by positivity)
          exact mul_le_mul hB hC (padicNorm.nonneg _) (by positivity)
      _ = (ℓ : ℚ) ^ (-2 : ℤ) := by
          rw [mul_one, show (-2 : ℤ) = -3 + 1 by norm_num, zpow_add_one₀ hℓ0, mul_comm]

/-- `∑_{k<ℓ} k^m ≡ ℓ B_m (mod ℓ²)` in `ℤ_(ℓ)`, for a prime `ℓ ≥ 5` and even `m`. -/
theorem padicNorm_sum_pow_sub_le (ℓ m : ℕ) [Fact ℓ.Prime] (hℓ : 5 ≤ ℓ) (hm : Even m) :
    padicNorm ℓ ((∑ k ∈ range ℓ, (k : ℚ) ^ m) - ℓ * bernoulli m) ≤ (ℓ : ℚ) ^ (-2 : ℤ) := by
  rw [sum_range_pow, sum_range_succ]
  have hlast : bernoulli m * ((m + 1).choose m : ℕ) * (ℓ : ℚ) ^ (m + 1 - m) / (m + 1) =
      ℓ * bernoulli m := by
    rw [Nat.choose_succ_self_right, show m + 1 - m = 1 by omega, pow_one]
    push_cast
    field_simp
  rw [hlast, add_sub_cancel_right]
  exact padicNorm.sum_le' (fun i hi => term_bound ℓ m i hℓ hm (mem_range.mp hi)) (by positivity)

/-! ### The denominator of `B_{2p}` -/

private theorem mod_three_eq_one (p : ℕ) (hp : p.Prime) (hq : (2 * p - 1).Prime) (h3 : 3 < p) :
    p % 3 = 1 := by
  have h1 : ¬ 3 ∣ p := fun hd => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd
    omega
  have h2 : ¬ 3 ∣ 2 * p - 1 := fun hd => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp hd
    omega
  omega

/-- The primes in the von Staudt–Clausen correction sum for `B_{2p}` are exactly `2` and `3`. -/
theorem vonStaudt_primes_eq (p : ℕ) (hp : p.Prime) (hq : (2 * p - 1).Prime) (h3 : 3 < p) :
    (range (2 * p + 2)).filter (fun r => r.Prime ∧ (r - 1) ∣ 2 * p) = {2, 3} := by
  have hp3 := mod_three_eq_one p hp hq h3
  have hp2 : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  ext r
  simp only [mem_filter, mem_range, mem_insert, mem_singleton]
  constructor
  · rintro ⟨-, hr, hdvd⟩
    have hr2 := hr.two_le
    obtain ⟨d1, d2, hd1, hd2, hd⟩ := Nat.dvd_mul.mp hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd1 with rfl | rfl <;>
      rcases (Nat.dvd_prime hp).mp hd2 with rfl | rfl
    · omega
    · exfalso
      have h2r : 2 ∣ r := by omega
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h2r
      omega
    · omega
    · exfalso
      have h3r : 3 ∣ r := by omega
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp h3r
      omega
  · rintro (rfl | rfl)
    · exact ⟨by omega, Nat.prime_two, by simp⟩
    · exact ⟨by omega, Nat.prime_three, dvd_mul_right 2 p⟩

/-- von Staudt–Clausen for `B_{2p}`: `B_{2p} = (6z - 5)/6` for an integer `z`. -/
theorem bernoulli_two_mul_eq (p : ℕ) (hp : p.Prime) (hq : (2 * p - 1).Prime) (h3 : 3 < p) :
    ∃ z : ℤ, bernoulli (2 * p) = ((6 * z - 5 : ℤ) : ℚ) / 6 := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen p
  rw [vonStaudt_primes_eq p hp hq h3, sum_pair (by norm_num)] at hz
  refine ⟨z, ?_⟩
  push_cast at hz ⊢
  rw [hz]
  ring

/-! ### The two halves and the main formula -/

private theorem padicNorm_six (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 5 ≤ ℓ) : padicNorm ℓ (6 : ℚ) = 1 := by
  have h := (padicNorm.nat_eq_one_iff (p := ℓ) 6).mpr fun hd => by
    rcases (Nat.Prime.dvd_mul Fact.out).mp (show ℓ ∣ 2 * 3 from hd) with h | h
    · have := Nat.le_of_dvd (by norm_num) h
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega
  exact_mod_cast h

/-- Adams half: `p` divides the numerator `N` of `B_{2p} = N / 6`. -/
theorem prime_dvd_num (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (N : ℤ)
    (hN : bernoulli (2 * p) = (N : ℚ) / 6) : (p : ℤ) ∣ N := by
  haveI := Fact.mk hp
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hS : padicNorm p (∑ k ∈ range p, (k : ℚ) ^ (2 * p)) ≤ (p : ℚ) ^ (-2 : ℤ) := by
    have := (padicNorm.dvd_iff_norm_le (p := p) (n := 2)
      (z := ∑ k ∈ range p, (k : ℤ) ^ (2 * p))).mp
      (by exact_mod_cast sq_dvd_sum_pow_two_mul p hp h5)
    push_cast at this
    exact this
  have hcong := padicNorm_sum_pow_sub_le p (2 * p) h5 (even_two_mul p)
  have hpB : padicNorm p ((p : ℚ) * bernoulli (2 * p)) ≤ (p : ℚ) ^ (-2 : ℤ) := by
    rw [show (p : ℚ) * bernoulli (2 * p) = (∑ k ∈ range p, (k : ℚ) ^ (2 * p)) -
      ((∑ k ∈ range p, (k : ℚ) ^ (2 * p)) - p * bernoulli (2 * p)) by ring]
    exact padicNorm.sub.trans (max_le hS hcong)
  rw [hN, padicNorm.mul, padicNorm.div, padicNorm_six p h5, div_one,
    padicNorm.padicNorm_p_of_prime, inv_mul_le_iff₀ hp0] at hpB
  apply (padicNorm.int_lt_one_iff N).mp
  calc padicNorm p (N : ℚ) ≤ (p : ℚ) * (p : ℚ) ^ (-2 : ℤ) := hpB
    _ = (p : ℚ)⁻¹ := by
        rw [show (-2 : ℤ) = -1 + -1 by norm_num, zpow_add₀ hp0.ne', zpow_neg_one,
          ← mul_assoc, mul_inv_cancel₀ hp0.ne', one_mul]
    _ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

/-- Kummer half: `q = 2p - 1` does not divide the numerator `N` of `B_{2p} = N / 6`. -/
theorem not_dvd_num (p : ℕ) (hq : (2 * p - 1).Prime) (h5 : 5 ≤ p) (N : ℤ)
    (hN : bernoulli (2 * p) = (N : ℚ) / 6) : ¬ ((2 * p - 1 : ℕ) : ℤ) ∣ N := by
  set q := 2 * p - 1 with hqdef
  haveI := Fact.mk hq
  intro hqN
  have hq5 : 5 ≤ q := by omega
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hq.pos
  have hcong := padicNorm_sum_pow_sub_le q (2 * p) hq5 (even_two_mul p)
  have hNn : padicNorm q (N : ℚ) ≤ (q : ℚ) ^ (-1 : ℤ) := by
    have := (padicNorm.dvd_iff_norm_le (p := q) (n := 1)).mp (by simpa using hqN)
    simpa using this
  have hqB : padicNorm q ((q : ℚ) * bernoulli (2 * p)) ≤ (q : ℚ) ^ (-2 : ℤ) := by
    rw [hN, padicNorm.mul, padicNorm.div, padicNorm_six q hq5, div_one,
      padicNorm.padicNorm_p_of_prime, inv_mul_le_iff₀ hq0]
    calc padicNorm q (N : ℚ) ≤ (q : ℚ) ^ (-1 : ℤ) := hNn
      _ = (q : ℚ) * (q : ℚ) ^ (-2 : ℤ) := by
        rw [show (-2 : ℤ) = -1 + -1 by norm_num, zpow_add₀ hq0.ne', zpow_neg_one,
          ← mul_assoc, mul_inv_cancel₀ hq0.ne', one_mul]
  have hS : padicNorm q (∑ k ∈ range q, (k : ℚ) ^ (2 * p)) ≤ (q : ℚ) ^ (-2 : ℤ) := by
    rw [show (∑ k ∈ range q, (k : ℚ) ^ (2 * p)) =
      ((∑ k ∈ range q, (k : ℚ) ^ (2 * p)) - q * bernoulli (2 * p)) + q * bernoulli (2 * p) by
        ring]
    exact padicNorm.nonarchimedean.trans (max_le hcong hqB)
  have hdvd : (q : ℤ) ^ 2 ∣ ∑ k ∈ range q, (k : ℤ) ^ (2 * p) := by
    have := (padicNorm.dvd_iff_norm_le (p := q) (n := 2)
      (z := ∑ k ∈ range q, (k : ℤ) ^ (2 * p))).mpr (by push_cast; exact hS)
    exact_mod_cast this
  obtain ⟨h, rfl⟩ : ∃ h, p = h + 1 := ⟨p - 1, by omega⟩
  have hq' : q = 2 * h + 1 := by omega
  apply not_sq_dvd_sum_pow_succ h (by omega) (hq' ▸ hq)
  rw [← hq', show 2 * h + 2 = 2 * (h + 1) by ring]
  exact hdvd

/-- **Main formula.** For a prime `p > 3` with `2p - 1` prime, `a(p) = 12 (2p - 1)`. -/
theorem a_eq (p : ℕ) (hp : p.Prime) (hq : (2 * p - 1).Prime) (h3 : 3 < p) :
    a p = 12 * (2 * p - 1) := by
  have h5 : 5 ≤ p := by
    by_contra h
    have : p = 4 := by omega
    subst this
    norm_num at hp
  obtain ⟨z, hz⟩ := bernoulli_two_mul_eq p hp hq h3
  have hpN := prime_dvd_num p hp h5 _ hz
  have hqN := not_dvd_num p hq h5 _ hz
  obtain ⟨M, hM⟩ := hpN
  set q := 2 * p - 1 with hqdef
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hval : bernoulli (2 * p) / ((2 * p * (2 * p - 1) : ℕ) : ℚ) =
      ((M : ℤ) : ℚ) / (((12 * q : ℕ) : ℤ) : ℚ) := by
    rw [hz, hM, ← hqdef]
    push_cast
    field_simp
    ring
  have h2 : ¬ (2 : ℤ) ∣ M := fun h => by
    have := dvd_mul_of_dvd_right h (p : ℤ)
    rw [← hM] at this
    omega
  have h3' : ¬ (3 : ℤ) ∣ M := fun h => by
    have := dvd_mul_of_dvd_right h (p : ℤ)
    rw [← hM] at this
    omega
  have hqM : ¬ (q : ℤ) ∣ M := fun h => hqN (by
    rw [hM]
    exact dvd_mul_of_dvd_right h (p : ℤ))
  have hcop : IsCoprime M ((12 * q : ℕ) : ℤ) := by
    have c2 : IsCoprime M 2 := (Int.prime_two.irreducible.coprime_iff_not_dvd.mpr h2).symm
    have c3 : IsCoprime M 3 := (Int.prime_three.irreducible.coprime_iff_not_dvd.mpr h3').symm
    have cq : IsCoprime M (q : ℤ) :=
      ((Nat.prime_iff_prime_int.mp hq).irreducible.coprime_iff_not_dvd.mpr hqM).symm
    have : ((12 * q : ℕ) : ℤ) = 2 ^ 2 * 3 * (q : ℤ) := by push_cast; ring
    rw [this]
    exact ((c2.pow_right).mul_right c3).mul_right cq
  have hden := Rat.den_div_eq_of_coprime (a := M) (b := ((12 * q : ℕ) : ℤ))
    (by have := hq.pos; positivity) (Int.isCoprime_iff_gcd_eq_one.mp hcop)
  have ha : a p = (bernoulli (2 * p) / ((2 * p * (2 * p - 1) : ℕ) : ℚ)).den := by
    unfold a
    rw [if_neg hp.ne_zero]
  rw [ha, hval]
  exact_mod_cast hden

/-- **OEIS A046969, Conjecture I** (Sauras Altuzarra, 2020) holds. -/
theorem conjecture1_holds : statement := by
  intro p hp hq h3
  rw [a_eq p hp hq h3, Nat.mul_div_cancel_left _ (by norm_num)]
  exact hq

/-- Conjecture I with the exact signature of the upstream theorem `OeisA46969.conjecture1`. -/
theorem conjecture1 (p : ℕ) (hp : p.Prime) (hp' : (2 * p - 1).Prime) (h3 : 3 < p) :
    (a p / 12).Prime :=
  conjecture1_holds p hp hp' h3

end AgenticConjectures.OeisA046969
