import Mathlib

/-!
# OEIS A108866 — Ordowski's conjecture: the prime direction and composite families

OEIS A108866 is the numerator of `∑_{k=1}^n 2^k/k`.  Thomas Ordowski conjectured (OEIS
comment, 2020-03-02) that for `n > 3` the numerator of `E_n = -2/n + ∑_{k=1}^n 2^k/k` is
divisible by `n^2` if and only if `n` is prime.

`a` and `ratExpression` are copied term for term from the formal-conjectures file
`FormalConjectures/OEIS/108866.lean` (commit `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`,
snapshot in `problems/oeis-a108866/upstream/`).  `statement` is the upstream `conjecture`
with its hypothesis `n > 3` moved under a universal quantifier; it is the same proposition.
The upstream test lemmas `a_0`–`a_4` and their `eval_a` macro are not copied.  In both files
the sum over `i ∈ range n` of `2^(i+1)/(i+1)` is `∑_{k=1}^n 2^k/k` (index shift `k = i + 1`),
the `if n > 0` branch only matters for `n = 0`, `.num` is the numerator of the reduced
fraction, and `n^2` is cast to `ℤ` before the congruence.

Proved here (the full `statement` is NOT proved):
* `prime_imp`: the prime direction, by the classical argument (Wolstenholme's congruence
  `p^2 ∣ H_{p-1}` and `p ∣ ∑_{k<p} C(p-1,k-1)/k^2`); this is not new.
* the composite direction for the families `not_modEq_of_even` (`2 ∣ n`),
  `not_modEq_of_three_dvd` (`3 ∣ n`, `n` not a power of `3`), `not_modEq_of_lead_one`,
  `not_modEq_of_top_digit` (leading base-`q` digit `c` of `n` with `q ∤ a(c)`) and
  `not_modEq_of_mul_pow` (`n = c q^e` with `q ∤ numerator(E_c)`);
* `statement_iff_composite` and the summary `iff_of_families`.

Method: for a prime `ℓ ∣ n`, if the `ℓ`-adic norm of `E_n` exceeds `1/ℓ`, then `ℓ` does not
divide the numerator of `E_n`, hence neither does `n^2`.
-/

open Finset

namespace AgenticConjectures.OeisA108866

/-- OEIS A108866: the numerator of `∑_{k=1}^n 2^k/k` (upstream definition). -/
noncomputable def a (n : ℕ) : ℕ :=
  (∑ i ∈ Finset.range n, (2 : ℚ) ^ (i + 1) / ((i + 1) : ℚ)).num.natAbs

/-- `E_n = -2/n + ∑_{k=1}^n 2^k/k` for `n > 0` (upstream definition). -/
noncomputable def ratExpression (n : ℕ) : ℚ :=
  if n > 0 then
    (-2 : ℚ) / (n : ℚ) + ∑ i ∈ (Finset.range n), (2 : ℚ) ^ (i + 1) / ((i + 1) : ℚ)
  else
    0

/-- Ordowski's conjecture (OEIS A108866), the upstream `conjecture` as a proposition. -/
def statement : Prop :=
  ∀ n : ℕ, n > 3 → ((ratExpression n).num ≡ 0 [ZMOD (n^2 : ℤ)] ↔ n.Prime)

section identities

theorem sum_choose_succ_div (n : ℕ) :
    ∑ i ∈ range (n + 1), ((n + 1).choose (i + 1) : ℚ) / ((i + 1) : ℚ) =
      ∑ i ∈ range n, (n.choose (i + 1) : ℚ) / ((i + 1) : ℚ) +
        ((2 : ℚ) ^ (n + 1) - 1) / ((n + 1) : ℚ) := by
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hterm : ∀ i ∈ range (n + 1), ((n + 1).choose (i + 1) : ℚ) / ((i + 1) : ℚ) =
      (n.choose (i + 1) : ℚ) / ((i + 1) : ℚ) +
        ((n + 1).choose (i + 1) : ℚ) / ((n + 1) : ℚ) := by
    intro i _
    have h1 : ((n + 1 : ℕ) : ℚ) * (n.choose i : ℚ) =
        ((n + 1).choose (i + 1) : ℚ) * ((i + 1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n i
    have h2 : ((n + 1).choose (i + 1) : ℚ) = (n.choose i : ℚ) + (n.choose (i + 1) : ℚ) := by
      exact_mod_cast Nat.choose_succ_succ' n i
    push_cast at h1 hn
    have hi : ((i : ℚ) + 1) ≠ 0 := by positivity
    field_simp
    linear_combination ((n : ℚ) + 1) * h2 + h1
  rw [sum_congr rfl hterm, sum_add_distrib, sum_range_succ, Nat.choose_succ_self, ← sum_div]
  have hsum : ∑ i ∈ range (n + 1), ((n + 1).choose (i + 1) : ℚ) = (2 : ℚ) ^ (n + 1) - 1 := by
    have h := Nat.sum_range_choose (n + 1)
    rw [sum_range_succ'] at h
    have h' : ((∑ i ∈ range (n + 1), (n + 1).choose (i + 1) : ℕ) : ℚ) + 1 =
        (2 : ℚ) ^ (n + 1) := by
      simpa using congrArg (fun x : ℕ => (x : ℚ)) h
    push_cast at h'
    linarith
  rw [hsum]
  simp

/-- `∑_{k=1}^n 2^k/k = H_n + ∑_{k=1}^n C(n,k)/k`. -/
theorem sum_two_pow_div (n : ℕ) :
    ∑ i ∈ range n, (2 : ℚ) ^ (i + 1) / ((i + 1) : ℚ) =
      ∑ i ∈ range n, 1 / ((i + 1) : ℚ) +
        ∑ i ∈ range n, (n.choose (i + 1) : ℚ) / ((i + 1) : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_choose_succ_div, sum_range_succ, sum_range_succ, ih]
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    field_simp
    ring

/-- `E_{m+1} = H_m + (m+1) ∑_{k=1}^m C(m,k-1)/k^2`. -/
theorem ratExpression_succ (m : ℕ) :
    ratExpression (m + 1) = ∑ i ∈ range m, 1 / ((i + 1) : ℚ) +
      ((m : ℚ) + 1) * ∑ i ∈ range m, (m.choose i : ℚ) / ((i + 1) : ℚ) ^ 2 := by
  rw [ratExpression, if_pos (Nat.succ_pos m), sum_two_pow_div, sum_range_succ (fun i => 1 / _),
    sum_range_succ (fun i => ((m + 1).choose (i + 1) : ℚ) / _), Nat.choose_self, mul_sum]
  have hterm : ∀ i ∈ range m, ((m + 1).choose (i + 1) : ℚ) / ((i + 1) : ℚ) =
      ((m : ℚ) + 1) * ((m.choose i : ℚ) / ((i + 1) : ℚ) ^ 2) := by
    intro i _
    have h1 : ((m + 1 : ℕ) : ℚ) * (m.choose i : ℚ) =
        ((m + 1).choose (i + 1) : ℚ) * ((i + 1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq m i
    push_cast at h1
    have hi : ((i : ℚ) + 1) ≠ 0 := by positivity
    field_simp
    linear_combination -h1
  rw [sum_congr rfl hterm]
  push_cast
  have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- `∑_{k=1}^{p-1} (1/k)^2 = 0` in `ZMod p` for a prime `p ≥ 5`. -/
theorem sum_inv_sq_zmod {p : ℕ} [hp : Fact p.Prime] (h5 : 5 ≤ p) :
    ∑ i ∈ range (p - 1), (((i + 1 : ℕ) : ZMod p)⁻¹) ^ 2 = 0 := by
  have hsplit : ∑ i ∈ range (p - 1), (((i + 1 : ℕ) : ZMod p)⁻¹) ^ 2 =
      ∑ i ∈ range p, (((i : ℕ) : ZMod p)⁻¹) ^ 2 := by
    have h := sum_range_succ' (fun i : ℕ => (((i : ℕ) : ZMod p)⁻¹) ^ 2) (p - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ p)] at h
    rw [h]
    simp
  have hreindex : ∑ i ∈ range p, (((i : ℕ) : ZMod p)⁻¹) ^ 2 = ∑ x : ZMod p, (x⁻¹) ^ 2 := by
    refine sum_nbij' (fun i => (i : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
    · intro i _; simp
    · intro x _; simpa using ZMod.val_lt x
    · intro i hi; simpa using ZMod.val_cast_of_lt (mem_range.mp hi)
    · intro x _; simp
    · intro i _; rfl
  have hinv : ∑ x : ZMod p, (x⁻¹) ^ 2 = ∑ x : ZMod p, x ^ 2 :=
    Fintype.sum_equiv (Equiv.inv (ZMod p)) _ _ (fun x => rfl)
  rw [hsplit, hreindex, hinv]
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [ZMod.card]
  omega

end identities

section padic

variable {p : ℕ} [hp : Fact p.Prime]

theorem padicNorm_natCast_eq_one {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    padicNorm p (k : ℚ) = 1 :=
  (padicNorm.nat_eq_one_iff k).2 fun h => absurd (Nat.le_of_dvd hk0 h) (by omega)

theorem padicNorm_succ_eq_one {i : ℕ} (hi : i + 1 < p) : padicNorm p ((i : ℚ) + 1) = 1 := by
  exact_mod_cast padicNorm_natCast_eq_one (p := p) (Nat.succ_pos i) hi

theorem padicNorm_intCast_le_inv {z : ℤ} (h : (p : ℤ) ∣ z) :
    padicNorm p (z : ℚ) ≤ (p : ℚ)⁻¹ := by
  have := (padicNorm.dvd_iff_norm_le (p := p) (n := 1) (z := z)).1 (by simpa using h)
  simpa using this

theorem padicNorm_two_eq_one (hp2 : p ≠ 2) : padicNorm p (2 : ℚ) = 1 := by
  have h2 : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)
  exact_mod_cast padicNorm_natCast_eq_one (p := p) (k := 2) (by norm_num) h2

theorem padicNorm_natCast_le_inv {k : ℕ} (h : p ∣ k) :
    padicNorm p (k : ℚ) ≤ (p : ℚ)⁻¹ := by
  exact_mod_cast padicNorm_intCast_le_inv (p := p) (z := (k : ℤ)) (Int.natCast_dvd_natCast.2 h)

theorem padicNorm_pow (x : ℚ) (k : ℕ) : padicNorm p (x ^ k) = padicNorm p x ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]

theorem padicNorm_sq (x : ℚ) : padicNorm p (x ^ 2) = padicNorm p x ^ 2 :=
  padicNorm_pow x 2

theorem padicNorm_two_pow_eq_one (hp2 : p ≠ 2) (k : ℕ) : padicNorm p ((2 : ℚ) ^ k) = 1 := by
  rw [padicNorm_pow, padicNorm_two_eq_one hp2, one_pow]

theorem padicNorm_prime_pow (e : ℕ) : padicNorm p (((p ^ e : ℕ) : ℚ)) = ((p : ℚ)⁻¹) ^ e := by
  rw [Nat.cast_pow, padicNorm_pow, padicNorm.padicNorm_p_of_prime]

/-- If `‖r‖_p > 1/p`, then `p` does not divide the numerator of `r`. -/
theorem not_dvd_num_of_inv_lt_padicNorm {r : ℚ} (h : (p : ℚ)⁻¹ < padicNorm p r) :
    ¬ (p : ℤ) ∣ r.num := by
  intro hdvd
  have hden : ¬ p ∣ r.den := by
    intro hd
    have h1 : p ∣ r.num.natAbs := Int.natCast_dvd.1 hdvd
    have : Nat.Coprime p p :=
      Nat.Coprime.coprime_dvd_right hd (Nat.Coprime.coprime_dvd_left h1 r.reduced)
    exact hp.out.one_lt.ne' ((Nat.coprime_self p).1 this)
  have hnum : padicNorm p (r.num : ℚ) ≤ (p : ℚ)⁻¹ := padicNorm_intCast_le_inv hdvd
  have h2 : padicNorm p (r.num : ℚ) = padicNorm p r := by
    rw [← Rat.mul_den_eq_num, padicNorm.mul, (padicNorm.nat_eq_one_iff _).2 hden, mul_one]
  linarith

/-- If `p` does not divide the numerator of `r`, then `‖r‖_p ≥ 1`. -/
theorem one_le_padicNorm_of_not_dvd_num {r : ℚ} (h : ¬ (p : ℤ) ∣ r.num) :
    1 ≤ padicNorm p r := by
  have h1 : padicNorm p (r.num : ℚ) = 1 := (padicNorm.int_eq_one_iff _).2 h
  rw [← Rat.mul_den_eq_num, padicNorm.mul] at h1
  have h2 : padicNorm p (r.den : ℚ) ≤ 1 := padicNorm.of_nat _
  have h3 : 0 ≤ padicNorm p r := padicNorm.nonneg _
  nlinarith

end padic

section prime

/-- `p ∣ ∑_{k=1}^{p-1} C(p-1, k-1) / k^2` for an odd prime `p = m + 1`. -/
theorem padicNorm_sum_choose_le {m : ℕ} [hp : Fact (m + 1).Prime] (hodd : m + 1 ≠ 2) :
    padicNorm (m + 1) (∑ i ∈ range m, (m.choose i : ℚ) / ((i + 1) : ℚ) ^ 2) ≤
      ((m + 1 : ℕ) : ℚ)⁻¹ := by
  set F : ℕ → ℚ := fun i => (m.choose i : ℚ) / ((i + 1) : ℚ) ^ 2 with hF
  have h2B : 2 * ∑ i ∈ range m, F i = ∑ j ∈ range m, (F j + F (m - 1 - j)) := by
    rw [sum_add_distrib, sum_range_reflect F m]; ring
  have hterm : ∀ j ∈ range m,
      padicNorm (m + 1) (F j + F (m - 1 - j)) ≤ ((m + 1 : ℕ) : ℚ)⁻¹ := by
    intro j hj
    have hjm : j < m := mem_range.mp hj
    have hcast : ((m - 1 - j : ℕ) : ℚ) + 1 = (m : ℚ) - j := by
      have h : m - 1 - j + 1 + j = m := by omega
      have := congrArg (Nat.cast : ℕ → ℚ) h
      push_cast at this
      linarith
    have hsymm : m.choose (m - 1 - j) = m.choose (j + 1) := by
      rw [show m - 1 - j = m - (j + 1) by omega, Nat.choose_symm (by omega)]
    have hpascal : ((m + 1).choose (j + 1) : ℚ) =
        (m.choose j : ℚ) + (m.choose (j + 1) : ℚ) := by
      exact_mod_cast Nat.choose_succ_succ' m j
    have hj1 : ((j : ℚ) + 1) ≠ 0 := by positivity
    have hmj' : ((m - j : ℕ) : ℚ) = (m : ℚ) - j := by
      rw [Nat.cast_sub hjm.le]
    have hmj : ((m : ℚ) - j) ≠ 0 := by
      rw [← hmj']; exact_mod_cast (show m - j ≠ 0 by omega)
    have key : F j + F (m - 1 - j) =
        ((m + 1).choose (j + 1) : ℚ) / ((j : ℚ) + 1) ^ 2 +
          ((m : ℚ) + 1) * (((m.choose (j + 1) * (2 * j + 1 - m) : ℤ)) : ℚ) /
            (((m - j : ℕ) : ℚ) ^ 2 * ((j : ℚ) + 1) ^ 2) := by
      simp only [hF, hcast, hsymm, hmj']
      rw [hpascal]
      push_cast
      field_simp
      ring
    rw [key]
    refine le_trans padicNorm.nonarchimedean (max_le ?_ ?_)
    · rw [padicNorm.div, padicNorm_sq, padicNorm_succ_eq_one (by omega), one_pow, div_one]
      exact padicNorm_natCast_le_inv (hp.out.dvd_choose_self (by omega) (by omega))
    · have hp' : padicNorm (m + 1) ((m : ℚ) + 1) = ((m + 1 : ℕ) : ℚ)⁻¹ := by
        exact_mod_cast padicNorm.padicNorm_p_of_prime (p := m + 1)
      rw [padicNorm.div, padicNorm.mul, padicNorm.mul, padicNorm_sq, padicNorm_sq, hp',
        padicNorm_succ_eq_one (i := j) (by omega),
        padicNorm_natCast_eq_one (k := m - j) (by omega) (by omega)]
      simp only [one_pow, mul_one, div_one]
      exact mul_le_of_le_one_right (by positivity) (padicNorm.of_int _)
  have h2 : padicNorm (m + 1) (2 * ∑ i ∈ range m, F i) ≤ ((m + 1 : ℕ) : ℚ)⁻¹ := by
    rw [h2B]; exact padicNorm.sum_le' hterm (by positivity)
  rwa [padicNorm.mul, padicNorm_two_eq_one hodd, one_mul] at h2

theorem sum_inv_sq_zmod' {m : ℕ} [Fact (m + 1).Prime] (h5 : 5 ≤ m + 1) :
    ∑ i ∈ range m, (((i + 1 : ℕ) : ZMod (m + 1))⁻¹) ^ 2 = 0 := by
  simpa using sum_inv_sq_zmod (p := m + 1) h5

/-- `p ∣ ∑_{k=1}^{p-1} 1/k^2` for a prime `p = m + 1 ≥ 5`. -/
theorem padicNorm_sum_inv_sq_le {m : ℕ} [Fact (m + 1).Prime] (h5 : 5 ≤ m + 1) :
    padicNorm (m + 1) (∑ i ∈ range m, 1 / ((i + 1) : ℚ) ^ 2) ≤ ((m + 1 : ℕ) : ℚ)⁻¹ := by
  set z : ℕ → ℤ := fun i => ((((i + 1 : ℕ) : ZMod (m + 1))⁻¹).val : ℤ) with hz
  have hzcast : ∀ i, ((z i : ℤ) : ZMod (m + 1)) = ((i + 1 : ℕ) : ZMod (m + 1))⁻¹ := by
    intro i; simp only [hz, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hsplit : ∑ i ∈ range m, 1 / ((i + 1) : ℚ) ^ 2 =
      ∑ i ∈ range m, (1 / ((i + 1) : ℚ) ^ 2 - ((z i ^ 2 : ℤ) : ℚ)) +
        ((∑ i ∈ range m, z i ^ 2 : ℤ) : ℚ) := by
    push_cast; rw [sum_sub_distrib]; ring
  rw [hsplit]
  refine le_trans padicNorm.nonarchimedean (max_le ?_ ?_)
  · refine padicNorm.sum_le' (fun i hi => ?_) (by positivity)
    have him : i < m := mem_range.mp hi
    have hi1 : ((i : ℚ) + 1) ≠ 0 := by positivity
    have heq : 1 / ((i + 1) : ℚ) ^ 2 - ((z i ^ 2 : ℤ) : ℚ) =
        ((1 - ((i + 1 : ℕ) : ℤ) ^ 2 * z i ^ 2 : ℤ) : ℚ) / ((i : ℚ) + 1) ^ 2 := by
      push_cast; field_simp
    rw [heq, padicNorm.div, padicNorm_sq, padicNorm_succ_eq_one (by omega), one_pow, div_one]
    apply padicNorm_intCast_le_inv
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hne : ((i + 1 : ℕ) : ZMod (m + 1)) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
    rw [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_pow, hzcast, Int.cast_one,
      Int.cast_natCast, ← mul_pow, mul_inv_cancel₀ hne, one_pow, sub_self]
  · apply padicNorm_intCast_le_inv
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sum]
    simp only [Int.cast_pow, hzcast]
    exact sum_inv_sq_zmod' h5

/-- Wolstenholme: `p^2 ∣ H_{p-1}` for a prime `p = m + 1 ≥ 5`. -/
theorem padicNorm_harmonic_le {m : ℕ} [hp : Fact (m + 1).Prime] (h5 : 5 ≤ m + 1) :
    padicNorm (m + 1) (∑ i ∈ range m, 1 / ((i + 1) : ℚ)) ≤ (((m + 1 : ℕ) : ℚ)⁻¹) ^ 2 := by
  set H : ℕ → ℚ := fun i => 1 / ((i + 1) : ℚ) with hH
  have hodd : m + 1 ≠ 2 := by omega
  -- `2 H = p ∑ 1/(k (p-k))`
  have h2H : 2 * ∑ i ∈ range m, H i =
      ((m : ℚ) + 1) * ∑ j ∈ range m, 1 / (((j : ℚ) + 1) * ((m - j : ℕ) : ℚ)) := by
    rw [two_mul]
    nth_rewrite 2 [← sum_range_reflect H m]
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hjm : j < m := mem_range.mp hj
    have hcast : ((m - 1 - j : ℕ) : ℚ) + 1 = ((m - j : ℕ) : ℚ) := by
      have h : m - 1 - j + 1 = m - j := by omega
      exact_mod_cast h
    have hj1 : ((j : ℚ) + 1) ≠ 0 := by positivity
    have hmj : ((m - j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show m - j ≠ 0 by omega)
    have hmj' : ((m - j : ℕ) : ℚ) = (m : ℚ) - j := by rw [Nat.cast_sub hjm.le]
    simp only [hH, hcast]
    field_simp
    rw [hmj']
    ring
  -- `∑ 1/(k (p-k)) = ∑ p/(k^2 (p-k)) - ∑ 1/k^2`
  have hsplit : ∑ j ∈ range m, 1 / (((j : ℚ) + 1) * ((m - j : ℕ) : ℚ)) =
      ∑ j ∈ range m, ((m : ℚ) + 1) / (((j : ℚ) + 1) ^ 2 * ((m - j : ℕ) : ℚ)) -
        ∑ j ∈ range m, 1 / ((j + 1) : ℚ) ^ 2 := by
    rw [eq_sub_iff_add_eq, ← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    have hjm : j < m := mem_range.mp hj
    have hj1 : ((j : ℚ) + 1) ≠ 0 := by positivity
    have hmj : ((m - j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show m - j ≠ 0 by omega)
    have hmj' : ((m - j : ℕ) : ℚ) = (m : ℚ) - j := by rw [Nat.cast_sub hjm.le]
    field_simp
    rw [hmj']
    ring
  have hp' : padicNorm (m + 1) ((m : ℚ) + 1) = ((m + 1 : ℕ) : ℚ)⁻¹ := by
    exact_mod_cast padicNorm.padicNorm_p_of_prime (p := m + 1)
  have hinner :
      padicNorm (m + 1) (∑ j ∈ range m, 1 / (((j : ℚ) + 1) * ((m - j : ℕ) : ℚ))) ≤
        ((m + 1 : ℕ) : ℚ)⁻¹ := by
    rw [hsplit]
    refine le_trans padicNorm.sub (max_le ?_ (padicNorm_sum_inv_sq_le h5))
    refine padicNorm.sum_le' (fun j hj => ?_) (by positivity)
    have hjm : j < m := mem_range.mp hj
    rw [padicNorm.div, padicNorm.mul, padicNorm_sq, hp',
      padicNorm_succ_eq_one (i := j) (by omega),
      padicNorm_natCast_eq_one (k := m - j) (by omega) (by omega)]
    simp
  have h2 : padicNorm (m + 1) (2 * ∑ i ∈ range m, H i) ≤ (((m + 1 : ℕ) : ℚ)⁻¹) ^ 2 := by
    rw [h2H, padicNorm.mul, hp', sq]
    exact mul_le_mul_of_nonneg_left hinner (by positivity)
  rwa [padicNorm.mul, padicNorm_two_eq_one hodd, one_mul] at h2

/-- The prime direction of the conjecture: `p^2` divides the numerator of `E_p` for every
prime `p > 3`. -/
theorem prime_imp {p : ℕ} (hp : p.Prime) (h : 3 < p) :
    (ratExpression p).num ≡ 0 [ZMOD (p ^ 2 : ℤ)] := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  haveI := Fact.mk hp
  have h5 : 5 ≤ m + 1 := by
    by_contra hcon
    have h4 : m + 1 = 4 := by omega
    rw [h4] at hp
    norm_num at hp
  have hp' : padicNorm (m + 1) ((m : ℚ) + 1) = ((m + 1 : ℕ) : ℚ)⁻¹ := by
    exact_mod_cast padicNorm.padicNorm_p_of_prime (p := m + 1)
  have hnorm : padicNorm (m + 1) (ratExpression (m + 1)) ≤ (((m + 1 : ℕ) : ℚ)⁻¹) ^ 2 := by
    rw [ratExpression_succ]
    refine le_trans padicNorm.nonarchimedean (max_le (padicNorm_harmonic_le h5) ?_)
    rw [padicNorm.mul, hp', sq]
    exact mul_le_mul_of_nonneg_left (padicNorm_sum_choose_le (by omega)) (by positivity)
  have hnum : padicNorm (m + 1) ((ratExpression (m + 1)).num : ℚ) ≤
      (((m + 1 : ℕ) : ℚ)) ^ (-((2 : ℕ) : ℤ)) := by
    rw [← Rat.mul_den_eq_num, padicNorm.mul, zpow_neg, zpow_natCast, ← inv_pow]
    calc padicNorm (m + 1) (ratExpression (m + 1)) *
          padicNorm (m + 1) ((ratExpression (m + 1)).den : ℚ)
        ≤ (((m + 1 : ℕ) : ℚ)⁻¹) ^ 2 * 1 :=
          mul_le_mul hnorm (padicNorm.of_nat _) (padicNorm.nonneg _) (by positivity)
      _ = (((m + 1 : ℕ) : ℚ)⁻¹) ^ 2 := mul_one _
  have hdvd := (padicNorm.dvd_iff_norm_le (p := m + 1) (n := 2)).2 hnum
  rw [Int.modEq_zero_iff_dvd]
  exact_mod_cast hdvd

end prime

section converse

/-- If some prime factor `ℓ` of `n` has `‖E_n‖_ℓ > 1/ℓ`, then `n^2` does not divide the
numerator of `E_n`. -/
theorem not_modEq_of_padicNorm {n ℓ : ℕ} [Fact ℓ.Prime] (hℓn : ℓ ∣ n)
    (h : (ℓ : ℚ)⁻¹ < padicNorm ℓ (ratExpression n)) :
    ¬ (ratExpression n).num ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  rw [Int.modEq_zero_iff_dvd]
  intro hdvd
  have hℓ : (ℓ : ℤ) ∣ (n : ℤ) ^ 2 :=
    dvd_pow (Int.natCast_dvd_natCast.2 hℓn) two_ne_zero
  exact not_dvd_num_of_inv_lt_padicNorm h (dvd_trans hℓ hdvd)

theorem padicNorm_two_term_lt_one (i : ℕ) :
    padicNorm 2 ((2 : ℚ) ^ (i + 1) / ((i + 1) : ℚ)) < 1 := by
  have hnum : padicNorm 2 (((2 ^ (i + 1) : ℤ)) : ℚ) ≤ (2 : ℚ) ^ (-((i + 1 : ℕ) : ℤ)) :=
    (padicNorm.dvd_iff_norm_le (p := 2) (n := i + 1)).1 (by simp)
  have hden : (2 : ℚ) ^ (-((i + 1 : ℕ) : ℤ)) < padicNorm 2 (((i + 1 : ℕ) : ℤ) : ℚ) := by
    rw [← not_le]
    intro hle
    have hd := (padicNorm.dvd_iff_norm_le (p := 2) (n := i + 1) (z := ((i + 1 : ℕ) : ℤ))).2
      (by exact_mod_cast hle)
    have : 2 ^ (i + 1) ∣ i + 1 := by exact_mod_cast hd
    exact absurd (Nat.le_of_dvd (Nat.succ_pos i) this) (not_le.2 Nat.lt_two_pow_self)
  push_cast at hnum hden
  rw [padicNorm.div, div_lt_one (lt_of_le_of_lt (by positivity) hden)]
  exact lt_of_le_of_lt hnum hden

/-- For even `n`, `‖E_n‖_2 ≥ 1`. -/
theorem one_le_padicNorm_two_of_even {n : ℕ} (hn : 0 < n) (heven : 2 ∣ n) :
    1 ≤ padicNorm 2 (ratExpression n) := by
  rw [ratExpression, if_pos hn]
  have hsum : padicNorm 2 (∑ i ∈ range n, (2 : ℚ) ^ (i + 1) / ((i + 1) : ℚ)) < 1 :=
    padicNorm.sum_lt' (fun i _ => padicNorm_two_term_lt_one i) one_pos
  have h22 : padicNorm 2 (2 : ℚ) = 2⁻¹ := by
    exact_mod_cast padicNorm.padicNorm_p_of_prime (p := 2)
  have hn2 : padicNorm 2 (n : ℚ) ≤ 2⁻¹ := by exact_mod_cast padicNorm_natCast_le_inv heven
  have hpos : 0 < padicNorm 2 (n : ℚ) :=
    lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero (by positivity)).symm
  have hfirst : 1 ≤ padicNorm 2 ((-2 : ℚ) / (n : ℚ)) := by
    rw [padicNorm.div, padicNorm.neg, h22, le_div_iff₀ hpos]
    linarith
  rw [padicNorm.add_eq_max_of_ne (ne_of_gt (lt_of_lt_of_le hsum hfirst))]
  exact le_max_of_le_left hfirst

/-- The composite direction for every even `n > 0`. -/
theorem not_modEq_of_even {n : ℕ} (hn : 0 < n) (heven : 2 ∣ n) :
    ¬ (ratExpression n).num ≡ 0 [ZMOD (n ^ 2 : ℤ)] :=
  not_modEq_of_padicNorm heven
    (lt_of_lt_of_le (by norm_num) (one_le_padicNorm_two_of_even hn heven))

/-- A term `a/k` with `a` an integer and `q^e ∤ k` has `q`-adic norm `< q^e`. -/
theorem padicNorm_div_lt_of_not_dvd {q e : ℕ} [hq : Fact q.Prime] (a : ℤ) {k : ℕ}
    (hk : ¬ q ^ e ∣ k) : padicNorm q ((a : ℚ) / k) < (q : ℚ) ^ e := by
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hq.out.pos
  have hk' : (q : ℚ) ^ (-(e : ℤ)) < padicNorm q (k : ℚ) := by
    rw [← not_le]
    intro hle
    have := (padicNorm.dvd_iff_norm_le (p := q) (n := e) (z := (k : ℤ))).2
      (by exact_mod_cast hle)
    exact hk (by exact_mod_cast this)
  have hpos : 0 < padicNorm q (k : ℚ) := lt_of_le_of_lt (by positivity) hk'
  rw [padicNorm.div, div_lt_iff₀ hpos]
  calc padicNorm q (a : ℚ) ≤ 1 := padicNorm.of_int a
    _ = (q : ℚ) ^ e * (q : ℚ) ^ (-(e : ℤ)) := by
        rw [zpow_neg, zpow_natCast, mul_inv_cancel₀ (by positivity)]
    _ < (q : ℚ) ^ e * padicNorm q (k : ℚ) := by gcongr

/-- Top-level estimate: if `-2/n` plus the terms `2^k/k` of `E_n` with `q^e ∣ k` has
`q`-adic norm `q^e`, then `‖E_n‖_q = q^e`. -/
theorem padicNorm_ratExpression_eq_of_top {q e n : ℕ} [hq : Fact q.Prime] (hn : 0 < n)
    (htop : padicNorm q ((-2 : ℚ) / n + ∑ i ∈ (range n).filter (fun i => q ^ e ∣ i + 1),
      (2 : ℚ) ^ (i + 1) / ((i + 1) : ℚ)) = (q : ℚ) ^ e) :
    padicNorm q (ratExpression n) = (q : ℚ) ^ e := by
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hq.out.pos
  set T := ∑ i ∈ (range n).filter (fun i => q ^ e ∣ i + 1), (2 : ℚ) ^ (i + 1) / ((i + 1) : ℚ)
  set R :=
    ∑ i ∈ (range n).filter (fun i => ¬ q ^ e ∣ i + 1), (2 : ℚ) ^ (i + 1) / ((i + 1) : ℚ)
  have hR : padicNorm q R < (q : ℚ) ^ e := by
    refine padicNorm.sum_lt' (fun i hi => ?_) (by positivity)
    have := padicNorm_div_lt_of_not_dvd (q := q) (e := e) (2 ^ (i + 1)) (mem_filter.1 hi).2
    push_cast at this
    exact this
  rw [ratExpression, if_pos hn,
    ← sum_filter_add_sum_filter_not (range n) (fun i => q ^ e ∣ i + 1)]
  rw [show (-2 : ℚ) / n + (T + R) = ((-2 : ℚ) / n + T) + R by ring]
  rw [padicNorm.add_eq_max_of_ne (by rw [htop]; exact ne_of_gt hR), htop]
  exact max_eq_left hR.le

/-- Top-level estimate when `q^e ∤ n`: if the terms of `E_n` with `q^e ∣ k` have `q`-adic
norm `q^e`, then `‖E_n‖_q = q^e`. -/
theorem padicNorm_ratExpression_eq {q e n : ℕ} [hq : Fact q.Prime] (hn : 0 < n)
    (hQn : ¬ q ^ e ∣ n)
    (htop : padicNorm q (∑ i ∈ (range n).filter (fun i => q ^ e ∣ i + 1),
      (2 : ℚ) ^ (i + 1) / ((i + 1) : ℚ)) = (q : ℚ) ^ e) :
    padicNorm q (ratExpression n) = (q : ℚ) ^ e := by
  refine padicNorm_ratExpression_eq_of_top hn ?_
  have h2 : padicNorm q ((-2 : ℚ) / n) < (q : ℚ) ^ e := by
    have := padicNorm_div_lt_of_not_dvd (q := q) (e := e) (-2) hQn
    push_cast at this
    exact this
  rw [add_comm ((-2 : ℚ) / n), padicNorm.add_eq_max_of_ne (by rw [htop]; exact ne_of_gt h2),
    htop]
  exact max_eq_left h2.le

/-- The terms `2^k/k` with `Q ∣ k ≤ n` are `2^(jQ)/(jQ)` for `1 ≤ j ≤ n / Q`. -/
theorem sum_filter_dvd_succ {Q : ℕ} (n : ℕ) (hQ : 0 < Q) :
    ∑ i ∈ (range n).filter (fun i => Q ∣ i + 1), (2 : ℚ) ^ (i + 1) / ((i + 1) : ℚ) =
      1 / (Q : ℚ) * ∑ j ∈ range (n / Q), (2 : ℚ) ^ ((j + 1) * Q) / ((j : ℚ) + 1) := by
  have hfilter : (range n).filter (fun i => Q ∣ i + 1) =
      (range (n / Q)).image (fun j => (j + 1) * Q - 1) := by
    ext i
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hi, d, hd⟩
      have hd1 : 0 < d := by
        rcases Nat.eq_zero_or_pos d with rfl | h
        · simp at hd
        · exact h
      have hdn : d ≤ n / Q := (Nat.le_div_iff_mul_le hQ).2 (by rw [mul_comm, ← hd]; omega)
      refine ⟨d - 1, by omega, ?_⟩
      rw [Nat.sub_add_cancel hd1, mul_comm]
      omega
    · rintro ⟨j, hj, rfl⟩
      have h1 : (j + 1) * Q ≤ n :=
        le_trans (Nat.mul_le_mul_right Q (show j + 1 ≤ n / Q by omega))
          (Nat.div_mul_le_self n Q)
      have h2 : 1 ≤ (j + 1) * Q := Nat.one_le_iff_ne_zero.mpr (by positivity)
      refine ⟨by omega, ?_⟩
      rw [Nat.sub_add_cancel h2]
      exact Dvd.intro_left _ rfl
  have hinj : Set.InjOn (fun j => (j + 1) * Q - 1) (range (n / Q) : Set ℕ) := by
    intro x _ y _ hxy
    have hx : 1 ≤ (x + 1) * Q := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hy : 1 ≤ (y + 1) * Q := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hxy' : (x + 1) * Q = (y + 1) * Q := by simp only at hxy; omega
    have := Nat.eq_of_mul_eq_mul_right hQ hxy'
    omega
  rw [hfilter, sum_image hinj, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have h2 : 1 ≤ (j + 1) * Q := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hcast : (((j + 1) * Q - 1 : ℕ) : ℚ) + 1 = ((j : ℚ) + 1) * (Q : ℚ) := by
    have := Nat.sub_add_cancel h2
    exact_mod_cast this
  rw [Nat.sub_add_cancel h2, hcast]
  have hQ' : (Q : ℚ) ≠ 0 := by positivity
  have hj : ((j : ℚ) + 1) ≠ 0 := by positivity
  field_simp

/-- For a prime `q > c`, `‖∑_{k=1}^c 2^k/k‖_q ≤ 1`. -/
theorem padicNorm_partial_sum_le_one {q c : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2) (hc : c < q) :
    padicNorm q (∑ i ∈ range c, (2 : ℚ) ^ (i + 1) / ((i + 1) : ℚ)) ≤ 1 := by
  refine padicNorm.sum_le' (fun i hi => ?_) zero_le_one
  have hic : i < c := mem_range.mp hi
  exact le_of_eq (by
    rw [padicNorm.div, padicNorm_two_pow_eq_one hq2, padicNorm_succ_eq_one (p := q) (i := i)
      (by omega), div_one])

/-- Fermat: `2^(k q^e) ≡ 2^k (mod q)`, so for `c < q` the sums `∑_{k=1}^c 2^(k q^e)/k` and
`∑_{k=1}^c 2^k/k` differ by a rational of `q`-adic norm `< 1`. -/
theorem padicNorm_fermat_sub_lt_one {q e c : ℕ} [hq : Fact q.Prime] (hc : c < q) :
    padicNorm q (∑ j ∈ range c, (2 : ℚ) ^ ((j + 1) * q ^ e) / ((j : ℚ) + 1) -
      ∑ j ∈ range c, (2 : ℚ) ^ (j + 1) / ((j + 1) : ℚ)) < 1 := by
  rw [← sum_sub_distrib]
  refine padicNorm.sum_lt' (fun j hj => ?_) one_pos
  have hjc : j < c := mem_range.mp hj
  have hdvd : (q : ℤ) ∣ 2 ^ ((j + 1) * q ^ e) - 2 ^ (j + 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [pow_mul, ZMod.pow_card_pow, sub_self]
  have heq : (2 : ℚ) ^ ((j + 1) * q ^ e) / ((j : ℚ) + 1) - (2 : ℚ) ^ (j + 1) / ((j + 1) : ℚ) =
      ((2 ^ ((j + 1) * q ^ e) - 2 ^ (j + 1) : ℤ) : ℚ) / ((j : ℚ) + 1) := by
    push_cast; ring
  rw [heq, padicNorm.div, padicNorm_succ_eq_one (p := q) (i := j) (by omega), div_one]
  exact lt_of_le_of_lt (padicNorm_intCast_le_inv hdvd)
    (inv_lt_one_of_one_lt₀ (by exact_mod_cast hq.out.one_lt))

/-- Leading-digit criterion: let `q` be an odd prime with `n < q^(e+1)` and `q^e ∤ n`, so that
`c = n / q^e < q` is the leading base-`q` digit of `n`.  If `q ∤ a(c)`, then
`‖E_n‖_q = q^e`. -/
theorem padicNorm_ratExpression_of_top_digit {q e n : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (h2 : n < q ^ (e + 1)) (hr : ¬ q ^ e ∣ n) (ha : ¬ q ∣ a (n / q ^ e)) :
    padicNorm q (ratExpression n) = (q : ℚ) ^ e := by
  have hQ : 0 < q ^ e := pow_pos hq.out.pos e
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (dvd_zero _) hr
    · exact h
  have hc : n / q ^ e < q := Nat.div_lt_of_lt_mul (by rwa [pow_succ] at h2)
  refine padicNorm_ratExpression_eq hn hr ?_
  rw [sum_filter_dvd_succ n hQ, padicNorm.mul, padicNorm.div, padicNorm.one,
    padicNorm_prime_pow]
  have hD := padicNorm_fermat_sub_lt_one (q := q) (e := e) hc
  have hS : padicNorm q (∑ i ∈ range (n / q ^ e), (2 : ℚ) ^ (i + 1) / ((i + 1) : ℚ)) = 1 := by
    refine le_antisymm (padicNorm_partial_sum_le_one hq2 hc)
      (one_le_padicNorm_of_not_dvd_num fun h => ha ?_)
    rw [a]
    exact Int.natCast_dvd.1 h
  generalize ∑ j ∈ range (n / q ^ e), (2 : ℚ) ^ ((j + 1) * q ^ e) / ((j : ℚ) + 1) = U at hD ⊢
  generalize ∑ i ∈ range (n / q ^ e), (2 : ℚ) ^ (i + 1) / ((i + 1) : ℚ) = S at hD hS
  rw [show U = (U - S) + S by ring, padicNorm.add_eq_max_of_ne (by rw [hS]; exact ne_of_lt hD),
    hS, max_eq_right hD.le, mul_one, one_div, inv_pow, inv_inv]

/-- Multiples of a prime power: if `q` is an odd prime, `c < q` and `q` does not divide the
numerator of `E_c`, then `‖E_{c q^e}‖_q = q^e`. -/
theorem padicNorm_ratExpression_of_mul_pow {q e c : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (hc : c < q) (hE : ¬ (q : ℤ) ∣ (ratExpression c).num) :
    padicNorm q (ratExpression (c * q ^ e)) = (q : ℚ) ^ e := by
  have hQ : 0 < q ^ e := pow_pos hq.out.pos e
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · simp [ratExpression] at hE
    · exact h
  refine padicNorm_ratExpression_eq_of_top (Nat.mul_pos hc0 hQ) ?_
  rw [sum_filter_dvd_succ _ hQ, Nat.mul_div_cancel _ hQ]
  have hD := padicNorm_fermat_sub_lt_one (q := q) (e := e) hc
  have hEc : padicNorm q (ratExpression c) = 1 := by
    refine le_antisymm ?_ (one_le_padicNorm_of_not_dvd_num hE)
    rw [ratExpression, if_pos hc0]
    refine le_trans padicNorm.nonarchimedean (max_le (le_of_eq ?_)
      (padicNorm_partial_sum_le_one hq2 hc))
    rw [padicNorm.div, padicNorm.neg, padicNorm_two_eq_one hq2, padicNorm_natCast_eq_one hc0 hc,
      div_one]
  have hEdef : ratExpression c =
      (-2 : ℚ) / (c : ℚ) + ∑ i ∈ range c, (2 : ℚ) ^ (i + 1) / ((i + 1) : ℚ) := by
    rw [ratExpression, if_pos hc0]
  generalize ∑ j ∈ range c, (2 : ℚ) ^ ((j + 1) * q ^ e) / ((j : ℚ) + 1) = U at hD ⊢
  generalize ∑ i ∈ range c, (2 : ℚ) ^ (i + 1) / ((i + 1) : ℚ) = S at hD hEdef
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hsplit : (-2 : ℚ) / ((c * q ^ e : ℕ) : ℚ) + 1 / ((q ^ e : ℕ) : ℚ) * U =
      1 / ((q ^ e : ℕ) : ℚ) * (ratExpression c + (U - S)) := by
    rw [hEdef]
    push_cast
    field_simp
    ring
  rw [hsplit, padicNorm.mul, padicNorm.div, padicNorm.one, padicNorm_prime_pow,
    padicNorm.add_eq_max_of_ne (by rw [hEc]; exact ne_of_gt hD), hEc, max_eq_left hD.le,
    mul_one, one_div, inv_pow, inv_inv]

/-- Leading base-`q` digit `1`: if `q` is an odd prime and `q^e < n < 2 q^e`, then
`‖E_n‖_q = q^e`. -/
theorem padicNorm_ratExpression_of_lead_one {q e n : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (h1 : q ^ e < n) (h2 : n < 2 * q ^ e) :
    padicNorm q (ratExpression n) = (q : ℚ) ^ e := by
  have hQ : 0 < q ^ e := pow_pos hq.out.pos e
  refine padicNorm_ratExpression_eq (by omega) ?_ ?_
  · rintro ⟨c, hc⟩
    have hc1 : 1 < c := by
      by_contra hcon
      interval_cases c <;> simp_all
    have hc2 : c < 2 := by
      by_contra hcon
      have : q ^ e * 2 ≤ q ^ e * c := Nat.mul_le_mul_left _ (by omega)
      omega
    omega
  · have hfilter : (range n).filter (fun i => q ^ e ∣ i + 1) = {q ^ e - 1} := by
      ext i
      simp only [mem_filter, mem_range, mem_singleton]
      constructor
      · rintro ⟨hi, c, hc⟩
        have hc1 : c ≠ 0 := by rintro rfl; simp at hc
        have hc2 : c < 2 := by
          by_contra hcon
          have : q ^ e * 2 ≤ q ^ e * c := Nat.mul_le_mul_left _ (by omega)
          omega
        have : c = 1 := by omega
        subst this
        omega
      · rintro rfl
        exact ⟨by omega, by rw [Nat.sub_add_cancel hQ]⟩
    rw [hfilter, sum_singleton, Nat.sub_add_cancel hQ]
    have hcast : ((q ^ e - 1 : ℕ) : ℚ) + 1 = ((q ^ e : ℕ) : ℚ) := by
      exact_mod_cast Nat.sub_add_cancel hQ
    rw [hcast, padicNorm.div, padicNorm_two_pow_eq_one hq2, padicNorm_prime_pow, inv_pow,
      one_div, inv_inv]

/-- `3 ∤ 2^(3^e + 1) + 2^(2 * 3^e)`. -/
theorem two_pow_add_two_pow_mod_three (e : ℕ) :
    (2 ^ (3 ^ e + 1) + 2 ^ (2 * 3 ^ e)) % 3 = 2 := by
  obtain ⟨k, hk⟩ : Odd (3 ^ e) := Odd.pow (by decide)
  rw [hk, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul, pow_mul, Nat.add_mod, Nat.pow_mod,
    Nat.pow_mod (2 ^ 2)]
  norm_num

/-- Leading base-`3` digit `2` and `n ≠ 2·3^e`: `‖E_n‖_3 = 3^e`. -/
theorem padicNorm_three_ratExpression_of_lead_two {e n : ℕ} (h1 : 2 * 3 ^ e < n)
    (h2 : n < 3 * 3 ^ e) : padicNorm 3 (ratExpression n) = (3 : ℚ) ^ e := by
  have hQ : 0 < 3 ^ e := pow_pos (by norm_num) e
  refine padicNorm_ratExpression_eq (by omega) ?_ ?_
  · rintro ⟨c, hc⟩
    have hc1 : 2 < c := by
      by_contra hcon
      have : 3 ^ e * c ≤ 3 ^ e * 2 := Nat.mul_le_mul_left _ (by omega)
      omega
    have hc2 : c < 3 := by
      by_contra hcon
      have : 3 ^ e * 3 ≤ 3 ^ e * c := Nat.mul_le_mul_left _ (by omega)
      omega
    omega
  · have hfilter :
        (range n).filter (fun i => 3 ^ e ∣ i + 1) = {3 ^ e - 1, 2 * 3 ^ e - 1} := by
      ext i
      simp only [mem_filter, mem_range, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hi, c, hc⟩
        have hc1 : c ≠ 0 := by rintro rfl; simp at hc
        have hc2 : c < 3 := by
          by_contra hcon
          have : 3 ^ e * 3 ≤ 3 ^ e * c := Nat.mul_le_mul_left _ (by omega)
          omega
        interval_cases c <;> omega
      · rintro (rfl | rfl)
        · exact ⟨by omega, by rw [Nat.sub_add_cancel hQ]⟩
        · exact ⟨by omega, by rw [Nat.sub_add_cancel (by omega)]; exact Dvd.intro_left 2 rfl⟩
    rw [hfilter, sum_pair (by omega), Nat.sub_add_cancel hQ, Nat.sub_add_cancel (by omega)]
    have hc1 : ((3 ^ e - 1 : ℕ) : ℚ) + 1 = ((3 ^ e : ℕ) : ℚ) := by
      exact_mod_cast Nat.sub_add_cancel hQ
    have hc2 : ((2 * 3 ^ e - 1 : ℕ) : ℚ) + 1 = 2 * ((3 ^ e : ℕ) : ℚ) := by
      have : 2 * 3 ^ e - 1 + 1 = 2 * 3 ^ e := Nat.sub_add_cancel (by omega)
      exact_mod_cast this
    have hQ' : ((3 ^ e : ℕ) : ℚ) ≠ 0 := by positivity
    have hsum : (2 : ℚ) ^ 3 ^ e / (((3 ^ e - 1 : ℕ) : ℚ) + 1) +
        (2 : ℚ) ^ (2 * 3 ^ e) / (((2 * 3 ^ e - 1 : ℕ) : ℚ) + 1) =
        ((2 ^ (3 ^ e + 1) + 2 ^ (2 * 3 ^ e) : ℕ) : ℚ) / (2 * ((3 ^ e : ℕ) : ℚ)) := by
      rw [hc1, hc2]
      push_cast
      field_simp
      ring
    rw [hsum, padicNorm.div, padicNorm.mul, padicNorm_two_eq_one (by norm_num), one_mul,
      padicNorm_prime_pow, (padicNorm.nat_eq_one_iff _).2, inv_pow, one_div, inv_inv]
    rw [Nat.dvd_iff_mod_eq_zero, two_pow_add_two_pow_mod_three]
    norm_num

theorem inv_lt_prime_pow {q : ℕ} (hq : q.Prime) (e : ℕ) : (q : ℚ)⁻¹ < (q : ℚ) ^ e :=
  calc (q : ℚ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hq.one_lt)
    _ ≤ (q : ℚ) ^ e := one_le_pow₀ (by exact_mod_cast hq.one_lt.le)

/-- The composite direction when an odd prime `q ∣ n` satisfies `q^e < n < 2 q^e`. -/
theorem not_modEq_of_lead_one {q e n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqn : q ∣ n)
    (h1 : q ^ e < n) (h2 : n < 2 * q ^ e) :
    ¬ (ratExpression n).num ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  haveI := Fact.mk hq
  apply not_modEq_of_padicNorm hqn
  rw [padicNorm_ratExpression_of_lead_one hq2 h1 h2]
  exact inv_lt_prime_pow hq e

/-- The composite direction when `3 ∣ n` and `n` is not a power of `3`. -/
theorem not_modEq_of_three_dvd {n : ℕ} (hn : 0 < n) (h3 : 3 ∣ n) (hpow : ∀ k : ℕ, n ≠ 3 ^ k) :
    ¬ (ratExpression n).num ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact not_modEq_of_even hn (even_iff_two_dvd.mp heven)
  · have hle : 3 ^ Nat.log 3 n ≤ n := Nat.pow_log_le_self 3 hn.ne'
    have hlt : n < 3 ^ (Nat.log 3 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have hne : n ≠ 3 ^ Nat.log 3 n := hpow _
    have hne2 : n ≠ 2 * 3 ^ Nat.log 3 n := by
      rintro h
      rw [h] at hodd
      exact (Nat.not_even_iff_odd.2 hodd) (even_two_mul _)
    apply not_modEq_of_padicNorm h3
    rcases lt_or_ge n (2 * 3 ^ Nat.log 3 n) with h | h
    · rw [padicNorm_ratExpression_of_lead_one (by norm_num) (lt_of_le_of_ne hle (Ne.symm hne)) h]
      exact_mod_cast inv_lt_prime_pow Nat.prime_three _
    · rw [padicNorm_three_ratExpression_of_lead_two (lt_of_le_of_ne h (Ne.symm hne2))
        (by rw [pow_succ] at hlt; linarith)]
      exact_mod_cast inv_lt_prime_pow Nat.prime_three _

/-- The composite direction from the leading-digit criterion: an odd prime `q ∣ n` with
`n < q^(e+1)`, `q^e ∤ n` and `q ∤ a(n / q^e)`. -/
theorem not_modEq_of_top_digit {q e n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqn : q ∣ n)
    (h2 : n < q ^ (e + 1)) (hr : ¬ q ^ e ∣ n) (ha : ¬ q ∣ a (n / q ^ e)) :
    ¬ (ratExpression n).num ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  haveI := Fact.mk hq
  apply not_modEq_of_padicNorm hqn
  rw [padicNorm_ratExpression_of_top_digit hq2 h2 hr ha]
  exact inv_lt_prime_pow hq e

/-- The composite direction for `n = c q^e` with `q` an odd prime, `e > 0`, `c < q` and
`q ∤ numerator(E_c)`. -/
theorem not_modEq_of_mul_pow {q e c n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (he : 0 < e)
    (hc : c < q) (hn : n = c * q ^ e) (hE : ¬ (q : ℤ) ∣ (ratExpression c).num) :
    ¬ (ratExpression n).num ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  subst hn
  haveI := Fact.mk hq
  apply not_modEq_of_padicNorm (Dvd.dvd.mul_left (dvd_pow_self q he.ne') c)
  rw [padicNorm_ratExpression_of_mul_pow hq2 hc hE]
  exact inv_lt_prime_pow hq e

end converse

/-- Given the prime direction, the conjecture is equivalent to its composite direction. -/
theorem statement_iff_composite :
    statement ↔ ∀ n : ℕ, 3 < n → ¬ n.Prime →
      ¬ (ratExpression n).num ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  constructor
  · intro h n hn hnp hmod
    exact hnp ((h n hn).1 hmod)
  · intro h n hn
    exact ⟨fun hmod => by_contra fun hnp => h n hn hnp hmod, fun hp => prime_imp hp hn⟩

/-- The conjectured equivalence holds for every `n > 3` that is prime, even, a multiple of `3`
other than a power of `3`, or satisfies the hypotheses of `not_modEq_of_top_digit` or
`not_modEq_of_mul_pow` for some odd prime `q`. -/
theorem iff_of_families {n : ℕ} (hn : 3 < n)
    (h : n.Prime ∨ 2 ∣ n ∨ (3 ∣ n ∧ ∀ k : ℕ, n ≠ 3 ^ k) ∨
      (∃ q e : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ n ∧ n < q ^ (e + 1) ∧ ¬ q ^ e ∣ n ∧
        ¬ q ∣ a (n / q ^ e)) ∨
      (∃ q e c : ℕ, q.Prime ∧ q ≠ 2 ∧ 0 < e ∧ c < q ∧ n = c * q ^ e ∧
        ¬ (q : ℤ) ∣ (ratExpression c).num)) :
    ((ratExpression n).num ≡ 0 [ZMOD (n ^ 2 : ℤ)] ↔ n.Prime) := by
  rcases h with hp | h2 | ⟨h3, hpow⟩ | ⟨q, e, hq, hq2, hqn, h2, hr, ha⟩ |
      ⟨q, e, c, hq, hq2, he, hc, hnc, hE⟩
  · exact iff_of_true (prime_imp hp hn) hp
  · refine iff_of_false (not_modEq_of_even (by omega) h2) fun hp => ?_
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2
    omega
  · refine iff_of_false (not_modEq_of_three_dvd (by omega) h3 hpow) fun hp => ?_
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3
    omega
  · refine iff_of_false (not_modEq_of_top_digit hq hq2 hqn h2 hr ha) fun hp => ?_
    have hqe : q = n := (Nat.prime_dvd_prime_iff_eq hq hp).1 hqn
    subst hqe
    rcases e with _ | _ | e
    · exact hr (by simp)
    · exact hr (by simp)
    · have hlt : q < q ^ (e + 1 + 1) :=
        lt_of_eq_of_lt (pow_one q).symm (Nat.pow_lt_pow_right hq.one_lt (by omega))
      rw [Nat.div_eq_of_lt hlt] at ha
      exact ha (by simp [a])
  · refine iff_of_false (not_modEq_of_mul_pow hq hq2 he hc hnc hE) fun hp => ?_
    rw [hnc] at hp
    rcases Nat.prime_mul_iff.1 hp with ⟨_, h1⟩ | ⟨_, h1⟩
    · exact hq.one_lt.ne' ((Nat.pow_eq_one.1 h1).resolve_right he.ne')
    · subst h1
      have : ratExpression 1 = 0 := by norm_num [ratExpression]
      rw [this] at hE
      exact hE (by simp)

end AgenticConjectures.OeisA108866
