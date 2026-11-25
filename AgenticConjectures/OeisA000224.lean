import Mathlib

/-!
# OEIS A000224 — the even-input exclusion

The definition below matches the pinned upstream snapshot
`problems/oeis-a000224/upstream/224_2322a58c.lean`: it counts distinct squares
modulo `n`, including zero. The upstream conjecture says, for `n > 1`, that
`(n * n) ≡ 1` modulo `A000224 n * (A000224 n - 1)` exactly when `n` is an odd
prime. We prove the negative congruence direction for every even `n > 1`.

Faithfulness: the `n = 0` convention, natural-number subtraction, and
`Nat.ModEq` statement are copied exactly; the theorem's `1 < n` hypothesis
excludes the boundary values from the upstream conjecture.

`closed_form_blocks_prime_pow` is the arithmetic half of the odd composite
prime-power exclusion in `problems/oeis-a000224/DETAILS.md` §4. It assumes the
closed form (A224-3) for the residue count and proves that form cannot satisfy
the divisibility. It does not identify `A000224 (p ^ e)` with that closed form;
that counting step remains the informal argument in DETAILS.md.
-/

namespace AgenticConjectures.OeisA000224

open Finset

/-- OEIS A000224: the number of distinct quadratic residues modulo `n`,
including zero. This is copied from the pinned upstream statement. -/
noncomputable def A000224 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else Finset.card ((Finset.range n).image (fun k : ℕ => k ^ 2 % n))

/-- No even `n > 1` satisfies the congruence side of the A000224 conjecture. -/
theorem even_not_conjecture_rhs {n : ℕ} (_hn : 1 < n) (heven : Even n) :
    ¬ (n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)] := by
  intro hmod
  have hd : 2 ∣ A000224 n * (A000224 n - 1) := Nat.two_dvd_mul_sub_one _
  have hmod2 : (n * n) ≡ 1 [MOD 2] := hmod.of_dvd hd
  have hnmod : n % 2 = 0 := Nat.mod_eq_zero_of_dvd heven.two_dvd
  have hsqmod : (n * n) % 2 = 0 := by simp [Nat.mul_mod, hnmod]
  change (n * n) % 2 = 1 % 2 at hmod2
  rw [hsqmod] at hmod2
  norm_num at hmod2

private lemma modEq_sub_one_dvd {m a : ℕ} (h : a ≡ 1 [MOD m]) (ha : 1 ≤ a) : m ∣ a - 1 := by
  have hI : (m : ℤ) ∣ (1 : ℤ) - (a : ℤ) := h.dvd
  have hI' : (m : ℤ) ∣ ((a - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub ha]
    rw [← dvd_neg] at hI
    simpa [neg_sub] using hI
  exact Int.natCast_dvd_natCast.mp hI'

private lemma prime_not_dvd_pow_sub_one {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ¬ p ∣ p ^ k - 1 := by
  intro h
  have hpow : p ∣ p ^ k := dvd_pow_self p hk.ne'
  have hle : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  have : p ∣ p ^ k - (p ^ k - 1) := Nat.dvd_sub hpow h
  exact hp.not_dvd_one (by simpa [Nat.sub_sub_self hle] using this)

/-- The closed form (A224-3) cannot satisfy the A000224 divisibility condition.
`r` is any natural number obeying that form for an odd prime power `p^e` with
`e ≥ 2`; in particular this applies when `r = A000224 (p^e)`, once that
identification is known. -/
theorem closed_form_blocks_prime_pow {p e r : ℕ} (hp : p.Prime) (hodd : Odd p) (he : 2 ≤ e)
    (hr : 2 * (p + 1) * r =
      if Even e then p ^ (e + 1) + p + 2 else p ^ (e + 1) + 2 * p + 1) :
    ¬ (p ^ e * p ^ e) ≡ 1 [MOD r * (r - 1)] := by
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hodd
    exact Nat.not_odd_iff_even.mpr even_two hodd
  have hp3 : 3 ≤ p := by
    have : 2 ≤ p := hp.two_le
    omega
  have hrhs : p ^ (e + 1) ≤ 2 * (p + 1) * r := by
    by_cases heven : Even e
    · rw [if_pos heven] at hr
      omega
    · rw [if_neg heven] at hr
      omega
  have hr2 : 2 ≤ r := by
    have hden : 2 * (p + 1) * 2 ≤ p ^ 3 := by
      have hsq : 9 ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      have hnine : 9 * p ≤ p ^ 3 := by
        calc
          9 * p ≤ p ^ 2 * p := Nat.mul_le_mul_right p hsq
          _ = p ^ 3 := by ring
      omega
    have hpow : p ^ 3 ≤ p ^ (e + 1) := Nat.pow_le_pow_right hp.pos (by omega)
    have : 2 * (p + 1) * 2 ≤ 2 * (p + 1) * r :=
      (hden.trans hpow).trans hrhs
    exact Nat.le_of_mul_le_mul_left this (by omega)
  intro hmod
  have hprod_pos : 1 ≤ p ^ e * p ^ e := by
    have hone : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
    calc
      1 ≤ p ^ e := hone
      _ = p ^ e * 1 := by simp
      _ ≤ p ^ e * p ^ e := Nat.mul_le_mul_left _ hone
  have hdivN : r * (r - 1) ∣ p ^ e * p ^ e - 1 := modEq_sub_one_dvd hmod hprod_pos
  by_cases heven : Even e
  · rw [if_pos heven] at hr
    haveI : Fact p.Prime := ⟨hp⟩
    have hZ := congrArg (Nat.cast (R := ZMod p)) hr
    have h2r : (2 * (r : ZMod p)) = 2 := by
      simpa [ZMod.natCast_self, pow_succ, Nat.cast_add, Nat.cast_mul] using hZ
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h0
      have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h0
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    have hr1 : (r : ZMod p) = 1 := by
      apply mul_left_cancel₀ h2ne
      simpa using h2r
    have hdiv : p ∣ r - 1 := by
      have : ((r - 1 : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_sub (by omega : 1 ≤ r), hr1, Nat.cast_one, sub_self]
      exact (ZMod.natCast_eq_zero_iff (r - 1) p).1 this
    have hpr : p ∣ r * (r - 1) := dvd_mul_of_dvd_right hdiv _
    have hpow : p ∣ p ^ e * p ^ e - 1 := dvd_trans hpr hdivN
    have hsq : p ^ e * p ^ e = p ^ (2 * e) := by rw [← pow_add, two_mul]
    rw [hsq] at hpow
    exact prime_not_dvd_pow_sub_one hp (by omega) hpow
  · rw [if_neg heven] at hr
    have hodd_e : Odd e := Nat.not_even_iff_odd.mp heven
    obtain ⟨k, hk⟩ := hodd_e
    have he3 : 3 ≤ e := by
      have hne2 : e ≠ 2 := by
        intro h
        subst h
        exact heven even_two
      omega
    have hrm1 : 2 * (p + 1) * (r - 1) = p ^ (e + 1) - 1 := by
      apply Nat.cast_injective (R := ℤ)
      have hrZ : ((2 * (p + 1) * r : ℕ) : ℤ) =
          ((p ^ (e + 1) + 2 * p + 1 : ℕ) : ℤ) := congrArg (Nat.cast (R := ℤ)) hr
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ r),
        Nat.cast_sub (Nat.one_le_pow _ _ hp.pos)]
      simp
      have hrZ' : (2 : ℤ) * ((p : ℤ) + 1) * r = (p : ℤ) ^ (e + 1) + 2 * p + 1 := by
        simpa using hrZ
      linarith [hrZ']
    have hdiv1 : r - 1 ∣ p ^ (e + 1) - 1 := ⟨2 * (p + 1), by rw [mul_comm, hrm1]⟩
    have hsq : p ^ e * p ^ e = p ^ (2 * e) := by rw [← pow_add, two_mul]
    have hdiv2 : r - 1 ∣ p ^ (2 * e) - 1 := by
      rw [← hsq]
      exact dvd_trans (dvd_mul_left (r - 1) r) hdivN
    have hgcd_exp : Nat.gcd (2 * e) (e + 1) = 2 := by
      rw [hk]
      have hsplit : Nat.gcd (2 * (2 * k + 1)) (2 * (k + 1)) =
          2 * Nat.gcd (2 * k + 1) (k + 1) := by
        simpa [Nat.mul_add, Nat.add_assoc, two_mul] using Nat.gcd_mul_left 2 (2 * k + 1) (k + 1)
      have hcop : Nat.gcd (2 * k + 1) (k + 1) = 1 := by
        have hsub : 2 * (k + 1) - (2 * k + 1) = 1 := by omega
        have hle : 2 * k + 1 ≤ 2 * (k + 1) := by omega
        apply Nat.eq_one_of_dvd_one
        have hcommon : Nat.gcd (2 * k + 1) (k + 1) ∣ 2 * (k + 1) - (2 * k + 1) :=
          Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.gcd_dvd_right (2 * k + 1) (k + 1)) 2)
            (Nat.gcd_dvd_left (2 * k + 1) (k + 1))
        simpa [hsub] using hcommon
      have hsucc : (2 * k + 1) + 1 = 2 * (k + 1) := by omega
      rw [hsucc, hsplit, hcop, Nat.mul_one]
    have hgcd : Nat.gcd (p ^ (2 * e) - 1) (p ^ (e + 1) - 1) = p ^ 2 - 1 := by
      rw [Nat.pow_sub_one_gcd_pow_sub_one, hgcd_exp]
    have hdivp2 : r - 1 ∣ p ^ 2 - 1 := by
      rw [← hgcd]
      exact Nat.dvd_gcd hdiv2 hdiv1
    let hq : ℕ := (p - 1) * (p ^ 2 + 1) / 2
    have heven_pm1 : Even (p - 1) := by
      obtain ⟨t, ht⟩ := hp.odd_of_ne_two hp2
      exact ⟨t, by omega⟩
    have hdvd : 2 ∣ (p - 1) * (p ^ 2 + 1) := dvd_mul_of_dvd_left heven_pm1.two_dvd _
    have hqmul : 2 * hq = (p - 1) * (p ^ 2 + 1) := Nat.mul_div_cancel' hdvd
    have hid : (p + 1) * ((p - 1) * (p ^ 2 + 1)) = p ^ 4 - 1 := by
      have hp1 : 1 ≤ p := by omega
      have h4 : 1 ≤ p ^ 4 := Nat.one_le_pow _ _ hp.pos
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_sub h4, Nat.cast_pow]
      simp
      ring
    have hidq : 2 * (p + 1) * hq = p ^ 4 - 1 := by
      calc
        2 * (p + 1) * hq = (p + 1) * (2 * hq) := by ring
        _ = (p + 1) * ((p - 1) * (p ^ 2 + 1)) := by rw [hqmul]
        _ = p ^ 4 - 1 := hid
    have hqgt : p ^ 2 - 1 < hq := by
      have hsq : 1 ≤ p ^ 2 := by nlinarith
      have hp1 : 1 ≤ p := by omega
      have hfac : (p - 1) * (p + 1) = p ^ 2 - 1 := by
        apply Nat.cast_injective (R := ℤ)
        rw [Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_sub hsq, Nat.cast_pow]
        simp
        ring
      have hlin : 2 * (p + 1) < p ^ 2 + 1 := by
        have : p ^ 2 ≥ 3 * p := by
          calc
            p ^ 2 = p * p := by ring
            _ ≥ 3 * p := Nat.mul_le_mul_right p hp3
        omega
      have hmul0 : (p - 1) * (2 * (p + 1)) < (p - 1) * (p ^ 2 + 1) :=
        Nat.mul_lt_mul_of_pos_left hlin (Nat.sub_pos_of_lt hp.one_lt)
      have : 2 * (p ^ 2 - 1) < (p - 1) * (p ^ 2 + 1) := by
        have hcomm : 2 * (p ^ 2 - 1) = (p - 1) * (2 * (p + 1)) := by
          rw [← hfac]
          ring
        simpa [hcomm] using hmul0
      have : 2 * (p ^ 2 - 1) < 2 * hq := by simpa [hqmul] using this
      exact Nat.lt_of_mul_lt_mul_left this
    have hlow : hq ≤ r - 1 := by
      have hpow : p ^ 4 ≤ p ^ (e + 1) := Nat.pow_le_pow_right hp.pos (by omega)
      have : p ^ 4 - 1 ≤ p ^ (e + 1) - 1 := by omega
      rw [← hidq, ← hrm1] at this
      exact Nat.le_of_mul_le_mul_left this (Nat.mul_pos (by decide) (Nat.succ_pos p))
    have hgt : p ^ 2 - 1 < r - 1 := hqgt.trans_le hlow
    have hpos : 0 < p ^ 2 - 1 :=
      Nat.sub_pos_of_lt <| (show 1 < 9 by decide).trans_le (Nat.pow_le_pow_left hp3 2)
    exact lt_irrefl _ ((Nat.le_of_dvd hpos hdivp2).trans_lt hgt)

/-- If the residue count of an odd prime power obeys the closed form (A224-3),
the A000224 congruence fails. -/
theorem odd_prime_pow_of_closed_form {p e : ℕ} (hp : p.Prime) (hodd : Odd p) (he : 2 ≤ e)
    (hR : 2 * (p + 1) * A000224 (p ^ e) =
      if Even e then p ^ (e + 1) + p + 2 else p ^ (e + 1) + 2 * p + 1) :
    ¬ (p ^ e * p ^ e) ≡ 1 [MOD A000224 (p ^ e) * (A000224 (p ^ e) - 1)] :=
  closed_form_blocks_prime_pow hp hodd he hR

end AgenticConjectures.OeisA000224
