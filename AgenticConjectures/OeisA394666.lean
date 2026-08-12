import Mathlib

/-!
# OEIS A394666 — zero terms of `n! mod (2n - 1)`

OEIS A394666 is the sequence `a(n) = n! mod (2n - 1)`, indexed from `n = 1`.
The entry conjectures that, for `n > 5`, `a(n) = 0` exactly when `2n - 1` is
composite.

This module proves that statement.  If `2n - 1 = u v` is composite, its odd
factors satisfy `u, v >= 3`.  Apart from the excluded case `u = v = 3`
(`n = 5`), one has `u + v <= n`.  Consequently
`uv ∣ u! v! ∣ (u+v)! ∣ n!`.  The converse follows because a prime divisor of
`n!` is at most `n`, whereas `2n - 1 > n`.

Faithfulness notes:
- `Nat.factorial` and `Nat.mod` are the ordinary nonnegative factorial and
  remainder used by OEIS.
- Natural subtraction in `2 * n - 1` agrees with integer subtraction on the
  asserted range `5 < n`.
- The theorem deliberately states the intended tail range `n > 5`.  Read as
  an unrestricted biconditional, the OEIS sentence would miss its own initial
  zero `a(1) = 0`; `zero_classification` records that boundary exception and
  gives the complete classification for positive indices.
-/

namespace AgenticConjectures.OeisA394666

/-- OEIS A394666; the source sequence starts at `n = 1`. -/
def a (n : ℕ) : ℕ :=
  Nat.factorial n % (2 * n - 1)

/-- The OEIS conjecture, with its stated `n > 5` range. -/
def statement : Prop :=
  ∀ n : ℕ, 5 < n → (a n = 0 ↔ ¬(2 * n - 1).Prime)

private lemma composite_modulus_dvd_factorial (n : ℕ) (hn : 5 < n)
    (hcomp : ¬(2 * n - 1).Prime) : 2 * n - 1 ∣ Nat.factorial n := by
  have hm2 : 2 ≤ 2 * n - 1 := by omega
  obtain ⟨u, hu_dvd, hu2, hu_lt⟩ :=
    (Nat.not_prime_iff_exists_dvd_lt hm2).mp hcomp
  obtain ⟨v, huv⟩ := hu_dvd
  have hv2 : 2 ≤ v := by
    by_contra hv
    have hv_cases : v = 0 ∨ v = 1 := by omega
    rcases hv_cases with rfl | rfl
    · simp at huv
      omega
    · simp at huv
      omega

  have hm_odd : Odd (2 * n - 1) := ⟨n - 1, by omega⟩
  have huv_odd : Odd (u * v) := by simpa [huv] using hm_odd
  have hu_odd : Odd u := Nat.Odd.of_mul_left huv_odd
  have hv_odd : Odd v := Nat.Odd.of_mul_right huv_odd
  obtain ⟨cu, hcu⟩ := hu_odd
  obtain ⟨cv, hcv⟩ := hv_odd
  have hu3 : 3 ≤ u := by omega
  have hv3 : 3 ≤ v := by omega

  have huv_sum_le : u + v ≤ n := by
    by_cases hu_eq : u = 3
    · rw [hu_eq] at huv ⊢
      have h3v : 3 * v = v + v + v := by ring
      rw [h3v] at huv
      have hv5 : 5 ≤ v := by
        by_contra hv
        have hv_eq : v = 3 := by omega
        subst v
        omega
      omega
    · have hu5 : 5 ≤ u := by omega
      have hnonneg :
          (0 : ℤ) ≤ ((u : ℤ) - 5) * ((v : ℤ) - 3) :=
        mul_nonneg (by omega) (by omega)
      have htwice : 2 * (u + v) ≤ u * v + 1 := by
        exact_mod_cast (show
          (2 : ℤ) * ((u : ℤ) + (v : ℤ)) ≤ (u : ℤ) * (v : ℤ) + 1 by
            nlinarith)
      omega

  have hu_fac : u ∣ Nat.factorial u := Nat.dvd_factorial (by omega) (le_refl u)
  have hv_fac : v ∣ Nat.factorial v := Nat.dvd_factorial (by omega) (le_refl v)
  have huv_fac : u * v ∣ Nat.factorial u * Nat.factorial v :=
    Nat.mul_dvd_mul hu_fac hv_fac
  have hfac_add : Nat.factorial u * Nat.factorial v ∣ Nat.factorial (u + v) :=
    Nat.factorial_mul_factorial_dvd_factorial_add u v
  have hfac_n : Nat.factorial (u + v) ∣ Nat.factorial n :=
    Nat.factorial_dvd_factorial huv_sum_le
  rw [huv]
  exact huv_fac.trans (hfac_add.trans hfac_n)

/-- **OEIS A394666:** for every `n > 5`, `n! mod (2n-1)` vanishes exactly
when `2n-1` is not prime. -/
theorem a_eq_zero_iff_not_prime : statement := by
  intro n hn
  constructor
  · intro hzero hprime
    have hdiv : 2 * n - 1 ∣ Nat.factorial n :=
      Nat.dvd_iff_mod_eq_zero.mpr hzero
    have hle : 2 * n - 1 ≤ n := hprime.dvd_factorial.mp hdiv
    omega
  · intro hcomp
    exact Nat.dvd_iff_mod_eq_zero.mp
      (composite_modulus_dvd_factorial n hn hcomp)

/-- Complete positive-index classification, including the exceptional initial
zero `a(1) = 0` displayed by OEIS. -/
theorem zero_classification (n : ℕ) (hn : 0 < n) :
    a n = 0 ↔ n = 1 ∨ (5 < n ∧ ¬(2 * n - 1).Prime) := by
  by_cases htail : 5 < n
  · have hmain := a_eq_zero_iff_not_prime
    unfold statement at hmain
    rw [hmain n htail]
    simp [htail, show n ≠ 1 by omega]
  · interval_cases n <;> norm_num [a] at *

end AgenticConjectures.OeisA394666
