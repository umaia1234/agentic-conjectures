import Mathlib

/-!
# OEIS A242560 — a closed form and the even-index formula

The canonical OEIS entry defines `a(N)` as the least integer `k` such that
`(N! - k) / (N - k)` is an integer, and conjectures `a(2n) = n`.  Its PARI
program starts at `k = 1`, so we make the intended positivity explicit.  We
interpret integrality as divisibility in `ℤ` and exclude `k = N`, where the
displayed quotient has denominator zero, as the PARI program also does.

The theorems below prove the stronger closed form
`a(N) = N - N / N.minFac` for `N > 1` and the advertised even-index formula.
The latter uses the OEIS offset `N = 1, 2, ...`; its hypothesis `0 < n`
therefore covers exactly the positive even indices.  Integer subtraction is
used in `Admissible`, so there is no natural-number truncated subtraction
mismatch.

Canonical source (checked 2026-08-12): https://oeis.org/A242560
-/

namespace AgenticConjectures.OeisA242560

/-- `k` is a positive candidate in the minimization defining OEIS A242560. -/
def Admissible (N k : ℕ) : Prop :=
  0 < k ∧ k ≠ N ∧
    ((N : ℤ) - (k : ℤ)) ∣ ((N.factorial : ℤ) - (k : ℤ))

private theorem admissible_exists (N : ℕ) : ∃ k, Admissible N k := by
  refine ⟨N + 1, by omega, by omega, ?_⟩
  refine ⟨-((N.factorial : ℤ) - (N + 1 : ℕ)), ?_⟩
  push_cast
  ring

/-- OEIS A242560, defined as the least positive admissible `k`. -/
noncomputable def a (N : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (admissible_exists N)

/-- The conjectured formula in OEIS A242560: `a(2n) = n` for every `n ≥ 1`. -/
theorem a_two_mul (n : ℕ) (hn : 0 < n) : a (2 * n) = n := by
  classical
  rw [a, Nat.find_eq_iff]
  constructor
  · refine ⟨hn, by omega, ?_⟩
    have hfacNat : n ∣ (2 * n).factorial := Nat.dvd_factorial hn (by omega)
    have hfacInt : (n : ℤ) ∣ ((2 * n).factorial : ℤ) := by
      exact_mod_cast hfacNat
    have hnInt : (n : ℤ) ∣ (n : ℤ) := dvd_refl _
    convert hfacInt.sub hnInt using 1
    push_cast
    ring
  · intro k hk hadmissible
    rcases hadmissible with ⟨hkpos, _, hkdiv⟩
    have hk_le : k ≤ 2 * n := by omega
    have hdpos : 0 < 2 * n - k := by omega
    have hdfacNat : 2 * n - k ∣ (2 * n).factorial :=
      Nat.dvd_factorial hdpos (Nat.sub_le _ _)
    have hdfacInt : ((2 * n - k : ℕ) : ℤ) ∣ ((2 * n).factorial : ℤ) := by
      exact_mod_cast hdfacNat
    have hkdiv' : ((2 * n - k : ℕ) : ℤ) ∣
        ((2 * n).factorial : ℤ) - (k : ℤ) := by
      simpa [Nat.cast_sub hk_le] using hkdiv
    have hdkInt : ((2 * n - k : ℕ) : ℤ) ∣ (k : ℤ) := by
      simpa only [sub_sub_cancel] using hdfacInt.sub hkdiv'
    have hdkNat : 2 * n - k ∣ k := by
      exact_mod_cast hdkInt
    have := Nat.le_of_dvd hkpos hdkNat
    omega

/-- Below the singular candidate `k = N`, admissibility is equivalent to the
complementary difference `N - k` dividing `N`. -/
theorem admissible_iff_sub_dvd (N k : ℕ) (hkpos : 0 < k) (hklt : k < N) :
    Admissible N k ↔ N - k ∣ N := by
  have hk_le : k ≤ N := hklt.le
  have hdpos : 0 < N - k := Nat.sub_pos_of_lt hklt
  have hdfacNat : N - k ∣ N.factorial :=
    Nat.dvd_factorial hdpos (Nat.sub_le _ _)
  have hdfacInt : ((N - k : ℕ) : ℤ) ∣ (N.factorial : ℤ) := by
    exact_mod_cast hdfacNat
  constructor
  · rintro ⟨_, _, hkdiv⟩
    have hkdiv' : ((N - k : ℕ) : ℤ) ∣
        (N.factorial : ℤ) - (k : ℤ) := by
      simpa [Nat.cast_sub hk_le] using hkdiv
    have hdkInt : ((N - k : ℕ) : ℤ) ∣ (k : ℤ) := by
      simpa only [sub_sub_cancel] using hdfacInt.sub hkdiv'
    have hdkNat : N - k ∣ k := by
      exact_mod_cast hdkInt
    have : N - k ∣ (N - k) + k := dvd_add (dvd_refl _) hdkNat
    simpa only [Nat.sub_add_cancel hk_le] using this
  · intro hdN
    refine ⟨hkpos, ne_of_lt hklt, ?_⟩
    have hdkNat : N - k ∣ k := by
      have : N - k ∣ N - (N - k) := Nat.dvd_sub hdN (dvd_refl _)
      simpa only [Nat.sub_sub_self hk_le] using this
    have hdkInt : ((N - k : ℕ) : ℤ) ∣ (k : ℤ) := by
      exact_mod_cast hdkNat
    have hout : ((N - k : ℕ) : ℤ) ∣
        (N.factorial : ℤ) - (k : ℤ) := hdfacInt.sub hdkInt
    simpa [Nat.cast_sub hk_le] using hout

/-- Stronger closed form: A242560 agrees with `N - N / N.minFac` for every
index `N > 1`. -/
theorem a_eq_sub_div_minFac (N : ℕ) (hN : 1 < N) :
    a N = N - N / N.minFac := by
  classical
  have hNpos : 0 < N := by omega
  have hpprime : N.minFac.Prime := Nat.minFac_prime (by omega)
  have hppos : 0 < N.minFac := Nat.minFac_pos N
  have hpone : 1 < N.minFac := hpprime.one_lt
  have hple : N.minFac ≤ N := Nat.minFac_le hNpos
  have hqpos : 0 < N / N.minFac := Nat.div_pos hple hppos
  have hqlt : N / N.minFac < N := Nat.div_lt_self hNpos hpone
  have hqdvd : N / N.minFac ∣ N := Nat.div_dvd_of_dvd (Nat.minFac_dvd N)
  rw [a, Nat.find_eq_iff]
  constructor
  · have hkpos : 0 < N - N / N.minFac := Nat.sub_pos_of_lt hqlt
    have hklt : N - N / N.minFac < N := Nat.sub_lt hNpos hqpos
    apply (admissible_iff_sub_dvd N (N - N / N.minFac) hkpos hklt).2
    simpa only [Nat.sub_sub_self (Nat.div_le_self N N.minFac)] using hqdvd
  · intro k hk hadmissible
    have hkltN : k < N := hk.trans (Nat.sub_lt hNpos hqpos)
    have hkpos : 0 < k := hadmissible.1
    have hdpos : 0 < N - k := Nat.sub_pos_of_lt hkltN
    have hdvdN : N - k ∣ N :=
      (admissible_iff_sub_dvd N k hkpos hkltN).1 hadmissible
    have hdleN : N - k ≤ N := Nat.le_of_dvd hNpos hdvdN
    have hcpos : 0 < N / (N - k) := Nat.div_pos hdleN hdpos
    have hcmul : N / (N - k) * (N - k) = N := Nat.div_mul_cancel hdvdN
    have hctwo : 2 ≤ N / (N - k) := by
      by_contra h
      have hc_one : N / (N - k) = 1 := by omega
      rw [hc_one, one_mul] at hcmul
      omega
    have hcdvdN : N / (N - k) ∣ N := Nat.div_dvd_of_dvd hdvdN
    have hpc : N.minFac ≤ N / (N - k) :=
      Nat.minFac_le_of_dvd hctwo hcdvdN
    have hdleq : N - k ≤ N / N.minFac := by
      apply (Nat.le_div_iff_mul_le hppos).2
      calc
        (N - k) * N.minFac = N.minFac * (N - k) := Nat.mul_comm _ _
        _ ≤ (N / (N - k)) * (N - k) := Nat.mul_le_mul_right _ hpc
        _ = N := hcmul
    omega

/-- Under the displayed OEIS definition, `a(25) = 20`; the current official
b-file instead lists 24 at index 25. -/
theorem a_25 : a 25 = 20 := by
  rw [a_eq_sub_div_minFac 25 (by omega)]
  norm_num

end AgenticConjectures.OeisA242560
