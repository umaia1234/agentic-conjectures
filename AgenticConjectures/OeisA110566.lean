import Mathlib

/-!
# OEIS A110566 — not every odd number is a value

OEIS A110566 is `a(n) = lcm(1, …, n) / den(H_n)` (offset 1), where `H_n` is the
`n`-th harmonic number. Jianing Song conjectured (Nov 28 2022) that every odd
number occurs in the sequence. This file refutes that conjecture: `81` never
occurs. More precisely, `v₃(a(n)) ≤ 3` for every `n`, so no odd multiple of `81`
is a value.

## Upstream correspondence

`a` and `statement` are copied term for term from
`problems/oeis-a110566/upstream/110566.lean`, the Formal Conjectures file
`FormalConjectures/OEIS/110566.lean` at commit
`c094b979118b89adb77cf5f8d923ac9dd2e51b1d`. The file keeps the upstream
`open Nat Finset Rat`. `statement` is the proposition of the upstream
`theorem conjecture`, and `not_statement` is its negation. The changes are:

* the `module`, `public import FormalConjecturesUtil`, and `@[expose] public section`
  scaffolding becomes `import Mathlib`;
* the namespace is `AgenticConjectures.OeisA110566`;
* the `@[category …]` and `@[AMS …]` attributes are dropped. They are metadata only;
* the upstream `sorry` is replaced by the proposition `statement`.

`harmonic` is mathlib's `harmonic : ℕ → ℚ`. Formal Conjectures defines no other
`harmonic` that the `open` could pick up. Upstream builds against Lean/mathlib
`v4.33.1` and this repository against `v4.30.0`. The definition
`harmonic n = ∑ i ∈ range n, (↑(i + 1))⁻¹` is identical in both (checked
2026-10-24).

Natural-number division in `a` is exact because `den(H_n)` divides
`lcm(1, …, n)` (`den_dvd_lcm`). The value `a 0 = 1` is irrelevant because the
conjecture quantifies over `n > 0`, matching the OEIS offset.

## Proof

Write `v = v₃` and `k(n) = ⌊log₃ n⌋`.

1. `H_n = H_{⌊n/3⌋} / 3 + R_n`, with `v(R_n) ≥ 0`. Here `R_n` is the sum of `1/j`
   over `j ≤ n` with `3 ∤ j`; the file proves `v(R_n) ≥ 0` by induction on `n`.
   Hence `v(H_n) = v(H_{⌊n/3⌋}) - 1` whenever `n ≥ 3` and
   `v(H_{⌊n/3⌋}) ≤ 0` (`padicValRat_harmonic_step`).
2. Strong induction over the base-3 tree, together with ten explicit values of
   `H_n`, gives:
   * `v(H_n) > 0` only for `n ∈ {2, 7, 22}` (Eswarathasan–Levine);
   * `v(H_n) + k(n) ≤ 3` for every `n`.
3. `v(lcm(1, …, n)) = k(n)` (mathlib's `Nat.factorization_lcmUpto`), and
   `lcm = a(n) · den(H_n)`. Therefore `v(a(n)) = k(n) - v(den H_n) ≤ 3`.
-/

namespace AgenticConjectures.OeisA110566

open Nat Finset Rat

/-- Upstream definition, verbatim: `a(n) = lcm(1, …, n) / den(H_n)`. -/
def a (n : ℕ) : ℕ :=
  (Icc 1 n).lcm id / (harmonic n).den

/-- The proposition of the upstream `theorem conjecture`, verbatim: every odd number
occurs in the sequence. -/
def statement : Prop :=
  ∀ m : ℕ, Odd m → ∃ n > 0, a n = m

/-- Sanity check against OEIS (and the upstream test `a_6`): `a(6) = 60 / 20 = 3`. -/
theorem a_6 : a 6 = 3 := by decide +kernel

/-- The bound `v₃(a(n)) ≤ 3` is attained: `a(66) = 27`. -/
theorem a_66 : a 66 = 27 := by decide +kernel

/-! ### The 3-adic step `H_n = H_{⌊n/3⌋} / 3 + R_n` -/

/-- `R_n = H_n - H_{⌊n/3⌋} / 3`, which is the sum of `1/j` over `j ≤ n` with `3 ∤ j`.
Only `padicValRat_harmonicRest_nonneg` is used below. -/
def harmonicRest (n : ℕ) : ℚ := harmonic n - harmonic (n / 3) / 3

/-- `R_n` is a `3`-adic integer. -/
theorem padicValRat_harmonicRest_nonneg (n : ℕ) : 0 ≤ padicValRat 3 (harmonicRest n) := by
  induction n with
  | zero => simp [harmonicRest]
  | succ n ih =>
    by_cases h : 3 ∣ n + 1
    · have h1 : (n + 1) / 3 = n / 3 + 1 := by omega
      have h2 : ((n + 1 : ℕ) : ℚ) = 3 * ((n / 3 + 1 : ℕ) : ℚ) := by
        exact_mod_cast (show n + 1 = 3 * (n / 3 + 1) by omega)
      have : harmonicRest (n + 1) = harmonicRest n := by
        simp only [harmonicRest, harmonic_succ, h1, h2]
        field_simp
        ring
      rw [this]
      exact ih
    · have h1 : (n + 1) / 3 = n / 3 := by omega
      have : harmonicRest (n + 1) = harmonicRest n + ((n + 1 : ℕ) : ℚ)⁻¹ := by
        simp only [harmonicRest, harmonic_succ, h1]
        ring
      rw [this]
      by_cases h0 : harmonicRest n + ((n + 1 : ℕ) : ℚ)⁻¹ = 0
      · rw [h0]
        simp
      · refine le_trans ?_ (padicValRat.min_le_padicValRat_add h0)
        refine le_min ih ?_
        rw [padicValRat.inv, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd h]
        simp

theorem padicValRat_three : padicValRat 3 (3 : ℚ) = 1 := by
  simpa using padicValRat.self (p := 3) (by norm_num)

/-- If `n ≥ 3` and `v₃(H_{⌊n/3⌋}) ≤ 0`, then `v₃(H_n) = v₃(H_{⌊n/3⌋}) - 1`. -/
theorem padicValRat_harmonic_step (n : ℕ) (hn : 3 ≤ n)
    (h : padicValRat 3 (harmonic (n / 3)) ≤ 0) :
    padicValRat 3 (harmonic n) = padicValRat 3 (harmonic (n / 3)) - 1 := by
  have hm : n / 3 ≠ 0 := by omega
  have hHm : harmonic (n / 3) ≠ 0 := (harmonic_pos hm).ne'
  have hsplit : harmonic n = harmonic (n / 3) / 3 + harmonicRest n := by
    simp only [harmonicRest]
    ring
  have hdiv : padicValRat 3 (harmonic (n / 3) / 3) = padicValRat 3 (harmonic (n / 3)) - 1 := by
    rw [padicValRat.div hHm (by norm_num), padicValRat_three]
  by_cases hR : harmonicRest n = 0
  · rw [hsplit, hR, add_zero, hdiv]
  · rw [hsplit, padicValRat.add_eq_of_lt ?_ ?_ hR ?_, hdiv]
    · rw [← hsplit]
      exact (harmonic_pos (by omega)).ne'
    · exact div_ne_zero hHm (by norm_num)
    · rw [hdiv]
      have := padicValRat_harmonicRest_nonneg n
      omega

/-! ### Ten explicit harmonic numbers -/

/-- A harmonic number equal to `N / D` with `3 ∤ N` and `3 ∤ D` has valuation `0`. -/
theorem padicValRat_harmonic_eq_zero_of_eq {n : ℕ} (N D : ℕ)
    (hH : harmonic n = (N : ℚ) / (D : ℚ)) (hN : ¬ 3 ∣ N) (hD : ¬ 3 ∣ D) :
    padicValRat 3 (harmonic n) = 0 := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (dvd_zero 3)
  have hD0 : D ≠ 0 := by
    rintro rfl
    exact hD (dvd_zero 3)
  rw [hH, padicValRat.div (by exact_mod_cast hN0) (by exact_mod_cast hD0), padicValRat.of_nat,
    padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hN, padicValNat.eq_zero_of_not_dvd hD]
  simp

/-- A harmonic number equal to `3 N / D` with `3 ∤ N` and `3 ∤ D` has valuation `1`. -/
theorem padicValRat_harmonic_eq_one_of_eq {n : ℕ} (N D : ℕ)
    (hH : harmonic n = (3 * N : ℚ) / (D : ℚ)) (hN : ¬ 3 ∣ N) (hD : ¬ 3 ∣ D) :
    padicValRat 3 (harmonic n) = 1 := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (dvd_zero 3)
  have hD0 : D ≠ 0 := by
    rintro rfl
    exact hD (dvd_zero 3)
  rw [hH, padicValRat.div (by positivity) (by exact_mod_cast hD0),
    padicValRat.mul (by norm_num) (by exact_mod_cast hN0), padicValRat_three,
    padicValRat.of_nat, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hN,
    padicValNat.eq_zero_of_not_dvd hD]
  simp

theorem padicValRat_harmonic_2 : padicValRat 3 (harmonic 2) = 1 :=
  padicValRat_harmonic_eq_one_of_eq 1 2 (by norm_num [harmonic, Finset.sum_range_succ])
    (by norm_num) (by norm_num)

theorem padicValRat_harmonic_6 : padicValRat 3 (harmonic 6) = 0 :=
  padicValRat_harmonic_eq_zero_of_eq 49 20 (by norm_num [harmonic, Finset.sum_range_succ])
    (by norm_num) (by norm_num)

theorem padicValRat_harmonic_7 : padicValRat 3 (harmonic 7) = 1 :=
  padicValRat_harmonic_eq_one_of_eq 121 140 (by norm_num [harmonic, Finset.sum_range_succ])
    (by norm_num) (by norm_num)

theorem padicValRat_harmonic_8 : padicValRat 3 (harmonic 8) = 0 :=
  padicValRat_harmonic_eq_zero_of_eq 761 280 (by norm_num [harmonic, Finset.sum_range_succ])
    (by norm_num) (by norm_num)

theorem padicValRat_harmonic_21 : padicValRat 3 (harmonic 21) = 0 :=
  padicValRat_harmonic_eq_zero_of_eq 18858053 5173168
    (by norm_num [harmonic, Finset.sum_range_succ]) (by norm_num) (by norm_num)

theorem padicValRat_harmonic_22 : padicValRat 3 (harmonic 22) = 1 :=
  padicValRat_harmonic_eq_one_of_eq 6364399 5173168
    (by norm_num [harmonic, Finset.sum_range_succ]) (by norm_num) (by norm_num)

theorem padicValRat_harmonic_23 : padicValRat 3 (harmonic 23) = 0 :=
  padicValRat_harmonic_eq_zero_of_eq 444316699 118982864
    (by norm_num [harmonic, Finset.sum_range_succ]) (by norm_num) (by norm_num)

theorem padicValRat_harmonic_66 : padicValRat 3 (harmonic 66) = 0 :=
  padicValRat_harmonic_eq_zero_of_eq 209060999005535159677640233 43787662374178602500420800
    (by norm_num [harmonic, Finset.sum_range_succ]) (by norm_num) (by norm_num)

theorem padicValRat_harmonic_67 : padicValRat 3 (harmonic 67) = 0 :=
  padicValRat_harmonic_eq_zero_of_eq 14050874595745034300902316411
    2933773379069966367528193600
    (by norm_num [harmonic, Finset.sum_range_succ]) (by norm_num) (by norm_num)

theorem padicValRat_harmonic_68 : padicValRat 3 (harmonic 68) = 0 :=
  padicValRat_harmonic_eq_zero_of_eq 14094018321907827923954201611
    2933773379069966367528193600
    (by norm_num [harmonic, Finset.sum_range_succ]) (by norm_num) (by norm_num)

/-! ### Induction over the base-3 tree -/

/-- `v₃(H_n) ≤ 0` unless `n ∈ {2, 7, 22}`. -/
theorem padicValRat_harmonic_nonpos (n : ℕ) (h2 : n ≠ 2) (h7 : n ≠ 7) (h22 : n ≠ 22) :
    padicValRat 3 (harmonic n) ≤ 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n
      · simp
      · simp
      · exact absurd rfl h2
    · by_cases hm : n / 3 = 2 ∨ n / 3 = 7 ∨ n / 3 = 22
      · have : n = 6 ∨ n = 8 ∨ n = 21 ∨ n = 23 ∨ n = 66 ∨ n = 67 ∨ n = 68 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [padicValRat_harmonic_6]
        · rw [padicValRat_harmonic_8]
        · rw [padicValRat_harmonic_21]
        · rw [padicValRat_harmonic_23]
        · rw [padicValRat_harmonic_66]
        · rw [padicValRat_harmonic_67]
        · rw [padicValRat_harmonic_68]
      · simp only [not_or] at hm
        have := ih (n / 3) (by omega) hm.1 hm.2.1 hm.2.2
        rw [padicValRat_harmonic_step n hn this]
        omega

/-- Eswarathasan–Levine for `p = 3`: `v₃(H_n) > 0` exactly for `n ∈ {2, 7, 22}`. -/
theorem padicValRat_harmonic_pos_iff (n : ℕ) :
    0 < padicValRat 3 (harmonic n) ↔ n = 2 ∨ n = 7 ∨ n = 22 := by
  constructor
  · intro h
    by_contra hn
    simp only [not_or] at hn
    have := padicValRat_harmonic_nonpos n hn.1 hn.2.1 hn.2.2
    omega
  · rintro (rfl | rfl | rfl)
    · rw [padicValRat_harmonic_2]
      norm_num
    · rw [padicValRat_harmonic_7]
      norm_num
    · rw [padicValRat_harmonic_22]
      norm_num

/-- `v₃(H_n) + ⌊log₃ n⌋ ≤ 3` for every `n`. -/
theorem padicValRat_harmonic_add_log_le (n : ℕ) :
    padicValRat 3 (harmonic n) + Nat.log 3 n ≤ 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n
      · simp
      · simp
      · rw [padicValRat_harmonic_2]
        norm_num
    · by_cases hm : n / 3 = 2 ∨ n / 3 = 7 ∨ n / 3 = 22
      · have : n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 66 ∨ n = 67 ∨
            n = 68 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [padicValRat_harmonic_6]; norm_num
        · rw [padicValRat_harmonic_7]; norm_num
        · rw [padicValRat_harmonic_8]; norm_num
        · rw [padicValRat_harmonic_21]; norm_num
        · rw [padicValRat_harmonic_22]; norm_num
        · rw [padicValRat_harmonic_23]; norm_num
        · rw [padicValRat_harmonic_66]; norm_num
        · rw [padicValRat_harmonic_67]; norm_num
        · rw [padicValRat_harmonic_68]; norm_num
      · simp only [not_or] at hm
        have hv := padicValRat_harmonic_nonpos (n / 3) hm.1 hm.2.1 hm.2.2
        rw [padicValRat_harmonic_step n hn hv]
        have hlog : Nat.log 3 n = Nat.log 3 (n / 3) + 1 := by
          have h1 := Nat.log_div_base 3 n
          have h2 : 0 < Nat.log 3 n := Nat.log_pos (by norm_num) hn
          omega
        have := ih (n / 3) (by omega)
        rw [hlog]
        push_cast
        linarith

/-! ### From `H_n` to `a(n)` -/

/-- The denominator of `H_n` divides `lcm(1, …, n)`, so the division in `a` is exact. -/
theorem den_dvd_lcm (n : ℕ) : (harmonic n).den ∣ (Icc 1 n).lcm id := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ]
    refine (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd ?_ ?_)
    · exact ih.trans (Finset.lcm_mono (Finset.Icc_subset_Icc_right (by omega)))
    · rw [Rat.inv_natCast_den_of_pos (by omega)]
      exact Finset.dvd_lcm (s := Icc 1 (n + 1)) (f := id) (by simp)

theorem lcm_eq_a_mul_den (n : ℕ) : (Icc 1 n).lcm id = a n * (harmonic n).den :=
  (Nat.div_mul_cancel (den_dvd_lcm n)).symm

theorem a_ne_zero (n : ℕ) : a n ≠ 0 := by
  intro h
  have hL := lcm_eq_a_mul_den n
  rw [h, zero_mul] at hL
  exact Nat.lcmUpto_ne_zero n hL

/-- `v₃(den H_n) ≥ ⌊log₃ n⌋ - 3`. -/
theorem log_le_padicValNat_den (n : ℕ) :
    Nat.log 3 n ≤ padicValNat 3 (harmonic n).den + 3 := by
  have h := padicValRat_harmonic_add_log_le n
  rw [padicValRat_def] at h
  have : (0 : ℤ) ≤ padicValInt 3 (harmonic n).num := by positivity
  omega

/-- **Main bound.** `v₃(a(n)) ≤ 3` for every `n`. -/
theorem padicValNat_a_le (n : ℕ) : padicValNat 3 (a n) ≤ 3 := by
  have hv : padicValNat 3 ((Icc 1 n).lcm id) = Nat.log 3 n := by
    rw [← Nat.factorization_def _ Nat.prime_three]
    exact Nat.factorization_lcmUpto n Nat.prime_three
  rw [lcm_eq_a_mul_den, padicValNat.mul (a_ne_zero n) (harmonic n).den_ne_zero] at hv
  have := log_le_padicValNat_den n
  omega

/-- No term of the sequence is divisible by `81`. In particular no odd multiple of `81`
occurs. -/
theorem not_eightyone_dvd_a (n : ℕ) : ¬ 81 ∣ a n := by
  intro h
  have h' : 3 ^ 4 ∣ a n := by
    norm_num
    exact h
  have := (padicValNat_dvd_iff_le (p := 3) (a_ne_zero n)).mp h'
  have := padicValNat_a_le n
  omega

/-- **Refutation of the A110566 conjecture.** The odd number `81` is not a value. -/
theorem not_statement : ¬ statement := by
  intro h
  obtain ⟨n, -, hn⟩ := h 81 ⟨40, by norm_num⟩
  exact not_eightyone_dvd_a n (by simp [hn])

end AgenticConjectures.OeisA110566
