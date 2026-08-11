import Mathlib

/-!
# OEIS A368633 — parity of the coefficients

Let `A(X) = ∑ n, a(n) X^n` be the integer formal power series specified by

`A(X) = 1 + 2 X A(X)^2 - X A(-X)^2`.

OEIS A368633 conjectures that `a(n)` is odd exactly at the indices
`n = 2^k - 1`.  We prove the equivalent subtraction-free statement
`n + 1 = 2^k` for every integer formal power series satisfying the displayed
equation.

The formalization uses `PowerSeries.rescale (-1) A` for `A(-X)`.  Reducing the
equation modulo 2 makes `-1 = 1` and `2 = 0`, so it becomes
`B = 1 + X B^2`.  Frobenius in characteristic 2 identifies `B^2` with the
series obtained by replacing `X` by `X^2`; coefficient induction then gives
the claimed support.

Faithfulness notes: OEIS has offset 0.  The source describes the coefficients
as nonnegative integers, while the theorem works over integer coefficients and
therefore proves a stronger statement.  Oddness is expressed by nonzero image
in `ZMod 2`.  The conclusion `n + 1 = 2^k` is equivalent over naturals to the
source's `n = 2^k - 1` and avoids truncated-subtraction ambiguity.
-/

namespace AgenticConjectures.OeisA368633

open PowerSeries

/-- The exact formal-power-series equation defining OEIS A368633. -/
def SatisfiesEquation (A : PowerSeries ℤ) : Prop :=
  A = 1 + 2 * X * A ^ 2 - X * (PowerSeries.rescale (-1) A) ^ 2

private noncomputable def modTwo (A : PowerSeries ℤ) : PowerSeries (ZMod 2) :=
  A.map (Int.castRingHom (ZMod 2))

private lemma modTwo_equation {A : PowerSeries ℤ} (hA : SatisfiesEquation A) :
    modTwo A = 1 + X * (modTwo A) ^ 2 := by
  unfold SatisfiesEquation at hA
  unfold modTwo
  calc
    PowerSeries.map (Int.castRingHom (ZMod 2)) A =
        PowerSeries.map (Int.castRingHom (ZMod 2))
          (1 + 2 * X * A ^ 2 - X * (PowerSeries.rescale (-1) A) ^ 2) :=
      congrArg _ hA
    _ = 1 + X * (PowerSeries.map (Int.castRingHom (ZMod 2)) A) ^ 2 := by
      have htwo : PowerSeries.map (Int.castRingHom (ZMod 2))
          (2 : PowerSeries ℤ) = 0 := by
        ext n
        simp only [PowerSeries.coeff_map, map_zero]
        have hsrc : (2 : PowerSeries ℤ) = 1 + 1 :=
          one_add_one_eq_two.symm
        rw [hsrc]
        simp only [map_add, PowerSeries.coeff_one]
        by_cases hn : n = 0
        · subst n
          simp only [↓reduceIte, map_one]
          exact CharTwo.add_self_eq_zero 1
        · simp [hn]
      have hneg : (Int.castRingHom (ZMod 2)) (-1) = 1 := by
        change -(1 : ZMod 2) = 1
        exact ZMod.neg_eq_self_mod_two 1
      have hseries (F : PowerSeries (ZMod 2)) : -F = F := by
        ext n
        simp only [map_neg]
        exact ZMod.neg_eq_self_mod_two _
      simp only [map_add, map_one, map_mul, map_pow, map_sub,
        PowerSeries.map_X, htwo, zero_mul,
        ← PowerSeries.rescale_map]
      rw [hneg, PowerSeries.rescale_one, RingHom.id_apply, add_zero]
      rw [sub_eq_add_neg, hseries]

private lemma square_eq_expand (B : PowerSeries (ZMod 2)) :
    B ^ 2 = PowerSeries.expand 2 (by norm_num) B := by
  symm
  simpa [PowerSeries.expand, PowerSeries.map, ZMod.frobenius_zmod] using
    (MvPowerSeries.map_frobenius_expand (R := ZMod 2) 2 (by norm_num) (f := B))

private lemma odd_index_power_iff (m : ℕ) :
    (∃ k, m + 1 = 2 ^ k) ↔ ∃ k, (2 * m + 1) + 1 = 2 ^ k := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    rw [pow_succ]
    omega
  · rintro ⟨k, hk⟩
    cases k with
    | zero => simp at hk
    | succ k =>
        refine ⟨k, ?_⟩
        rw [pow_succ] at hk
        omega

private lemma even_positive_index_not_power (m : ℕ) :
    ¬ ∃ k, (2 * m + 2) + 1 = 2 ^ k := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => simp at hk
  | succ k =>
      rw [pow_succ] at hk
      omega

private lemma coeff_modTwo_support {A : PowerSeries ℤ} (hA : SatisfiesEquation A) :
    ∀ n, PowerSeries.coeff n (modTwo A) = 1 ↔ ∃ k, n + 1 = 2 ^ k := by
  have hB : modTwo A =
      1 + X * PowerSeries.expand 2 (by norm_num) (modTwo A) := by
    calc
      modTwo A = 1 + X * (modTwo A) ^ 2 := modTwo_equation hA
      _ = 1 + X * PowerSeries.expand 2 (by norm_num) (modTwo A) := by
        rw [square_eq_expand]
  have hcoeff (n : ℕ) :
      PowerSeries.coeff (n + 1) (modTwo A) =
        if 2 ∣ n then PowerSeries.coeff (n / 2) (modTwo A) else 0 := by
    have hc := congrArg (PowerSeries.coeff (n + 1)) hB
    simpa [PowerSeries.coeff_expand] using hc
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          have hc := congrArg (PowerSeries.coeff 0) hB
          have hb0 : PowerSeries.coeff 0 (modTwo A) = 1 := by
            simpa using hc
          constructor
          · intro _
            exact ⟨0, by simp⟩
          · intro _
            exact hb0
      | succ n =>
          by_cases heven : 2 ∣ n
          · obtain ⟨m, rfl⟩ := heven
            rw [hcoeff]
            simp only [dvd_mul_right, if_true]
            have hdiv : 2 * m / 2 = m := by omega
            rw [hdiv]
            rw [ih m (by omega)]
            exact odd_index_power_iff m
          · obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 1 := by
              use n / 2
              omega
            subst n
            rw [hcoeff]
            have hnot : ¬ 2 ∣ 2 * m + 1 := by omega
            simp [hnot, even_positive_index_not_power m]

/-- **OEIS A368633 parity conjecture.**  Every integer coefficient sequence
satisfying the source generating-function equation has an odd coefficient at
index `n` exactly when `n + 1` is a power of two. -/
theorem parity_conjecture {A : PowerSeries ℤ} (hA : SatisfiesEquation A) (n : ℕ) :
    Odd (PowerSeries.coeff n A) ↔ ∃ k, n + 1 = 2 ^ k := by
  rw [← ZMod.intCast_eq_one_iff_odd]
  simpa [modTwo] using coeff_modTwo_support hA n

end AgenticConjectures.OeisA368633
