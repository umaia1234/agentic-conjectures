import Mathlib

/-!
# OEIS A397588: parity of a quadratic recurrence

The canonical source is <https://oeis.org/A397588>.  It defines the generating
function `A(x) = ∑_{n≥1} a(n)x^n` by

`A(x) = x + (x A(x)^2)'`

and records the equivalent coefficient recurrence

`a(1) = 1`,
`a(n) = (n+1) ∑_{k=1}^{n-1} a(k)a(n-k)` for `n > 1`.

The OEIS conjecture says that `a(n)` is odd exactly when `n` is a power of
two.  We formalize the displayed coefficient recurrence directly, for an
arbitrary natural-valued sequence satisfying it.  Thus there is no issue of
formal-power-series differentiation or indexing beyond the explicit
restriction `n ≥ 1`; the source has no `a(0)` term and neither does the
formal statement.
-/

namespace AgenticConjectures.OeisA397588

open scoped BigOperators

/-- The coefficient recurrence displayed in OEIS A397588. -/
def SatisfiesRecurrence (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧
    ∀ n, 1 < n →
      a n = (n + 1) * ∑ k ∈ Finset.Icc 1 (n - 1), a k * a (n - k)

/-- The OEIS A397588 parity conjecture, stated for every sequence satisfying
its displayed recurrence. -/
def statement : Prop :=
  ∀ (a : ℕ → ℕ), SatisfiesRecurrence a →
    ∀ n, 0 < n → (Odd (a n) ↔ ∃ m : ℕ, n = 2 ^ m)

/-- Being a nonnegative integral power of two. -/
def IsTwoPower (n : ℕ) : Prop := ∃ k : ℕ, n = 2 ^ k

private lemma isTwoPower_two_mul (m : ℕ) : IsTwoPower (2 * m) ↔ IsTwoPower m := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => simp at hk
    | succ k =>
        refine ⟨k, ?_⟩
        simp only [pow_succ] at hk
        omega
  · rintro ⟨k, rfl⟩
    refine ⟨k + 1, ?_⟩
    simp [pow_succ, mul_comm]

/-- In characteristic two, the terms of an even-index convolution cancel in
pairs away from the middle term. -/
private lemma convolution_even (f : ℕ → ZMod 2) (m : ℕ) (hm : 0 < m) :
    (∑ k ∈ Finset.Icc 1 (2 * m - 1), f k * f (2 * m - k)) = f m ^ 2 := by
  classical
  let s := (Finset.Icc 1 (2 * m - 1)).erase m
  have hm_mem : m ∈ Finset.Icc 1 (2 * m - 1) := by
    simp only [Finset.mem_Icc]
    omega
  have hcancel : ∑ k ∈ s, f k * f (2 * m - k) = 0 := by
    apply Finset.sum_involution (fun k _ ↦ 2 * m - k)
    · intro k hk
      have hk' : k ∈ Finset.Icc 1 (2 * m - 1) := (Finset.mem_erase.mp hk).2
      simp only [Finset.mem_Icc] at hk'
      have hback : 2 * m - (2 * m - k) = k := by omega
      rw [hback]
      have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
      calc
        f k * f (2 * m - k) + f (2 * m - k) * f k =
            f k * f (2 * m - k) + f k * f (2 * m - k) := by
              rw [mul_comm (f (2 * m - k)) (f k)]
        _ = 2 * (f k * f (2 * m - k)) :=
          (two_mul (f k * f (2 * m - k))).symm
        _ = 0 := by rw [htwo, zero_mul]
    · intro k hk _
      have hk_ne : k ≠ m := (Finset.mem_erase.mp hk).1
      omega
    · intro k hk
      rw [Finset.mem_erase]
      have hkIcc : k ∈ Finset.Icc 1 (2 * m - 1) := (Finset.mem_erase.mp hk).2
      have hk_ne : k ≠ m := (Finset.mem_erase.mp hk).1
      simp only [Finset.mem_Icc] at hkIcc ⊢
      constructor
      · intro h
        omega
      · constructor <;> omega
    · intro k hk
      have hkIcc : k ∈ Finset.Icc 1 (2 * m - 1) := (Finset.mem_erase.mp hk).2
      simp only [Finset.mem_Icc] at hkIcc
      omega
  rw [← Finset.sum_erase_add _ _ hm_mem, hcancel, zero_add]
  rw [show 2 * m - m = m by omega]
  simp [pow_two]

private lemma odd_isTwoPower_iff_one {n : ℕ} (hn : Odd n) : IsTwoPower n ↔ n = 1 := by
  constructor
  · rintro ⟨k, rfl⟩
    cases k with
    | zero => rfl
    | succ k =>
        exfalso
        exact Nat.not_even_iff_odd.mpr hn
          (even_two.pow_of_ne_zero (Nat.succ_ne_zero k))
  · rintro rfl
    exact ⟨0, by simp⟩

private theorem parity_of_recurrence (a : ℕ → ℕ)
    (ha1 : a 1 = 1)
    (hrec : ∀ n, 1 < n →
      a n = (n + 1) * ∑ k ∈ Finset.Icc 1 (n - 1), a k * a (n - k)) :
    ∀ n, 0 < n → (Odd (a n) ↔ IsTwoPower n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hnpos
      rw [← ZMod.natCast_eq_one_iff_odd]
      by_cases hn1 : n = 1
      · subst n
        simp only [ha1, Nat.cast_one]
        constructor
        · intro _
          exact ⟨0, by norm_num⟩
        · intro _
          trivial
      have hn2 : 1 < n := by omega
      have hcast : (a n : ZMod 2) =
          (n + 1 : ℕ) * ∑ k ∈ Finset.Icc 1 (n - 1),
            (a k : ZMod 2) * (a (n - k) : ZMod 2) := by
        rw [hrec n hn2]
        push_cast
        rfl
      obtain hneven | hnodd := Nat.even_or_odd n
      · obtain ⟨m, hm⟩ := hneven
        have hn_eq : n = 2 * m := by omega
        have hmpos : 0 < m := by omega
        have hmlt : m < n := by omega
        have hcoef : ((n + 1 : ℕ) : ZMod 2) = 1 := by
          rw [ZMod.natCast_eq_one_iff_odd]
          rw [hn_eq]
          exact (even_two_mul m).add_one
        rw [hcast, hcoef, one_mul, hn_eq]
        rw [convolution_even (fun k ↦ (a k : ZMod 2)) m hmpos, ZMod.pow_card]
        have ihm : ((a m : ZMod 2) = 1 ↔ IsTwoPower m) := by
          rw [ZMod.natCast_eq_one_iff_odd]
          exact ih m hmlt hmpos
        exact ihm.trans (isTwoPower_two_mul m).symm
      · have hcoef : ((n + 1 : ℕ) : ZMod 2) = 0 := by
          rw [ZMod.natCast_eq_zero_iff_even]
          exact hnodd.add_one
        rw [hcast, hcoef, zero_mul]
        constructor
        · intro h
          norm_num at h
        · intro hp
          have : n = 1 := (odd_isTwoPower_iff_one hnodd).mp hp
          exact (hn1 this).elim

/-- The OEIS A397588 conjecture is true. -/
theorem odd_iff_power_of_two : statement := by
  intro a ha n hn
  exact parity_of_recurrence a ha.1 ha.2 n hn

end AgenticConjectures.OeisA397588
