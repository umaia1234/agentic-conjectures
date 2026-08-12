import Mathlib

/-!
# OEIS A396093 — parity of the third iterate of `x / (1 - x)^2`

OEIS A396093 is the coefficient sequence of

`A(x) = B(B(B(x)))`, where `B(x) = x / (1 - x)^2`.

The entry gives initial values `a(0), ..., a(7)` and the order-eight recurrence

`a(n) = 14 a(n-1) - 75 a(n-2) + 196 a(n-3) - 269 a(n-4)
        + 196 a(n-5) - 75 a(n-6) + 14 a(n-7) - a(n-8)`.

The definition below is exactly that recurrence, indexed from zero and evaluated
over `ℤ` so subtraction has its ordinary meaning.  Modulo two it becomes

`a(n+8) = a(n+6) + a(n+4) + a(n+2) + a(n)`.

Applying this identity at `n` and `n+2` shows that parity has period ten.  The
first ten terms then give the complete classification

`Even (a n) ↔ Even n ∨ n % 10 = 5`,

from which both parity conjectures printed on the OEIS entry follow.

Faithfulness notes: OEIS has offset 0, and `a(0) = 0` is included below.  The
first conjecture begins at `n = 1`, although the stronger theorem here includes
`n = 0`.  In the second conjecture, natural-number subtraction in `2*n - 1`
and `5*k - 2` is harmless because the quantified hypotheses require `n,k ≥ 1`.
-/

namespace AgenticConjectures.OeisA396093

/-- OEIS A396093, defined by its published initial values and order-eight
recurrence. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 33
  | 4 => 174
  | 5 => 892
  | 6 => 4480
  | 7 => 22149
  | n + 8 =>
      14 * a (n + 7) - 75 * a (n + 6) + 196 * a (n + 5) -
        269 * a (n + 4) + 196 * a (n + 3) - 75 * a (n + 2) +
        14 * a (n + 1) - a n

/-- The published recurrence reduced modulo two. -/
lemma mod_two_recurrence (n : ℕ) :
    a (n + 8) % 2 = (a (n + 6) + a (n + 4) + a (n + 2) + a n) % 2 := by
  rw [a]
  omega

/-- The parity of A396093 has period ten. -/
lemma mod_two_period_ten (n : ℕ) : a (n + 10) % 2 = a n % 2 := by
  have h0 := mod_two_recurrence n
  have h2 := mod_two_recurrence (n + 2)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h2
  omega

private lemma even_period_ten (n : ℕ) : Even (a (n + 10)) ↔ Even (a n) := by
  simp only [Int.even_iff, mod_two_period_ten]

/-- Complete parity classification: even positions are even, while the only
odd positions with even values are those congruent to 5 modulo 10. -/
theorem even_a_iff (n : ℕ) : Even (a n) ↔ Even n ∨ n % 10 = 5 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 10
      · interval_cases n <;> norm_num [a, Nat.even_iff]
      · have hn10 : 10 ≤ n := by omega
        have hlt : n - 10 < n := by omega
        rw [show n = (n - 10) + 10 by omega, even_period_ten, ih (n - 10) hlt]
        simp only [Nat.even_iff]
        omega

/-- First A396093 conjecture: every even-indexed term is even.  This is
slightly stronger than the OEIS wording, which assumes `n ≥ 1`. -/
theorem even_index_even (n : ℕ) : Even (a (2 * n)) := by
  rw [even_a_iff]
  exact Or.inl ⟨n, by omega⟩

/-- Second A396093 conjecture, with the source's quantifiers and
natural-number indexing: `a(2n-1)` is even exactly when `n = 5k-2` for some
`k ≥ 1`. -/
theorem odd_index_even_iff (n : ℕ) (hn : 1 ≤ n) :
    Even (a (2 * n - 1)) ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 5 * k - 2 := by
  rw [even_a_iff]
  have hodd : ¬ Even (2 * n - 1) := by
    rw [Nat.not_even_iff_odd]
    exact ⟨n - 1, by omega⟩
  simp only [hodd, false_or]
  constructor
  · intro hmod
    refine ⟨(2 * n - 1) / 10 + 1, by omega, ?_⟩
    have hdiv := Nat.mod_add_div (2 * n - 1) 10
    omega
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have heq : 2 * (5 * (j + 1) - 2) - 1 = 10 * j + 5 := by omega
    rw [heq]
    omega

end AgenticConjectures.OeisA396093
