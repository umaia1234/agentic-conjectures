import Mathlib

/-!
# OEIS A384162 — refutation of a conjectured cross-reference

OEIS A384162 defines `a(n)` as the coefficient of `x^n` in

`n*x / (1 - x*(1 - x + n))`

and conjectures `a(n) = n * A342168(n-1)`.  The denominator is
`1 - (n+1)*x + x^2`, so its coefficients satisfy the recurrence encoded by
`a384162Coeff` below.  OEIS A342168 supplies the finite binomial-sum formula
encoded by `A342168`.

We prove the negation of the conjecture at `n = 2`: the left side is `6`,
whereas `2 * A342168(1) = 2 * 4 = 8`.

Faithfulness notes: A384162 has offset 1 and A342168 has offset 0, so the
subscript `n - 1` is literal and is not an indexing conversion.  The A384162
coefficient recurrence is over `ℤ`, avoiding natural-number truncation; the
A342168 formula is over `ℕ`, exactly as published.  This module formalizes the
published generating-function and binomial-sum formulas.  The independent
certificate in `problems/oeis-a384162/a384162_certificate.py` instead enumerates
the marked words and evaluates the Chebyshev definition.
-/

namespace AgenticConjectures.OeisA384162

open Finset

/-- Coefficients of `m*x / (1 - (m+1)*x + x^2)` over the integers. -/
def a384162Coeff (m : ℕ) : ℕ → ℤ
  | 0 => 0
  | 1 => m
  | k + 2 => (m + 1 : ℕ) * a384162Coeff m (k + 1) - a384162Coeff m k

/-- OEIS A384162 via its published rational generating function. -/
def A384162 (n : ℕ) : ℤ := a384162Coeff n n

/-- OEIS A342168 via its published finite binomial-sum formula. -/
def A342168 (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), (n + 1) ^ (n - k) * Nat.choose (2 * n + 1 - k) k

/-- The exact conjectured cross-reference on OEIS A384162. -/
def statement : Prop :=
  ∀ n : ℕ, 0 < n → A384162 n = (n * A342168 (n - 1) : ℕ)

theorem a384162_two : A384162 2 = 6 := by
  norm_num [A384162, a384162Coeff]

theorem a342168_one : A342168 1 = 4 := by
  norm_num [A342168, Finset.sum_range_succ]

/-- The conjecture is false at `n = 2`: `6 ≠ 2 * 4`. -/
theorem oeis_a384162_conjecture_false : ¬ statement := by
  intro h
  have h2 := h 2 (by norm_num)
  rw [a384162_two, a342168_one] at h2
  norm_num at h2

end AgenticConjectures.OeisA384162
