import Mathlib

/-
The proof architecture is adapted from the fixed-parameter `m = 8` proof in
AlphaProof Nexus, copyright 2026 Google LLC and licensed under Apache-2.0:
https://github.com/google-deepmind/alphaproof-nexus-results/blob/42f344cfa9d57154f36e6b9bef1f71760a438c54/APNOutputs/OEIS/oeis_113254_conjecture_0.lean

This file modifies that architecture by retaining `m` symbolically, deriving
the polynomial recurrence for general `m`, and proving the full family.
-/

/-!
# OEIS A113249 — odd-indexed terms in the full parameter family are squares

OEIS A113249 records the fourth-order family

`a(m,n) = m^4 * a(m,n-4) + (2*m)^2 * a(m,n-3) - 4 * a(m,n-1)`

with initial values

`a(m,0) = -1`, `a(m,1) = 4`,
`a(m,2) = -13 + 6*(m-1) + 3*(m-1)^2`, and
`a(m,3) = (-8+m^2)^2`.

Its comment conjectures that `a(m,2*n+1)` is a perfect square for all
parameters `m` and indices `n`. This module proves the stronger identity

`a(m,2*n+1) = Y(m,n)^2`

for every integer `m`, where `Y(m,0)=2`, `Y(m,1)=8-m^2`, and
`Y(m,n+2)=4*Y(m,n+1)-m^2*Y(m,n)`.

The canonical source is OEIS A113249, revision 29 (2023-08-18), checked on
2026-08-12. There is no Formal Conjectures Lean snapshot for the general
parameter claim. A public AlphaProof Nexus proof for the special case `m=8`
(linked from OEIS A113254) uses the same auxiliary-recurrence strategy; the
proof here carries the parameter symbolically and proves the full family.

Faithfulness notes:
- The sequence has integer values, including negative even-indexed terms, so
  both the parameter and values are represented in `ℤ`.
- The OEIS examples use nonnegative integer parameters but the conjecture does
  not explicitly declare a domain. The registered `statement` gives the
  natural-parameter interpretation by quantifying over `m n : ℕ` and casting
  `m` to `ℤ`; the main identity is stronger because it holds for every
  `m : ℤ`.
- The definition below copies the four initial values and the shifted
  recurrence exactly. Its `n+4` clause is the source recurrence at index
  `n+4`; no natural-number subtraction is used.
- `IsSquare` is witnessed in `ℤ`, which is the ordinary meaning of a perfect
  square for this integer sequence.
- No novelty is claimed. The fixed case `m=3` has an OEIS formula due to
  Robert Israel, and the fixed case `m=8` already has the cited Lean proof.
-/

namespace AgenticConjectures.OeisA113249

/-- The exact fourth-order parameter family from OEIS A113249, shifted to a
forward recursive clause at index `n+4`. -/
def a (m : ℤ) : ℕ → ℤ
  | 0 => -1
  | 1 => 4
  | 2 => -13 + 6 * (m - 1) + 3 * (m - 1) ^ 2
  | 3 => (-8 + m ^ 2) ^ 2
  | n + 4 => m ^ 4 * a m n + (2 * m) ^ 2 * a m (n + 1) - 4 * a m (n + 3)

/-- The second-order auxiliary sequence whose squares are the odd terms of
the fourth-order family. -/
def Y (m : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => 8 - m ^ 2
  | n + 2 => 4 * Y m (n + 1) - m ^ 2 * Y m n

private lemma Y_add_two (m : ℤ) (n : ℕ) :
    Y m (n + 2) = 4 * Y m (n + 1) - m ^ 2 * Y m n := rfl

private lemma square_recurrence_identity (m A B : ℤ) :
    (4 * (4 * A - m ^ 2 * B) - m ^ 2 * A) ^ 2 =
      (16 - m ^ 2) * (4 * A - m ^ 2 * B) ^ 2
        + m ^ 2 * (m ^ 2 - 16) * A ^ 2 + m ^ 6 * B ^ 2 := by
  ring

private lemma Y_sq_step (m : ℤ) (n : ℕ) :
    Y m (n + 3) ^ 2 =
      (16 - m ^ 2) * Y m (n + 2) ^ 2
        + m ^ 2 * (m ^ 2 - 16) * Y m (n + 1) ^ 2 + m ^ 6 * Y m n ^ 2 := by
  rw [Y_add_two m (n + 1), Y_add_two m n]
  exact square_recurrence_identity m (Y m (n + 1)) (Y m n)

private lemma a_add_four (m : ℤ) (k : ℕ) :
    a m (k + 4) = m ^ 4 * a m k + 4 * m ^ 2 * a m (k + 1) - 4 * a m (k + 3) := by
  rw [a]
  ring

private lemma a_rec_zero (m : ℤ) (k : ℕ) :
    a m (k + 4) + 4 * a m (k + 3) - 4 * m ^ 2 * a m (k + 1) - m ^ 4 * a m k = 0 := by
  have h := a_add_four m k
  linear_combination h

/-- Eliminating the two unused residue classes from the fourth-order
recurrence gives a third-order recurrence with step size two. -/
private lemma a_step_six (m : ℤ) (k : ℕ) :
    a m (k + 6) =
      (16 - m ^ 2) * a m (k + 4)
        + m ^ 2 * (m ^ 2 - 16) * a m (k + 2) + m ^ 6 * a m k := by
  have h1 := a_rec_zero m (k + 2)
  have h2 := a_rec_zero m (k + 1)
  have h3 := a_rec_zero m k
  linear_combination h1 - 4 * h2 + m ^ 2 * h3

private lemma a_step_odd (m : ℤ) (n : ℕ) :
    a m (2 * n + 7) =
      (16 - m ^ 2) * a m (2 * n + 5)
        + m ^ 2 * (m ^ 2 - 16) * a m (2 * n + 3) + m ^ 6 * a m (2 * n + 1) := by
  simpa only [show 2 * n + 1 + 6 = 2 * n + 7 by omega,
    show 2 * n + 1 + 4 = 2 * n + 5 by omega,
    show 2 * n + 1 + 2 = 2 * n + 3 by omega] using a_step_six m (2 * n + 1)

private lemma a_eq_Y_sq_window (m : ℤ) (n : ℕ) :
    a m (2 * n + 1) = Y m n ^ 2 ∧
      a m (2 * n + 3) = Y m (n + 1) ^ 2 ∧
        a m (2 * n + 5) = Y m (n + 2) ^ 2 := by
  induction n with
  | zero =>
      constructor
      · norm_num [a, Y]
      constructor
      · simp [a, Y]
        ring
      · simp [a, Y]
        ring
  | succ n ih =>
      rcases ih with ⟨ih1, ih2, ih3⟩
      have ha := a_step_odd m n
      have hy := Y_sq_step m n
      rw [ih1, ih2, ih3] at ha
      constructor
      · simpa only [Nat.succ_eq_add_one] using ih2
      constructor
      · simpa only [Nat.succ_eq_add_one] using ih3
      · rw [show 2 * (n + 1) + 5 = 2 * n + 7 by omega, ha]
        exact hy.symm

/-- Strong closed form for the odd subsequence: every odd term is the square
of the corresponding auxiliary-recurrence term, for every integer parameter. -/
theorem odd_term_eq_aux_square (m : ℤ) (n : ℕ) :
    a m (2 * n + 1) = Y m n ^ 2 :=
  (a_eq_Y_sq_window m n).1

/-- The natural-parameter interpretation of the OEIS conjecture. -/
def statement : Prop :=
  ∀ m n : ℕ, IsSquare (a (m : ℤ) (2 * n + 1))

/-- **OEIS A113249 general-family square conjecture, under its natural-parameter
interpretation.** Every odd-indexed term is a perfect square. -/
theorem oeis_a113249_conjecture : statement := by
  intro m n
  rw [odd_term_eq_aux_square]
  exact ⟨Y m n, by ring⟩

end AgenticConjectures.OeisA113249
