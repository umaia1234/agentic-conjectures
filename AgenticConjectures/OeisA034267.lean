import Mathlib

/-!
# OEIS A034267 — the conjectured D-finite recurrence, proved

OEIS A034267 (offset 0) is the diagonal `f(n,n)` of OEIS A034261, where

`f(m,k) = binomial(m+k,k+1) * (m*k+m+1) / (k+2)`.

Its Formula section conjectures

`-(n+2)(11n-7)a(n) + 2(23n^2+44n+30)a(n-1)
  - 4(n+5)(2n-3)a(n-2) = 0`.

This module proves the recurrence for every meaningful index `n >= 2`. The
canonical source is OEIS A034267, revision 23 (2025-09-04), checked on
2026-08-12. There is no upstream Lean snapshot for this entry.

Faithfulness notes:
- `f` is the exact two-variable formula on A034261, and `a_eq_f_diag` proves
  that the closed form used below is its diagonal.
- The OEIS formula uses exact division. We therefore work in `ℚ`, rather than
  introduce natural-number division; this module does not separately prove
  that every displayed value is integral. Equality in `ℚ` is sufficient for
  the proposed recurrence.
- The OEIS recurrence omits its range. Since its offset is 0 and it references
  `a(n-2)`, `n >= 2` is the conventional minimal range. The hypothesis also
  makes Lean's natural-index subtractions `n-1` and `n-2` faithful.
- Coefficient subtraction, in particular `2n-3`, is performed in `ℚ` and is
  not truncated natural subtraction.
- At the boundary `n=2`, the identity is checked directly. For `n>=3`, the
  proof expands the three binomial coefficients as factorial quotients,
  clears nonzero denominators, and closes the resulting polynomial identity.
-/

namespace AgenticConjectures.OeisA034267

open Nat

/-- The two-variable formula defining OEIS A034261, interpreted with exact
division in `ℚ`. OEIS A034267 is its diagonal. -/
def f (m k : ℕ) : ℚ :=
  (Nat.choose (m + k) (k + 1) : ℚ) *
    (((m : ℚ) * k + m + 1) / (k + 2))

/-- The closed formula displayed on OEIS A034267. -/
def a (n : ℕ) : ℚ :=
  (Nat.choose (2 * n) (n + 1) : ℚ) *
    (((n : ℚ) ^ 2 + n + 1) / (n + 2))

/-- The displayed closed formula is exactly the diagonal of the source's
two-variable definition. -/
theorem a_eq_f_diag (n : ℕ) : a n = f n n := by
  simp [a, f, two_mul, pow_two]

/-- The OEIS recurrence statement on its minimal meaningful range. -/
def statement : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    -((n : ℚ) + 2) * (11 * n - 7) * a n
      + 2 * (23 * (n : ℚ) ^ 2 + 44 * n + 30) * a (n - 1)
      - 4 * ((n : ℚ) + 5) * (2 * n - 3) * a (n - 2) = 0

/-- **The A034267 D-finite recurrence conjecture**: the OEIS closed form
satisfies the proposed order-2 polynomial recurrence for every `n >= 2`. -/
theorem a034267_recurrence : statement := by
  intro n hn
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 2 := ⟨n - 2, by omega⟩
  rcases t with _ | t
  · norm_num [a, Nat.choose]
  simp only [show t + 1 + 2 = t + 3 by omega,
    show t + 3 - 1 = t + 2 by omega,
    show t + 3 - 2 = t + 1 by omega]
  have h1 : t + 1 + 1 ≤ 2 * (t + 1) := by omega
  have h2 : t + 2 + 1 ≤ 2 * (t + 2) := by omega
  have h3 : t + 3 + 1 ≤ 2 * (t + 3) := by omega
  simp only [a]
  rw [Nat.cast_choose (K := ℚ) h1, Nat.cast_choose (K := ℚ) h2,
    Nat.cast_choose (K := ℚ) h3]
  simp only [show 2 * (t + 1) - (t + 1 + 1) = t by omega,
    show 2 * (t + 2) - (t + 2 + 1) = t + 1 by omega,
    show 2 * (t + 3) - (t + 3 + 1) = t + 2 by omega]
  simp only [show 2 * (t + 1) = 2 * t + 2 by omega,
    show 2 * (t + 2) = 2 * t + 4 by omega,
    show 2 * (t + 3) = 2 * t + 6 by omega]
  rw [show (2 * t + 6)! = (2 * t + 6) * (2 * t + 5) * (2 * t + 4) *
      (2 * t + 3) * (2 * t + 2)! by
      simp only [show 2 * t + 6 = (2 * t + 5) + 1 by omega,
        show 2 * t + 5 = (2 * t + 4) + 1 by omega,
        show 2 * t + 4 = (2 * t + 3) + 1 by omega,
        show 2 * t + 3 = (2 * t + 2) + 1 by omega,
        Nat.factorial_succ]
      ring]
  rw [show (2 * t + 4)! = (2 * t + 4) * (2 * t + 3) * (2 * t + 2)! by
      simp only [show 2 * t + 4 = (2 * t + 3) + 1 by omega,
        show 2 * t + 3 = (2 * t + 2) + 1 by omega,
        Nat.factorial_succ]
      ring]
  rw [show (t + 4)! = (t + 4) * (t + 3) * (t + 2)! by
      simp only [show t + 4 = (t + 3) + 1 by omega,
        show t + 3 = (t + 2) + 1 by omega,
        Nat.factorial_succ]
      ring]
  rw [show (t + 3)! = (t + 3) * (t + 2)! by
      simp only [show t + 3 = (t + 2) + 1 by omega, Nat.factorial_succ]]
  rw [show (t + 2)! = (t + 2) * (t + 1) * Nat.factorial t by
      simp only [show t + 2 = (t + 1) + 1 by omega, Nat.factorial_succ]
      ring]
  rw [show (t + 1)! = (t + 1) * Nat.factorial t by
      simp only [Nat.factorial_succ]]
  push_cast
  field_simp
  ring

end AgenticConjectures.OeisA034267
