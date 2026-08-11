import Mathlib

/-!
# OEIS A136433 — the conjectured order-9 linear recurrence, proved

OEIS A136433 (offset 1) is defined by `a(1) = 11` and, for `n ≥ 0`,
`a(n+2) = ((n mod 3) + 1) · a(n+1) + ((n mod 2) + 1)`.
The OEIS entry conjectures the constant-coefficient recurrence
`a(n) = 6·a(n-3) + a(n-6) - 6·a(n-9)` for all `n ≥ 10`.

This module proves that conjecture. It follows the informal proof in
`problems/oeis-a136433/PROOF.md` (three-step transition `a(t+3) = 6·a(t) + B(t)`
with `B` of period 6), though here the statement is closed directly by a case
split on `t mod 6` after full unfolding.

Faithfulness notes (there is no upstream Lean snapshot for this entry):
- `a 0` is a junk value (`0`) never referenced by the claim — the OEIS sequence
  starts at `a(1) = 11`. The recurrence defining `a (n+2)` uses the same index
  base `n ≥ 0` as the OEIS definition, giving `a(2) = 12, a(3) = 26, a(4) = 79, …`.
- The OEIS claim contains a subtraction, so the headline statement is cast to
  `ℤ`; `a136433_add_form` is the equivalent subtraction-free form over `ℕ`.
- The range `n ≥ 10` is exactly the OEIS claim (at `n = 9` the right-hand side
  would touch the undefined `a(0)`).
-/

namespace AgenticConjectures.OeisA136433

/-- OEIS A136433, offset 1: `a 1 = 11`,
`a (n+2) = ((n % 3) + 1) * a (n+1) + ((n % 2) + 1)`. `a 0` is unused. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 11
  | n + 2 => (n % 3 + 1) * a (n + 1) + (n % 2 + 1)

/-- Subtraction-free form over `ℕ`: `t + 10` ranges over exactly all `n ≥ 10`. -/
theorem a136433_add_form (t : ℕ) :
    a (t + 10) + 6 * a (t + 1) = 6 * a (t + 7) + a (t + 4) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 6 ∧ t = 6 * q + r :=
    ⟨t / 6, t % 6, by omega, by omega⟩
  interval_cases r <;> simp [a, Nat.add_mod, Nat.mul_mod] <;> ring_nf

/-- **The A136433 recurrence conjecture**: for all `n ≥ 10`,
`a(n) = 6·a(n-3) + a(n-6) - 6·a(n-9)` (over `ℤ`, matching the OEIS phrasing). -/
theorem a136433_order9 (n : ℕ) (hn : 10 ≤ n) :
    (a n : ℤ) = 6 * a (n - 3) + a (n - 6) - 6 * a (n - 9) := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 10 := ⟨n - 10, by omega⟩
  have h := a136433_add_form t
  have e3 : t + 10 - 3 = t + 7 := by omega
  have e6 : t + 10 - 6 = t + 4 := by omega
  have e9 : t + 10 - 9 = t + 1 := by omega
  rw [e3, e6, e9]
  omega

end AgenticConjectures.OeisA136433
