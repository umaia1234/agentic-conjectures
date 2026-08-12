import Mathlib

/-!
# OEIS A112970 — power-of-two identities for a generalized Stern sequence

The definition and three equality statements below match the upstream Formal
Conjectures snapshot
`problems/oeis-a112970/upstream/112970_93dc5e41.lean`, modulo namespace and
benchmark attributes.  The additional theorem `power_of_two_eq_a033638`
formalizes the quarter-square clause present in OEIS but omitted by that
snapshot.  They use the OEIS recurrence

* `a(0) = a(1) = 1`;
* `a(2n+1) = a(n)`;
* `a(2n) = a(n) + a(n-2)`, with negative arguments interpreted as zero.

Faithfulness details: OEIS has offset `0`; the upstream model represents the
integer-side convention `a(n)=0` for `n≤-1` by a guarded natural subtraction
in the even branch.  The proof uses that guard at the `a(-1)=0` boundary, so
the guarded model is essential rather than an irrelevant subtraction choice.
-/

namespace AgenticConjectures.OeisA112970

/-- The upstream natural-number model of OEIS A112970. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else if n = 1 then 1
  else
    let k := n / 2
    if n % 2 = 1 then
      a k
    else
      let aPrev : ℕ := if k < 2 then 0 else a (k - 2)
      a k + aPrev
termination_by n

@[simp] theorem a_zero : a 0 = 1 := by
  rw [a]
  simp

@[simp] theorem a_one : a 1 = 1 := by
  rw [a]
  simp

@[simp] theorem a_two : a 2 = 1 := by
  rw [a]
  norm_num

/-- The defining odd-index recurrence, including its `k=0` boundary case. -/
theorem a_odd (k : ℕ) : a (2 * k + 1) = a k := by
  by_cases hk : k = 0
  · subst k
    simp only [Nat.mul_zero, Nat.zero_add, a_one, a_zero]
  · have hdiv : (2 * k + 1) / 2 = k := by omega
    rw [a]
    simp [hk, hdiv]

/-- The defining even-index recurrence, with the negative-index convention
implemented by the guard at `k < 2`. -/
theorem a_even (k : ℕ) :
    a (2 * k) = a k + if k < 2 then 0 else a (k - 2) := by
  by_cases h0 : k = 0
  · subst k
    rfl
  by_cases h1 : k = 1
  · subst k
    rw [a]
    simp
  · rw [a]
    simp [h0, h1]

/-- The first OEIS conjecture: `a(2^n) = a(2^(n+1)+1)`. -/
theorem conjecture1 (n : ℕ) : a (2 ^ n) = a (2 ^ (n + 1) + 1) := by
  simpa [pow_succ, Nat.mul_comm] using (a_odd (2 ^ n)).symm

/-- The common value in the second OEIS conjecture is one at `2^n-1`. -/
theorem conjecture3 (n : ℕ) : a (2 ^ n - 1) = 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
      have hindex : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
        rw [pow_succ]
        omega
      rw [hindex, a_odd, ih]

/-- The companion family `a(3*2^n-1)` also has constant value one. -/
theorem three_mul_pow_sub_one (n : ℕ) : a (3 * 2 ^ n - 1) = 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
      have hindex : 3 * 2 ^ (n + 1) - 1 = 2 * (3 * 2 ^ n - 1) + 1 := by
        rw [pow_succ]
        omega
      rw [hindex, a_odd, ih]

/-- The second OEIS conjecture: `a(2^n-1) = a(3*2^n-1)`. -/
theorem conjecture2 (n : ℕ) : a (2 ^ n - 1) = a (3 * 2 ^ n - 1) := by
  rw [conjecture3, three_mul_pow_sub_one]

/-- Every two steps, the auxiliary values at `2^n-2` increase by one. -/
theorem shifted_power_recurrence (n : ℕ) :
    a (2 ^ (n + 3) - 2) = a (2 ^ (n + 1) - 2) + 1 := by
  have hp : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  have hp2 : 2 ≤ 2 ^ (n + 1) := by
    rw [pow_succ]
    omega
  have hp4 : 4 ≤ 2 ^ (n + 2) := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    omega
  have heven : 2 ^ (n + 3) - 2 = 2 * (2 ^ (n + 2) - 1) := by
    rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
    omega
  have hodd : (2 ^ (n + 2) - 1) - 2 = 2 * (2 ^ (n + 1) - 2) + 1 := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    omega
  have hk : ¬(2 ^ (n + 2) - 1 < 2) := by omega
  rw [heven, a_even, if_neg hk, conjecture3, hodd, a_odd]
  omega

/-- Closed form for the auxiliary values used by the even recurrence. -/
theorem shifted_power_formula (n : ℕ) :
    a (2 ^ (n + 1) - 2) = (n + 2) / 2 := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n ih0 _ =>
      rw [show n + 2 + 1 = n + 3 by omega, shifted_power_recurrence, ih0]
      omega

private theorem quarter_square_succ (n : ℕ) :
    (n + 1) ^ 2 / 4 = n ^ 2 / 4 + (n + 1) / 2 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · ring_nf
    omega
  · ring_nf
    omega

/-- The missing clause of the OEIS conjecture: the power-of-two values are
the quarter-square sequence A033638. -/
theorem power_of_two_eq_a033638 (n : ℕ) :
    a (2 ^ n) = n ^ 2 / 4 + 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [show 2 ^ (n + 1) = 2 * 2 ^ n by
        rw [pow_succ]
        omega, a_even]
      rcases n with _ | m
      · norm_num
      · have hp : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by omega)
        have hge : 2 ≤ 2 ^ (m + 1) := by
          rw [pow_succ]
          omega
        rw [if_neg (Nat.not_lt_of_ge hge), shifted_power_formula, ih]
        have hsquare := quarter_square_succ (m + 1)
        omega

end AgenticConjectures.OeisA112970
