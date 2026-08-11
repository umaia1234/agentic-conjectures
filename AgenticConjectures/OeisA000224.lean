import Mathlib

/-!
# OEIS A000224 — the even-input exclusion

The definition below matches the pinned upstream snapshot
`problems/oeis-a000224/upstream/224_2322a58c.lean`: it counts distinct squares
modulo `n`, including zero. The upstream conjecture says, for `n > 1`, that
`(n * n) ≡ 1` modulo `A000224 n * (A000224 n - 1)` exactly when `n` is an odd
prime. We prove the negative congruence direction for every even `n > 1`.

Faithfulness: the `n = 0` convention, natural-number subtraction, and
`Nat.ModEq` statement are copied exactly; the theorem's `1 < n` hypothesis
excludes the boundary values from the upstream conjecture.
-/

namespace AgenticConjectures.OeisA000224

open Finset

/-- OEIS A000224: the number of distinct quadratic residues modulo `n`,
including zero. This is copied from the pinned upstream statement. -/
noncomputable def A000224 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else Finset.card ((Finset.range n).image (fun k : ℕ => k ^ 2 % n))

/-- No even `n > 1` satisfies the congruence side of the A000224 conjecture. -/
theorem even_not_conjecture_rhs {n : ℕ} (_hn : 1 < n) (heven : Even n) :
    ¬ (n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)] := by
  intro hmod
  have hd : 2 ∣ A000224 n * (A000224 n - 1) := Nat.two_dvd_mul_sub_one _
  have hmod2 : (n * n) ≡ 1 [MOD 2] := hmod.of_dvd hd
  have hnmod : n % 2 = 0 := Nat.mod_eq_zero_of_dvd heven.two_dvd
  have hsqmod : (n * n) % 2 = 0 := by simp [Nat.mul_mod, hnmod]
  change (n * n) % 2 = 1 % 2 at hmod2
  rw [hsqmod] at hmod2
  norm_num at hmod2

end AgenticConjectures.OeisA000224
