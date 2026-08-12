import Mathlib

/-!
# OEIS A067720 — excluding the power-of-two subfamily

The pinned upstream snapshot
`problems/oeis-a067720/upstream/67720.lean` defines membership in A067720 by

`Nat.totient (k ^ 2 + 1) = k * Nat.totient (k + 1)`

and conjectures that every member other than `8` has `k + 1` prime. The
definition below copies that proposition exactly. We prove that no member can
satisfy `k + 1 = 2 ^ a` when `a >= 2`.

Faithfulness: the theorem uses natural-number exponentiation exactly as the
upstream statement does. Its `2 <= a` hypothesis excludes the prime boundary
case `a = 1`; no claim is made about odd prime powers, general composite values
of `k + 1`, or the upstream universal conjecture.
-/

namespace AgenticConjectures.OeisA067720

/-- A number `k` belongs to OEIS A067720. This is the exact proposition used
by the pinned FormalConjectures statement. -/
def A (k : ℕ) : Prop :=
  Nat.totient (k ^ 2 + 1) = k * Nat.totient (k + 1)

/-- No A067720 member has `k + 1 = 2 ^ a` for an exponent `a >= 2`. -/
theorem power_two_add_one_not_solution {k a : ℕ} (ha : 2 ≤ a)
    (hk : k + 1 = 2 ^ a) : ¬ A k := by
  intro hA
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le ha
  let c : ℕ := 2 ^ b
  have hcpos : 0 < c := by simp [c]
  have hk4 : k + 1 = 4 * c := by rw [hk, hb]; simp [c, pow_add]
  let t : ℕ := 2 * c - 1
  have htpos : 0 < t := by dsimp [t]; omega
  have hkt : k = 2 * t + 1 := by dsimp [t]; omega
  let N : ℕ := 2 * t ^ 2 + 2 * t + 1
  have hfac : k ^ 2 + 1 = 2 * N := by rw [hkt]; dsimp [N]; ring
  have hNodd : Odd N := by
    refine ⟨t ^ 2 + t, ?_⟩
    dsimp [N]
    ring
  have ha0 : 0 < a := by omega
  have htotpow : Nat.totient (2 ^ a) = 2 ^ (a - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two ha0]
    simp
  have hpowsucc : 2 ^ a = 2 * 2 ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
    ring
  have ht_pow : t + 1 = 2 ^ (a - 1) := by
    rw [hkt, hpowsucc] at hk
    omega
  unfold A at hA
  rw [hfac, Nat.totient_two_mul_of_odd hNodd, hk, htotpow] at hA
  have hle : Nat.totient N ≤ N := Nat.totient_le N
  have hstrict : N < k * 2 ^ (a - 1) := by
    rw [hkt, ← ht_pow]
    dsimp [N]
    nlinarith
  have hcontra := lt_of_le_of_lt hle hstrict
  exact hcontra.ne hA

end AgenticConjectures.OeisA067720
