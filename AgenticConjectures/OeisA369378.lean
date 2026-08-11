import Mathlib

/-!
# OEIS A369378 — the conjectured lower bound, proved

OEIS A369378 defines `a(n)` as the least `k` for which

`2^(2^n + 1) - 1 + 2^k`

is prime (or `-1` if no such `k` exists), and conjectures that for `n > 0`
the displayed number is not prime whenever `k < 2^n`. This module proves
exactly that universal claim.

For positive `k`, write `k = 2^r * q` with `q` odd. The bound on `k` forces
`r < n`. Then the Fermat number `2^(2^r) + 1` is a proper divisor of the
candidate: it divides the `2^k + 1` part because `q` is odd, and it divides
`2^(2^n) - 1` because `2^(n-r)` is even. The case `k = 0` is a power of two.

Faithfulness notes (there is no upstream Lean snapshot for this entry):
- the proposition is the OEIS conjecture quoted in
  `problems/oeis-a369378/README.md`, with `n` and `k` in `ℕ`;
- Lean includes zero among the natural numbers. The entry history originally
  said "natural k", and `k = 0` is covered separately here;
- natural-number subtraction is exact because `2^(2^n + 1) >= 1`;
- the result says nothing about primality for `k >= 2^n` or about whether
  `a(n)` exists.
-/

namespace AgenticConjectures.OeisA369378

/-- The number whose primality is tested in the A369378 conjecture. -/
def candidate (n k : ℕ) : ℕ := 2 ^ (2 ^ n + 1) - 1 + 2 ^ k

/-- The exact lower-bound conjecture displayed on OEIS A369378. -/
def statement : Prop :=
  ∀ n k : ℕ, 0 < n → k < 2 ^ n → ¬Nat.Prime (candidate n k)

/-- **OEIS A369378:** no admissible exponent `k < 2^n` yields a prime. -/
theorem oeis_a369378 : statement := by
  intro n k hn hk
  by_cases hk0 : k = 0
  · subst k
    have hpow : 1 ≤ 2 ^ (2 ^ n + 1) :=
      Nat.one_le_pow (2 ^ n + 1) 2 (by omega)
    rw [candidate, pow_zero, Nat.sub_add_cancel hpow]
    exact Nat.Prime.not_prime_pow (by omega : 2 ≤ 2 ^ n + 1)
  · obtain ⟨r, q, hqodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk0
    have hrn : r < n := by
      by_contra h
      have hpow : 2 ^ n ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) (by omega)
      have hqpos : 0 < q := hqodd.pos
      have : 2 ^ n ≤ 2 ^ r * q := le_trans hpow (Nat.le_mul_of_pos_right _ hqpos)
      omega
    let d := 2 ^ (2 ^ r) + 1
    have hd1 : d ∣ 2 ^ (2 ^ n) - 1 := by
      have hbase : d ∣ (2 ^ (2 ^ r)) ^ (2 ^ (n - r)) - 1 := by
        have hfactor : d ∣ (2 ^ (2 ^ r)) ^ 2 - 1 := by
          refine ⟨2 ^ (2 ^ r) - 1, ?_⟩
          dsimp [d]
          exact Nat.sq_sub_sq (2 ^ (2 ^ r)) 1
        have htwo : 2 ∣ 2 ^ (n - r) := pow_dvd_pow 2 (by omega : 1 ≤ n - r)
        exact hfactor.trans (Nat.pow_sub_one_dvd_pow_sub_one _ htwo)
      have hexp : 2 ^ r * 2 ^ (n - r) = 2 ^ n := by
        rw [← Nat.pow_add]
        congr 1
        omega
      rw [← pow_mul, hexp] at hbase
      exact hbase
    have hd2 : d ∣ 2 ^ (2 ^ r * q) + 1 := by
      simpa [d, pow_mul] using hqodd.nat_add_dvd_pow_add_pow (2 ^ (2 ^ r)) 1
    have hdCandidate : d ∣ candidate n (2 ^ r * q) := by
      obtain ⟨a, ha⟩ := hd1
      obtain ⟨b, hb⟩ := hd2
      refine ⟨2 * a + b, ?_⟩
      calc
        candidate n (2 ^ r * q) =
            2 * (2 ^ (2 ^ n) - 1) + (2 ^ (2 ^ r * q) + 1) := by
              rw [candidate, pow_succ]
              have hA : 1 ≤ 2 ^ (2 ^ n) :=
                Nat.one_le_pow (2 ^ n) 2 (by omega)
              omega
        _ = 2 * (d * a) + d * b := by rw [ha, hb]
        _ = d * (2 * a + b) := by ring
    apply Nat.not_prime_of_dvd_of_lt hdCandidate
    · dsimp [d]
      have hx : 0 < 2 ^ (2 ^ r) := pow_pos (by omega) _
      omega
    · dsimp [d, candidate]
      have hsmall : 2 ^ (2 ^ r) < 2 ^ (2 ^ n) :=
        Nat.pow_lt_pow_right (by omega) (Nat.pow_lt_pow_right (by omega) hrn)
      have hqpos : 0 < q := hqodd.pos
      have hkpos : 0 < 2 ^ r * q := mul_pos (by positivity) hqpos
      have hkpow : 1 < 2 ^ (2 ^ r * q) := Nat.one_lt_pow (Nat.ne_of_gt hkpos) (by omega)
      rw [pow_succ]
      have hA : 1 ≤ 2 ^ (2 ^ n) :=
        Nat.one_le_pow (2 ^ n) 2 (by omega)
      omega

end AgenticConjectures.OeisA369378
