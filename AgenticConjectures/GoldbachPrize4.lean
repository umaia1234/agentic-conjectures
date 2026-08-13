import Mathlib

/-!
# Let's Prove Goldbach prize problem 4

The current prize page at <https://www.dimostriamogoldbach.it/en/prizes/>
asks whether, for primes `n₁ < n₂ < n₃` and every integer `n > 1`, there
are positive integers `h,k` with `h+k=n` such that neither `n₁*h-1` nor
`n₁*k+1` is divisible by `n₂` or `n₃`.

We formalize the quantifiers over natural numbers.  This agrees with the
source's positivity requirements.  Natural subtraction causes no semantic
problem because `n₁` is prime and `h` is positive, hence `n₁*h >= 2`; the
explicit counterexample below also satisfies the stronger bound `n >= 4`.
-/

namespace AgenticConjectures.GoldbachPrize4

/-- The universal assertion in prize problem 4. -/
def statement : Prop :=
  ∀ n₁ n₂ n₃ n : ℕ,
    Nat.Prime n₁ → Nat.Prime n₂ → Nat.Prime n₃ →
    n₁ < n₂ → n₂ < n₃ → 1 < n →
    ∃ h k : ℕ,
      0 < h ∧ 0 < k ∧ h + k = n ∧
      ¬ n₂ ∣ n₁ * h - 1 ∧ ¬ n₃ ∣ n₁ * h - 1 ∧
      ¬ n₂ ∣ n₁ * k + 1 ∧ ¬ n₃ ∣ n₁ * k + 1

/-- The assertion is false for `(n₁,n₂,n₃,n)=(2,3,5,5)`.
For the four positive decompositions of `5`, respectively, one has
`3 ∣ 2*4+1`, `3 ∣ 2*2-1`, `5 ∣ 2*3-1`, or `3 ∣ 2*1+1`. -/
theorem refuted : ¬ statement := by
  intro hstatement
  obtain ⟨h, k, hh, hk, hsum, h3hm, h5hm, h3kp, h5kp⟩ :=
    hstatement 2 3 5 5 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hcases :
      (h = 1 ∧ k = 4) ∨ (h = 2 ∧ k = 3) ∨
      (h = 3 ∧ k = 2) ∨ (h = 4 ∧ k = 1) := by
    omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h3kp (by norm_num)
  · exact h3hm (by norm_num)
  · exact h5hm (by norm_num)
  · exact h3kp (by norm_num)

end AgenticConjectures.GoldbachPrize4
