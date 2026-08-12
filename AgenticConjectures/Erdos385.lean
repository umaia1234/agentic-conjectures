import Mathlib

/-!
# Erdős problem 385 — an unconditional odd-index subfamily

The original 1979 paper defines

`F(n) = max {m + p(m) | m < n and m is composite}`,

where `p(m)` is the least prime divisor of `m`, and asks whether `F(n) ≤ n`
infinitely often.  It then says plausible prime conjectures predict only
finitely many such indices.  The current canonical page therefore asks the
logically opposite eventual form `F(n) > n` and whether `F(n) - n` tends to
infinity.  The original and current sources were checked on 2026-08-12:
https://users.renyi.hu/~p_erdos/1979-23.pdf and
https://www.erdosproblems.com/385.

The upstream FormalConjectures snapshot uses `sSup` and its
`Nat.Composite` predicate.  Here `Composite m` is stated explicitly as
`1 < m ∧ ¬ Nat.Prime m`, and `F` is the supremum of the finite range
`m < n`.  Thus it is the same maximum whenever that range contains a
composite; unlike the upstream `sSup` presentation, it is definitionally zero
when the range is empty.  Our theorem starts at `n = 5`, so this boundary
difference is irrelevant.  All indices and least prime factors are natural
numbers; the only subtraction is `n - 1`, protected by `5 ≤ n`.

This module does not assert either open asymptotic statement.  It proves the
elementary but infinite subfamily `F(n) > n` for every odd `n ≥ 5`.
-/

namespace AgenticConjectures.Erdos385

/-- The explicit composite-number predicate used in the finite maximum. -/
def Composite (m : ℕ) : Prop := 1 < m ∧ ¬ m.Prime

/-- The exact finite maximum from Erdős problem 385, with value zero when the
candidate set is empty. -/
noncomputable def F (n : ℕ) : ℕ := by
  classical
  exact (Finset.range n).sup fun m => if Composite m then m + m.minFac else 0

/-- Every composite `m < n` contributes its defining candidate to `F(n)`. -/
theorem candidate_le_F {m n : ℕ} (hmn : m < n) (hm : Composite m) :
    m + m.minFac ≤ F n := by
  classical
  have hle := Finset.le_sup
    (f := fun k => if Composite k then k + k.minFac else 0)
    (Finset.mem_range.mpr hmn)
  simpa only [F, if_pos hm] using hle

/-- The first question in Erdős 385 holds unconditionally at every odd index
`n ≥ 5`: the even composite witness `m = n - 1` gives `F(n) ≥ n + 1`. -/
theorem odd_index_lt_F (n : ℕ) (hn : 5 ≤ n) (hodd : Odd n) : n < F n := by
  have htwo : 2 ∣ n - 1 := by
    rcases hodd with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    omega
  have heven : Even (n - 1) := even_iff_two_dvd.mpr htwo
  have hcomposite : Composite (n - 1) := by
    refine ⟨by omega, ?_⟩
    intro hprime
    have heq : n - 1 = 2 := hprime.even_iff.mp heven
    omega
  have hle := candidate_le_F (m := n - 1) (n := n) (by omega) hcomposite
  have hminfac : (n - 1).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr htwo
  rw [hminfac] at hle
  omega

/-- The elementary baseline used by the finite certificate: `F(n) ≥ n` for
every `n ≥ 5`.  At an even index, `m = n - 2` is an even composite witness;
at an odd index, `odd_index_lt_F` is stronger. -/
theorem index_le_F (n : ℕ) (hn : 5 ≤ n) : n ≤ F n := by
  by_cases hodd : Odd n
  · exact (odd_index_lt_F n hn hodd).le
  · have heven : Even n := Nat.not_odd_iff_even.mp hodd
    have htwo : 2 ∣ n - 2 := by
      rcases heven with ⟨k, hk⟩
      refine ⟨k - 1, ?_⟩
      omega
    have hneven : Even (n - 2) := even_iff_two_dvd.mpr htwo
    have hcomposite : Composite (n - 2) := by
      refine ⟨by omega, ?_⟩
      intro hprime
      have heq : n - 2 = 2 := hprime.even_iff.mp hneven
      omega
    have hle := candidate_le_F (m := n - 2) (n := n) (by omega) hcomposite
    have hminfac : (n - 2).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr htwo
    rw [hminfac] at hle
    omega

end AgenticConjectures.Erdos385
