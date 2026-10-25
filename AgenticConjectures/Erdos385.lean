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
elementary but infinite subfamily `F(n) > n` for every odd `n ≥ 5`, and more
generally whenever `n - 1` is not prime (for example `n % 6 = 4`).  It also
proves the coverage criterion `n < F n ↔ ∃ m < n, Composite m ∧ n < m + p(m)`
used by the finite certificate programs, and the resulting necessary condition
for an equality case: if `n ≥ 5` and `F n = n`, then `n` is even and `n - 1` is
prime.
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

/-- The coverage criterion behind the finite certificate: `F(n) > n` exactly
when some composite `m < n` satisfies `n < m + p(m)`, i.e. `n - m < p(m)`. -/
theorem lt_F_iff (n : ℕ) : n < F n ↔ ∃ m < n, Composite m ∧ n < m + m.minFac := by
  classical
  unfold F
  rw [Finset.lt_sup_iff]
  constructor
  · rintro ⟨m, hm, hlt⟩
    by_cases hc : Composite m
    · exact ⟨m, Finset.mem_range.mp hm, hc, by simpa [hc] using hlt⟩
    · simp [hc] at hlt
  · rintro ⟨m, hm, hc, hlt⟩
    exact ⟨m, Finset.mem_range.mpr hm, by simpa [hc] using hlt⟩

/-- Generalization of `odd_index_lt_F`: if `n ≥ 5` and `n - 1` is not prime,
then the composite witness `m = n - 1` gives `F(n) ≥ n - 1 + p(n - 1) > n`. -/
theorem lt_F_of_not_prime_pred (n : ℕ) (hn : 5 ≤ n) (hprime : ¬ (n - 1).Prime) :
    n < F n := by
  have hcomposite : Composite (n - 1) := ⟨by omega, hprime⟩
  have hle := candidate_le_F (m := n - 1) (n := n) (by omega) hcomposite
  have htwo : 2 ≤ (n - 1).minFac := (Nat.minFac_prime (by omega)).two_le
  omega

/-- An even residue class beyond the odd indices: if `n ≥ 5` and `n ≡ 4 (mod 6)`,
then `n - 1 ≥ 9` is an odd multiple of `3`, hence composite, and `F(n) > n`. -/
theorem lt_F_of_mod_six_eq_four (n : ℕ) (hn : 5 ≤ n) (hmod : n % 6 = 4) : n < F n := by
  apply lt_F_of_not_prime_pred n hn
  intro hprime
  have hthree : 3 ∣ n - 1 := by omega
  have := hprime.eq_one_or_self_of_dvd 3 hthree
  omega

/-- Necessary condition for an equality case: if `n ≥ 5` and `F(n) = n`, then
`n` is even and `n - 1` is prime. -/
theorem even_and_prime_pred_of_F_eq (n : ℕ) (hn : 5 ≤ n) (heq : F n = n) :
    Even n ∧ (n - 1).Prime := by
  constructor
  · by_contra hnot
    have := odd_index_lt_F n hn (Nat.not_even_iff_odd.mp hnot)
    omega
  · by_contra hnot
    have := lt_F_of_not_prime_pred n hn hnot
    omega

end AgenticConjectures.Erdos385
