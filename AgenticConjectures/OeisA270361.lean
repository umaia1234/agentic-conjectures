import Mathlib

/-!
# OEIS A270361 — uniqueness of the smaller odd-prime factor

OEIS A270361 records the conjecture that, for a fixed odd prime `p`, there is
at most one odd prime `q < p` for which `p * q - 1` is a square.

There is no upstream Lean snapshot for this entry.  The exported `statement`
uses `sourceRel p q`, the literal natural-number equation
`p * q - 1 = m ^ 2`.  Internally, `rel p q` uses the subtraction-safe
equivalent `p * q = m ^ 2 + 1`; `rel_of_source` proves the conversion under
the source's positivity hypotheses.  All quantifiers and strict inequalities
in the OEIS wording are preserved.  In fact, the proof only needs the two
candidate values of `q` to be odd and positive, so the private helper proves
a slightly stronger uniqueness result.

The key observation is that every square witness is even and lies strictly
between `0` and `p`.  Two witnesses for the same `p` are roots of `X² + 1`
modulo `p`, hence primality says that their difference or sum is divisible by
`p`.  The difference is too small unless it is zero, while the sum is positive
and below `2p`; if divisible by `p` it would equal the odd number `p`,
contradicting that both witnesses are even.
-/

namespace AgenticConjectures.OeisA270361

/-- Literal form of the OEIS condition "`p * q - 1` is a square" over `ℕ`. -/
def sourceRel (p q : ℕ) : Prop :=
  ∃ m : ℕ, p * q - 1 = m ^ 2

/-- Subtraction-safe form of "`p * q - 1` is a square" over `ℕ`. -/
def rel (p q : ℕ) : Prop :=
  ∃ m : ℕ, p * q = m ^ 2 + 1

/-- For every odd prime `p`, at most one odd prime `q < p` satisfies the
literal OEIS square condition. -/
def statement : Prop :=
  ∀ p : ℕ, p.Prime → Odd p →
    ∀ q₁ q₂ : ℕ,
      q₁.Prime → Odd q₁ → q₁ < p → sourceRel p q₁ →
      q₂.Prime → Odd q₂ → q₂ < p → sourceRel p q₂ →
      q₁ = q₂

private lemma rel_of_source {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (h : sourceRel p q) : rel p q := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  omega

private lemma witness_lt {p q m : ℕ} (hp : 0 < p) (hq : q < p)
    (hm : p * q = m ^ 2 + 1) : m < p := by
  have hprod : p * q < p * p := (Nat.mul_lt_mul_left hp).2 hq
  have hsquares : m ^ 2 < p ^ 2 := by
    calc
      m ^ 2 < m ^ 2 + 1 := Nat.lt_succ_self _
      _ = p * q := hm.symm
      _ < p * p := hprod
      _ = p ^ 2 := by simp [pow_two]
  exact (Nat.pow_lt_pow_iff_left (by norm_num : 2 ≠ 0)).mp hsquares

private lemma witness_even {p q m : ℕ} (hp : Odd p) (hq : Odd q)
    (hm : p * q = m ^ 2 + 1) : Even m := by
  have hsquare_succ : Odd (m ^ 2 + 1) := by
    rw [← hm]
    exact hp.mul hq
  have hsquare : Even (m ^ 2) :=
    Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hsquare_succ)
  exact (Nat.even_pow.mp hsquare).1

private lemma witness_pos {p q m : ℕ} (hp : p.Prime) (hq : Odd q)
    (hm : p * q = m ^ 2 + 1) : 0 < m := by
  by_contra h
  have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
  subst m
  norm_num at hm
  have hp_le : p ≤ p * q := Nat.le_mul_of_pos_right p hq.pos
  have hp_two : 2 ≤ p := hp.two_le
  omega

private lemma ordered_witnesses_equal {p q₁ q₂ m₁ m₂ : ℕ}
    (hp : p.Prime) (hpodd : Odd p)
    (hq₁odd : Odd q₁) (hq₂odd : Odd q₂)
    (hq₁lt : q₁ < p) (hq₂lt : q₂ < p)
    (hm₁ : p * q₁ = m₁ ^ 2 + 1) (hm₂ : p * q₂ = m₂ ^ 2 + 1)
    (horder : m₁ ≤ m₂) : m₁ = m₂ := by
  have hm₁lt : m₁ < p := witness_lt hp.pos hq₁lt hm₁
  have hm₂lt : m₂ < p := witness_lt hp.pos hq₂lt hm₂
  have hm₁even : Even m₁ := witness_even hpodd hq₁odd hm₁
  have hm₂even : Even m₂ := witness_even hpodd hq₂odd hm₂
  have hm₁pos : 0 < m₁ := witness_pos hp hq₁odd hm₁

  have hp_dvd_sq₁ : p ∣ m₁ ^ 2 + 1 := ⟨q₁, hm₁.symm⟩
  have hp_dvd_sq₂ : p ∣ m₂ ^ 2 + 1 := ⟨q₂, hm₂.symm⟩
  have hp_dvd_diff : p ∣ (m₂ ^ 2 + 1) - (m₁ ^ 2 + 1) :=
    Nat.dvd_sub hp_dvd_sq₂ hp_dvd_sq₁
  have hp_dvd_product : p ∣ (m₂ + m₁) * (m₂ - m₁) := by
    rw [← Nat.sq_sub_sq]
    have hdiff : (m₂ ^ 2 + 1) - (m₁ ^ 2 + 1) = m₂ ^ 2 - m₁ ^ 2 := by
      omega
    rwa [hdiff] at hp_dvd_diff

  rcases (hp.dvd_mul.mp hp_dvd_product) with hp_dvd_sum | hp_dvd_difference
  · have hsum_pos : 0 < m₂ + m₁ := by omega
    have hsum_lt : m₂ + m₁ < 2 * p := by omega
    obtain ⟨k, hk⟩ := hp_dvd_sum
    have hk_pos : 0 < k := by
      by_contra hk0
      have : k = 0 := Nat.eq_zero_of_not_pos hk0
      subst k
      simp at hk
      omega
    have hk_one : k = 1 := by
      by_contra hk_ne
      have hk_two : 2 ≤ k := by omega
      have htwo_le : p * 2 ≤ p * k := Nat.mul_le_mul_left p hk_two
      omega
    subst k
    simp at hk
    have hp_even : Even p := by
      rw [← hk]
      exact hm₂even.add hm₁even
    exact False.elim ((Nat.not_even_iff_odd.mpr hpodd) hp_even)
  · have hdiff_lt : m₂ - m₁ < p :=
      lt_of_le_of_lt (Nat.sub_le m₂ m₁) hm₂lt
    have hdiff_zero : m₂ - m₁ = 0 :=
      Nat.eq_zero_of_dvd_of_lt hp_dvd_difference hdiff_lt
    omega

private theorem odd_factor_unique {p q₁ q₂ : ℕ}
    (hp : p.Prime) (hpodd : Odd p)
    (hq₁odd : Odd q₁) (hq₂odd : Odd q₂)
    (hq₁lt : q₁ < p) (hq₂lt : q₂ < p)
    (hrel₁ : rel p q₁) (hrel₂ : rel p q₂) : q₁ = q₂ := by
  obtain ⟨m₁, hm₁⟩ := hrel₁
  obtain ⟨m₂, hm₂⟩ := hrel₂
  have hwitness : m₁ = m₂ := by
    rcases le_total m₁ m₂ with horder | horder
    · exact ordered_witnesses_equal hp hpodd hq₁odd hq₂odd
        hq₁lt hq₂lt hm₁ hm₂ horder
    · exact (ordered_witnesses_equal hp hpodd hq₂odd hq₁odd
        hq₂lt hq₁lt hm₂ hm₁ horder).symm
  have hproducts : p * q₁ = p * q₂ := by
    rw [hm₁, hm₂, hwitness]
  exact Nat.eq_of_mul_eq_mul_left hp.pos hproducts

/-- **OEIS A270361 conjecture**: an odd prime `p` admits at most one smaller
odd prime `q` such that `p * q - 1` is a square. -/
theorem oeis_a270361_conjecture : statement := by
  intro p hp hpodd q₁ q₂ _ hq₁odd hq₁lt hsource₁ _ hq₂odd hq₂lt hsource₂
  exact odd_factor_unique hp hpodd hq₁odd hq₂odd hq₁lt hq₂lt
    (rel_of_source hp.pos hq₁odd.pos hsource₁)
    (rel_of_source hp.pos hq₂odd.pos hsource₂)

end AgenticConjectures.OeisA270361
