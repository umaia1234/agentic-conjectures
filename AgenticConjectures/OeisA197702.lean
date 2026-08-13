import Mathlib

/-!
# OEIS A197702 — signed sums of consecutive odd numbers

OEIS A197702 defines `a(n)` to be the least positive `k` for which `n` is a
signed sum of the first `k` positive odd numbers.  Its conjectured formula is
proved here for every `n` in the official offset (`n >= 1`).

We encode the indices carrying a minus sign by a finset `S : Finset (Fin k)`.
Since the sum of the first `k` odd numbers is `k^2`, the signed-sum condition is
exactly

`n + 2 * sum_{i in S} (2*i+1) = k^2`.

If `(k-1)^2 < n <= k^2` and `d = k^2-n`, then `d < 2*k-1`.  The theorem below
proves that the least signed-sum length is

* `k+2` when `d=4`;
* `k+1` when `d` is odd;
* `k` otherwise (including `d=0`).

The only obstruction is the elementary fact that `2` is not a sum of
distinct positive odd numbers.  Every other positive `t < 2*k+1` is such a
sum: use the singleton `{t}` when `t` is odd, and `{1,t-1}` when `t` is even.

Faithfulness notes (there is no upstream Lean snapshot for this entry):

* `Fin k` indexes exactly `1,3,...,2*k-1`, with no duplicate signs.
* The equation above is equivalent to choosing `+` or `-` independently for
  every one of those `k` terms.
* `predictedLength` uses the square gap from the OEIS wording.  The hypothesis
  `d+1 < 2*k` is equivalent, for positive `k`, to `d < 2*k-1`, hence to the
  entry's interval `(k-1)^2 < n` once `n+d=k^2`.
* `a` is the infimum of exactly the positive representable lengths.  The main
  theorem supplies an attained least element, so no empty-set convention is
  involved.
-/

namespace AgenticConjectures.OeisA197702

open scoped BigOperators

/-- The positive odd number in position `i`, with positions starting at zero. -/
def oddWeight {k : ℕ} (i : Fin k) : ℕ := 2 * i.val + 1

/-- A literal choice of signs for the first `k` positive odd numbers. -/
def SignedSum (n k : ℕ) : Prop :=
  ∃ ε : Fin k → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    (n : ℤ) = ∑ i, ε i * oddWeight i

/-- `n` is a signed sum `±1 ±3 ... ±(2k-1)`.  The members of `S` are
the positions assigned a minus sign. -/
def Representable (n k : ℕ) : Prop :=
  ∃ S : Finset (Fin k), n + 2 * ∑ i ∈ S, oddWeight i = k * k

private theorem sum_all_oddWeights (k : ℕ) :
    ∑ i : Fin k, oddWeight i = k * k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_succ]
      have hweight (i : Fin k) : oddWeight i.succ = oddWeight i + 2 := by
        simp [oddWeight]
        omega
      have htail : ∑ i : Fin k, oddWeight i.succ =
          (∑ i : Fin k, oddWeight i) + 2 * k := by
        calc
          _ = ∑ i : Fin k, (oddWeight i + 2) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact hweight i
          _ = (∑ i : Fin k, oddWeight i) + ∑ _i : Fin k, 2 :=
            Finset.sum_add_distrib
          _ = (∑ i : Fin k, oddWeight i) + 2 * k := by simp [Nat.mul_comm]
      rw [htail, ih]
      simp only [oddWeight, Fin.val_zero]
      nlinarith

private theorem membershipSign_sum {k : ℕ} (S : Finset (Fin k)) :
    (∑ i : Fin k, (if i ∈ S then (-1 : ℤ) else 1) * oddWeight i) =
      (∑ i : Fin k, (oddWeight i : ℤ)) -
        2 * ∑ i ∈ S, (oddWeight i : ℤ) := by
  calc
    _ = ∑ i : Fin k,
        ((oddWeight i : ℤ) - if i ∈ S then (2 : ℤ) * oddWeight i else 0) := by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hi : i ∈ S
      · simp [hi]
        ring
      · simp [hi]
    _ = (∑ i : Fin k, (oddWeight i : ℤ)) -
        ∑ i : Fin k, if i ∈ S then (2 : ℤ) * oddWeight i else 0 := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ i : Fin k, (oddWeight i : ℤ)) -
        2 * ∑ i ∈ S, (oddWeight i : ℤ) := by
      congr 1
      simp [Finset.mul_sum]

/-- The normalized natural-number equation is exactly equivalent to the
literal choice between positive and negative signs in the OEIS definition. -/
theorem signedSum_iff_representable (n k : ℕ) :
    SignedSum n k ↔ Representable n k := by
  constructor
  · rintro ⟨ε, hε, hsum⟩
    let S : Finset (Fin k) := Finset.univ.filter fun i ↦ ε i = -1
    have hεeq : ε = fun i ↦ if i ∈ S then -1 else 1 := by
      funext i
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with hneg
      · exact hneg
      · rcases hε i with hpos | hneg'
        · exact hpos
        · exact False.elim (hneg hneg')
    refine ⟨S, ?_⟩
    have hall : (∑ i : Fin k, (oddWeight i : ℤ)) = k * k := by
      norm_cast
      exact sum_all_oddWeights k
    have hnat : (n : ℤ) + 2 * ∑ i ∈ S, (oddWeight i : ℤ) = k * k := by
      rw [hsum, hεeq, membershipSign_sum, hall]
      linarith
    exact_mod_cast hnat
  · rintro ⟨S, hS⟩
    let ε : Fin k → ℤ := fun i ↦ if i ∈ S then -1 else 1
    refine ⟨ε, ?_, ?_⟩
    · intro i
      simp only [ε]
      split <;> simp
    · have hall : (∑ i : Fin k, (oddWeight i : ℤ)) = k * k := by
        norm_cast
        exact sum_all_oddWeights k
      have hScast : (n : ℤ) + 2 * ∑ i ∈ S, (oddWeight i : ℤ) = k * k := by
        exact_mod_cast hS
      simp only [ε]
      rw [membershipSign_sum, hall]
      linarith

/-- The length prescribed by the conjecture from the upper square `k^2` and
the gap `d = k^2-n`. -/
def predictedLength (k d : ℕ) : ℕ :=
  if d = 4 then k + 2 else if Odd d then k + 1 else k

/-- OEIS A197702 as an infimum of its qualifying positive lengths. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ Representable n k}

private theorem exists_oddWeight_sum (k t : ℕ) (hk : 0 < k) (ht : 0 < t)
    (htop : t < 2 * k + 1) (htwo : t ≠ 2) :
    ∃ S : Finset (Fin k), ∑ i ∈ S, oddWeight i = t := by
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' t
  · have hr_gt : 1 < r := by omega
    have hr_le : r ≤ k := by omega
    let i₀ : Fin k := ⟨0, hk⟩
    let i₁ : Fin k := ⟨r - 1, by omega⟩
    have hne : i₀ ≠ i₁ := by
      intro h
      have hval := congrArg Fin.val h
      simp only [i₀, i₁] at hval
      omega
    refine ⟨{i₀, i₁}, ?_⟩
    rw [Finset.sum_insert (by simpa [eq_comm] using hne), Finset.sum_singleton]
    simp only [oddWeight, i₀, i₁]
    omega
  · have hr_lt : r < k := by omega
    let i : Fin k := ⟨r, hr_lt⟩
    refine ⟨{i}, ?_⟩
    simp only [Finset.sum_singleton, oddWeight, i]
    omega

/-- Two is the unique small obstruction: it is not a sum of distinct positive
odd numbers, regardless of how many initial odd numbers are available. -/
private theorem oddWeight_sum_ne_two {k : ℕ} (S : Finset (Fin k)) :
    (∑ i ∈ S, oddWeight i) ≠ 2 := by
  intro hsum
  have hcard : S.card ≤ 2 := by
    calc
      S.card = ∑ _i ∈ S, 1 := by simp
      _ ≤ ∑ i ∈ S, oddWeight i := by
        exact Finset.sum_le_sum fun i _hi ↦ by simp [oddWeight]
      _ = 2 := hsum
  interval_cases h : S.card
  · have hS : S = ∅ := Finset.card_eq_zero.mp h
    subst S
    simp at hsum
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h
    simp [oddWeight] at hsum
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp h
    have hi_not_mem : i ∉ ({j} : Finset (Fin k)) := by simp [hij]
    rw [Finset.sum_insert hi_not_mem, Finset.sum_singleton] at hsum
    simp only [oddWeight] at hsum
    have hi : i.val = 0 := by omega
    have hj : j.val = 0 := by omega
    apply hij
    apply Fin.ext
    omega

private theorem representable_le_square {n j : ℕ} (h : Representable n j) :
    n ≤ j * j := by
  rcases h with ⟨S, hS⟩
  omega

/-- The exact least-length formula behind OEIS A197702. -/
theorem predictedLength_isLeast (n k d : ℕ) (hk : 0 < k)
    (hgap : n + d = k * k) (hwindow : d + 1 < 2 * k) :
    IsLeast {j : ℕ | 0 < j ∧ Representable n j} (predictedLength k d) := by
  have hlower : (k - 1) * (k - 1) < n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    simp only [Nat.add_one_sub_one]
    nlinarith
  have hbelow : ∀ {j : ℕ}, j < k → ¬Representable n j := by
    intro j hj hrep
    have hj_le : j ≤ k - 1 := by omega
    have hsquare : j * j ≤ (k - 1) * (k - 1) :=
      Nat.mul_self_le_mul_self hj_le
    have hn_le := representable_le_square hrep
    omega
  constructor
  · by_cases hd4 : d = 4
    · subst d
      have ht : 0 < 2 * k + 4 := by omega
      have htop : 2 * k + 4 < 2 * (k + 2) + 1 := by omega
      obtain ⟨S, hS⟩ :=
        exists_oddWeight_sum (k + 2) (2 * k + 4) (by omega) ht htop (by omega)
      change 0 < k + 2 ∧ Representable n (k + 2)
      refine ⟨by omega, ⟨S, ?_⟩⟩
      rw [hS]
      nlinarith
    · obtain ⟨r, heven | hodd⟩ := Nat.even_or_odd' d
      · have hd_not_odd : ¬Odd d := by
          rw [heven]
          simp
        simp only [predictedLength, if_neg hd4, if_neg hd_not_odd]
        by_cases hr0 : r = 0
        · subst r
          refine ⟨hk, ⟨∅, ?_⟩⟩
          simp only [Finset.sum_empty, mul_zero, add_zero]
          omega
        · have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
          have hr_top : r < 2 * k + 1 := by omega
          have hr_two : r ≠ 2 := by
            intro hr
            apply hd4
            omega
          obtain ⟨S, hS⟩ := exists_oddWeight_sum k r hk hr_pos hr_top hr_two
          refine ⟨hk, ⟨S, ?_⟩⟩
          rw [hS]
          omega
      · have hd_odd : Odd d := ⟨r, hodd⟩
        simp only [predictedLength, if_neg hd4, if_pos hd_odd]
        have ht_pos : 0 < k + r + 1 := by omega
        have ht_top : k + r + 1 < 2 * (k + 1) + 1 := by omega
        have ht_two : k + r + 1 ≠ 2 := by omega
        obtain ⟨S, hS⟩ :=
          exists_oddWeight_sum (k + 1) (k + r + 1) (by omega) ht_pos ht_top ht_two
        refine ⟨by omega, ⟨S, ?_⟩⟩
        rw [hS]
        nlinarith
  · intro j hj
    rcases hj with ⟨hj_pos, hrep⟩
    by_cases hd4 : d = 4
    · subst d
      change k + 2 ≤ j
      by_contra hnot
      have hj_lt : j < k + 2 := by omega
      by_cases hjk : j < k
      · exact hbelow hjk hrep
      have hj_cases : j = k ∨ j = k + 1 := by omega
      rcases hj_cases with rfl | rfl
      · rcases hrep with ⟨S, hS⟩
        have hsum : ∑ i ∈ S, oddWeight i = 2 := by omega
        exact oddWeight_sum_ne_two S hsum
      · rcases hrep with ⟨S, hS⟩
        have hparity : 2 * (∑ i ∈ S, oddWeight i) = 2 * k + 5 := by
          nlinarith
        omega
    · obtain ⟨r, heven | hodd⟩ := Nat.even_or_odd' d
      · have hd_not_odd : ¬Odd d := by
          rw [heven]
          simp
        simp only [predictedLength, if_neg hd4, if_neg hd_not_odd]
        by_contra hnot
        exact hbelow (by omega) hrep
      · have hd_odd : Odd d := ⟨r, hodd⟩
        simp only [predictedLength, if_neg hd4, if_pos hd_odd]
        by_contra hnot
        have hj_lt : j < k + 1 := by omega
        by_cases hjk : j < k
        · exact hbelow hjk hrep
        have hj_eq : j = k := by omega
        subst j
        rcases hrep with ⟨S, hS⟩
        have hparity : 2 * (∑ i ∈ S, oddWeight i) = 2 * r + 1 := by
          omega
        omega

/-- The OEIS sequence has exactly the conjectured value in every square
interval. -/
theorem a_eq_predictedLength (n k d : ℕ) (hk : 0 < k)
    (hgap : n + d = k * k) (hwindow : d + 1 < 2 * k) :
    a n = predictedLength k d := by
  have hleast := predictedLength_isLeast n k d hk hgap hwindow
  apply Nat.le_antisymm
  · exact Nat.sInf_le hleast.1
  · have hmem : a n ∈ {j : ℕ | 0 < j ∧ Representable n j} :=
      Nat.sInf_mem ⟨predictedLength k d, hleast.1⟩
    exact hleast.2 hmem

/-- The universal conjecture in the square-interval wording used by OEIS.
The hypotheses say `(k-1)^2 < n ≤ k^2`; the gap is `k^2-n`. -/
def statement : Prop :=
  ∀ n k : ℕ, 0 < k → (k - 1) * (k - 1) < n → n ≤ k * k →
    a n = if k * k - n = 4 then k + 2
      else if Odd (k * k - n) then k + 1 else k

/-- **OEIS A197702:** the conjectured three-case formula holds for all
official indices. -/
theorem oeis_a197702 : statement := by
  intro n k hk hlower hupper
  let d := k * k - n
  have hgap : n + d = k * k := Nat.add_sub_of_le hupper
  have hwindow : d + 1 < 2 * k := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    simp only [Nat.add_one_sub_one] at hlower
    dsimp only [d] at hgap ⊢
    nlinarith
  exact a_eq_predictedLength n k d hk hgap hwindow

end AgenticConjectures.OeisA197702
