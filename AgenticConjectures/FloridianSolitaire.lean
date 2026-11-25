import Mathlib

/-!
# Floridian solitaire — immediate losses for every `n > 6`

Meyerowitz, Curran, Locke, and Low, *Floridian Solitaire: A New Variant of
Bulgarian Solitaire*, arXiv:2608.08313, ask in "Directions for further
research":

> Prove that there is a losing position for each `n > 6`. The open cases are
> `n = 6m` and `n = 6m + 2`.

An immediate loss is an α-position with no legal α-move, and every immediate
loss is a losing position. This module proves the stronger statement: every
integer `n > 6` has an immediate-loss position.

## Correspondence with the paper

* A position is a finite multiset of positive part sizes. Multiplicity is the
  paper's frequency notation, and selecting a submultiset is the paper's
  choice of individual parts.
* `Separated` says that no two consecutive positive integers both occur. That
  is exactly "distinct part sizes differ by at least two."
* `omega` is the paper's Ω-rule: subtract one from every part, delete parts
  that become zero, and add one part whose size is the old number of parts.
* A legal α-move is a nonempty submultiset selection whose result differs from
  the start and for which both the result and its Ω-image are separated. This
  is the paper's literal three-point definition of an α-move.
* The odd family `1, m, m` and the family `1, 3ᵐ` are the constructions the
  paper records for `n = 2m + 1 > 3` and `n = 3m + 1 > 4`. The block family and
  the witnesses `(1, 5, 5, 7)` and `(4, 4, 6, 6)` are the argument in
  `problems/floridian-solitaire/PROOF.md`.

## Where the formal statement is narrower than the paper's Lemma 7

Lemma 7 says that for a separated partition with `p` parts, `Ω` of that
partition is separated exactly when the partition has no part of size `p` or
`p + 2`. The singleton partition `(1)` is a counterexample to that wording:
`p = 1` occurs, but `Ω(1) = (1)` is separated. The equivalence proved here
assumes `1 < p`. Every partition of an integer greater than 1 to which the
equivalence is applied in this file has at least two parts.
-/

namespace AgenticConjectures.FloridianSolitaire

open Nat

/-- Distinct positive part sizes differ by at least two. -/
def Separated (μ : Multiset ℕ) : Prop :=
  ∀ a, μ.count a = 0 ∨ μ.count (a + 1) = 0

/-- The paper's Ω-rule. -/
def omega (μ : Multiset ℕ) : Multiset ℕ :=
  ((μ.map fun a => a - 1).filter (· ≠ 0)) + ({μ.card} : Multiset ℕ)

/-- The α-result of selecting the submultiset `σ`, before the legality test. -/
def alphaResult (μ σ : Multiset ℕ) : Multiset ℕ :=
  (μ - σ) + ((σ.map fun a => a - 1).filter (· ≠ 0)) + ({σ.card} : Multiset ℕ)

/-- The paper's three conditions for a legal α-move. -/
def IsLegalAlpha (μ σ : Multiset ℕ) : Prop :=
  σ ≤ μ ∧ σ ≠ 0 ∧ alphaResult μ σ ≠ μ ∧ Separated (alphaResult μ σ) ∧
    Separated (omega (alphaResult μ σ))

/-- An α-position with no legal α-move. -/
def ImmediateLoss (μ : Multiset ℕ) : Prop :=
  μ.count 0 = 0 ∧ Separated μ ∧ ∀ σ, ¬ IsLegalAlpha μ σ

lemma not_sep_consec {ν : Multiset ℕ} {a : ℕ}
    (ha : 0 < ν.count a) (hb : 0 < ν.count (a + 1)) : ¬ Separated ν := by
  intro h
  rcases h a with h0 | h1
  · omega
  · omega

lemma not_legal_sep {μ σ : Multiset ℕ} (h : ¬ Separated (alphaResult μ σ)) :
    ¬ IsLegalAlpha μ σ := by
  rintro ⟨_, _, _, hsep, _⟩
  exact h hsep

lemma not_legal_omega {μ σ : Multiset ℕ} (h : ¬ Separated (omega (alphaResult μ σ))) :
    ¬ IsLegalAlpha μ σ := by
  rintro ⟨_, _, _, _, hΩ⟩
  exact h hΩ

lemma not_legal_same {μ σ : Multiset ℕ} (h : alphaResult μ σ = μ) : ¬ IsLegalAlpha μ σ := by
  rintro ⟨_, _, hneq, _, _⟩
  exact hneq h

lemma not_legal_empty (μ : Multiset ℕ) : ¬ IsLegalAlpha μ 0 := by
  rintro ⟨_, hne, _, _, _⟩
  exact hne rfl

lemma count_map_pred_pos (σ : Multiset ℕ) {b : ℕ} (hb : 0 < b) :
    (σ.map fun a => a - 1).count b = σ.count (b + 1) := by
  rw [Multiset.count_map]
  have hfilter : σ.filter (fun a => b = a - 1) = Multiset.replicate (σ.count (b + 1)) (b + 1) := by
    ext a
    simp only [Multiset.count_filter, Multiset.count_replicate]
    by_cases ha : a = b + 1
    · subst ha
      simp
    · have hne : b ≠ a - 1 := by
        intro h
        apply ha
        have h1 : 1 ≤ a := by
          cases a with
          | zero => simp at h; omega
          | succ _ => exact Nat.succ_le_succ (Nat.zero_le _)
        exact (Nat.sub_eq_iff_eq_add h1).mp h.symm
      have hne' : b + 1 ≠ a := fun h => ha h.symm
      simp [hne, hne']
  rw [hfilter, Multiset.card_replicate]

lemma alpha_count (μ σ : Multiset ℕ) {b : ℕ} (hb : 0 < b) :
    (alphaResult μ σ).count b =
      μ.count b - σ.count b + σ.count (b + 1) + (if b = σ.card then 1 else 0) := by
  unfold alphaResult
  have hfilt : ((σ.map fun a => a - 1).filter (· ≠ 0)).count b =
      (σ.map fun a => a - 1).count b := by
    rw [Multiset.count_filter]
    simp [hb.ne']
  rw [Multiset.count_add, Multiset.count_add, Multiset.count_sub, hfilt,
    count_map_pred_pos σ hb, Multiset.count_singleton]

lemma count_alpha_ge_kept (μ σ : Multiset ℕ) {b : ℕ} (hb : 0 < b) :
    μ.count b - σ.count b ≤ (alphaResult μ σ).count b := by
  rw [alpha_count μ σ hb]
  omega

lemma count_alpha_ge_pred (μ σ : Multiset ℕ) {b : ℕ} (hb : 0 < b) :
    σ.count (b + 1) ≤ (alphaResult μ σ).count b := by
  rw [alpha_count μ σ hb]
  omega

lemma pos_count_of_card (μ σ : Multiset ℕ) (hc : 0 < σ.card) :
    0 < (alphaResult μ σ).count σ.card := by
  have h := alpha_count μ σ hc
  rw [h]
  simp

lemma count_map_pred_zero (σ : Multiset ℕ) (h0 : σ.count 0 = 0) :
    (σ.map fun a => a - 1).count 0 = σ.count 1 := by
  rw [Multiset.count_map]
  have hfilter : σ.filter (fun a => 0 = a - 1) = Multiset.replicate (σ.count 1) 1 := by
    ext a
    simp only [Multiset.count_filter, Multiset.count_replicate]
    cases a with
    | zero =>
        simp [h0]
    | succ a =>
        cases a with
        | zero => simp
        | succ a =>
            simp
  rw [hfilter, Multiset.card_replicate]

lemma card_filter_pred (σ : Multiset ℕ) (h0 : σ.count 0 = 0) :
    ((σ.map fun a => a - 1).filter (· ≠ 0)).card = σ.card - σ.count 1 := by
  set τ := σ.map fun a => a - 1
  have hcard : τ.card = σ.card := Multiset.card_map _ _
  have hsplit := Multiset.card_eq_countP_add_countP (fun x : ℕ => 0 = x) τ
  have hpos : Multiset.countP (fun x : ℕ => ¬ 0 = x) τ =
      (τ.filter (fun x => ¬ 0 = x)).card := by
    classical
    simpa using (Multiset.countP_eq_card_filter (p := fun x : ℕ => ¬ 0 = x) τ)
  have hfilt : τ.filter (fun x => ¬ 0 = x) = τ.filter (· ≠ 0) := by
    apply Multiset.filter_congr
    intro x _
    exact not_congr eq_comm
  have hzero : τ.count 0 = σ.count 1 := count_map_pred_zero σ h0
  have : τ.card = τ.count 0 + (τ.filter (· ≠ 0)).card := by
    simpa [Multiset.count, hpos, hfilt] using hsplit
  omega

lemma card_alphaResult (μ σ : Multiset ℕ) (hσ : σ ≤ μ) (h0 : μ.count 0 = 0) :
    (alphaResult μ σ).card = μ.card - σ.count 1 + 1 := by
  have hσ0 : σ.count 0 = 0 := by
    have := (Multiset.le_iff_count.mp hσ) 0
    omega
  unfold alphaResult
  rw [Multiset.card_add, Multiset.card_add, Multiset.card_sub hσ, Multiset.card_singleton,
    card_filter_pred σ hσ0]
  have hle1 : σ.count 1 ≤ σ.card := Multiset.countP_le_card _ σ
  have hle2 : σ.card ≤ μ.card := Multiset.card_le_card hσ
  omega

lemma count_alpha_zero (μ σ : Multiset ℕ) (hμ : μ.count 0 = 0) (hσ : σ ≤ μ)
    (hc : σ.card ≠ 0) : (alphaResult μ σ).count 0 = 0 := by
  unfold alphaResult
  rw [Multiset.count_add, Multiset.count_add, Multiset.count_sub, Multiset.count_filter,
    Multiset.count_singleton]
  have hσ0 : σ.count 0 = 0 := by
    have := (Multiset.le_iff_count.mp hσ) 0
    omega
  have hcard : 0 ≠ σ.card := by simpa [eq_comm] using hc
  simp [hμ, hσ0, hcard]

lemma count_omega (μ : Multiset ℕ) {b : ℕ} (hb : 0 < b) :
    (omega μ).count b = μ.count (b + 1) + (if b = μ.card then 1 else 0) := by
  unfold omega
  have hfilt : ((μ.map fun a => a - 1).filter (· ≠ 0)).count b =
      (μ.map fun a => a - 1).count b := by
    rw [Multiset.count_filter]
    simp [hb.ne']
  rw [Multiset.count_add, hfilt, count_map_pred_pos μ hb, Multiset.count_singleton]

lemma count_omega_zero (μ : Multiset ℕ) (hp : μ.card ≠ 0) : (omega μ).count 0 = 0 := by
  unfold omega
  rw [Multiset.count_add, Multiset.count_filter, Multiset.count_singleton]
  have hcard : 0 ≠ μ.card := by simpa [eq_comm] using hp
  simp [hcard]

/-- The paper's Lemma 7, for partitions with at least two parts. -/
theorem omega_separated_iff {μ : Multiset ℕ} (h0 : μ.count 0 = 0) (hsep : Separated μ)
    (hp : 1 < μ.card) :
    Separated (omega μ) ↔ μ.count μ.card = 0 ∧ μ.count (μ.card + 2) = 0 := by
  have h0μ : μ.count 0 = 0 := h0
  constructor
  · intro hΩ
    refine ⟨?_, ?_⟩
    · by_contra hpos
      have hpos' : 0 < μ.count μ.card := by omega
      have hpred : 0 < (omega μ).count (μ.card - 1) := by
        have hformula := count_omega μ (show 0 < μ.card - 1 by omega)
        rw [hformula]
        have : (μ.card - 1) + 1 = μ.card := by omega
        simp [this, hpos']
      have hhere : 0 < (omega μ).count μ.card := by
        have hformula := count_omega μ (show 0 < μ.card by omega)
        rw [hformula]
        simp
      have hhere' : 0 < (omega μ).count ((μ.card - 1) + 1) := by
        simpa [show (μ.card - 1) + 1 = μ.card by omega] using hhere
      exact not_sep_consec hpred hhere' hΩ
    · by_contra hpos
      have hpos' : 0 < μ.count (μ.card + 2) := by omega
      have hnext : 0 < (omega μ).count (μ.card + 1) := by
        have hformula := count_omega μ (show 0 < μ.card + 1 by omega)
        rw [hformula]
        simp [hpos']
      have hhere : 0 < (omega μ).count μ.card := by
        have hformula := count_omega μ (show 0 < μ.card by omega)
        rw [hformula]
        simp
      exact not_sep_consec hhere hnext hΩ
  · intro ⟨hp0, hp2⟩
    intro a
    by_cases ha0 : a = 0
    · left
      simpa [ha0] using count_omega_zero μ (by omega)
    · by_contra hboth
      push Not at hboth
      have ha : 0 < a := by omega
      have hca : 0 < (omega μ).count a := by omega
      have hcb : 0 < (omega μ).count (a + 1) := by omega
      rw [count_omega μ ha] at hca
      rw [count_omega μ (by omega : 0 < a + 1)] at hcb
      have hA : 0 < μ.count (a + 1) ∨ a = μ.card := by
        by_cases hap : a = μ.card
        · exact Or.inr hap
        · left
          simp [hap] at hca
          exact hca
      have hB : 0 < μ.count (a + 2) ∨ a + 1 = μ.card := by
        by_cases hap : a + 1 = μ.card
        · exact Or.inr hap
        · left
          simp [hap] at hcb
          exact hcb
      rcases hA with hA | hA
      · rcases hB with hB | hB
        · exact not_sep_consec hA hB hsep
        · have : 0 < μ.count μ.card := by simpa [hB] using hA
          omega
      · rcases hB with hB | hB
        · have : 0 < μ.count (μ.card + 2) := by simpa [hA] using hB
          omega
        · omega

lemma alpha_select_one (μ : Multiset ℕ) (h : ({1} : Multiset ℕ) ≤ μ) :
    alphaResult μ ({1} : Multiset ℕ) = μ := by
  unfold alphaResult
  have hmap : (({1} : Multiset ℕ).map fun a => a - 1) = {0} := by
    simp [Multiset.map_singleton]
  have hfilter : (({0} : Multiset ℕ).filter (fun a => a ≠ 0)) = 0 := by
    simp [Multiset.filter_singleton]
  rw [hmap, hfilter, Multiset.card_singleton]
  simpa using Multiset.add_sub_cancel h

/-! ### The two families already in the paper -/

def oddParts (m : ℕ) : Multiset ℕ := Multiset.replicate 2 m + {1}

lemma odd_sum (m : ℕ) : (oddParts m).sum = 2 * m + 1 := by
  unfold oddParts
  rw [Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_singleton, nsmul_eq_mul]
  norm_cast

lemma odd_count (m : ℕ) (_hm : m ≠ 1) (b : ℕ) :
    (oddParts m).count b = (if b = m then 2 else 0) + (if b = 1 then 1 else 0) := by
  unfold oddParts
  simp only [Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton, eq_comm]

theorem odd_immediateLoss (m : ℕ) (hm : 3 ≤ m) : ImmediateLoss (oddParts m) := by
  have hm1 : m ≠ 1 := by omega
  have hm2 : m ≠ 2 := by omega
  have hcount := odd_count m hm1
  have hcount1 : (oddParts m).count 1 = 1 := by rw [hcount]; simp [hm1.symm]
  have hcountm : (oddParts m).count m = 2 := by rw [hcount]; simp [hm1]
  have hcount_ne {b : ℕ} (h1 : b ≠ 1) (hbm : b ≠ m) : (oddParts m).count b = 0 := by
    rw [hcount]; simp [h1, hbm]
  have h0 : (oddParts m).count 0 = 0 := hcount_ne (by decide) (by omega)
  have hsepμ : Separated (oddParts m) := by
    intro a
    by_cases h1 : a = 1
    · subst h1
      exact Or.inr (hcount_ne (by decide) hm2.symm)
    · by_cases ham : a = m
      · subst ham
        exact Or.inr (hcount_ne (by omega) (by omega))
      · exact Or.inl (hcount_ne h1 ham)
  refine ⟨h0, hsepμ, ?_⟩
  intro σ hlegal
  rcases hlegal with ⟨hle, hne, hneq, hsepR, hΩ⟩
  have hi : σ.count 1 ≤ 1 := by
    have hle' := (Multiset.le_iff_count.mp hle) 1
    rwa [hcount1] at hle'
  have hj : σ.count m ≤ 2 := by
    have hle' := (Multiset.le_iff_count.mp hle) m
    rwa [hcountm] at hle'
  have hother (a : ℕ) (ha1 : a ≠ 1) (ham : a ≠ m) : σ.count a = 0 := by
    have hle' := (Multiset.le_iff_count.mp hle) a
    rw [hcount_ne ha1 ham] at hle'
    exact Nat.eq_zero_of_le_zero hle'
  have hmem : ∀ a ∈ σ, a = 1 ∨ a = m := by
    intro a ha
    by_contra hnot
    push Not at hnot
    have := hother a hnot.1 hnot.2
    exact (Multiset.count_pos.mpr ha).ne' this
  have hsup : ∀ a ∈ σ, a ∈ ({1, m} : Finset ℕ) := by
    intro a ha
    rcases hmem a ha with rfl | rfl <;> simp
  have hsumc := Multiset.sum_count_eq_card (s := ({1, m} : Finset ℕ)) hsup
  have hpair : ∑ a ∈ ({1, m} : Finset ℕ), σ.count a = σ.count 1 + σ.count m := by
    exact Finset.sum_pair (f := fun a => σ.count a) hm1.symm
  have hcard : σ.card = σ.count 1 + σ.count m := by omega
  match h1 : σ.count 1, h2 : σ.count m with
  | 0, 0 =>
      exact hne (Multiset.card_eq_zero.mp (by omega))
  | 0, 1 =>
      have hb : 1 ≤ m := by omega
      have hge := count_alpha_ge_pred (oddParts m) σ (b := m - 1) (by omega)
      have hsum : (m - 1) + 1 = m := Nat.sub_add_cancel hb
      have hpred : 0 < (alphaResult (oddParts m) σ).count (m - 1) := by
        have hge' : σ.count m ≤ (alphaResult (oddParts m) σ).count (m - 1) := by
          simpa [hsum] using hge
        omega
      have hkeepge := count_alpha_ge_kept (oddParts m) σ (b := m) (by omega)
      have hkeep : 0 < (alphaResult (oddParts m) σ).count m := by
        have hkeep' : 2 - σ.count m ≤ (alphaResult (oddParts m) σ).count m := by
          simpa [hcountm] using hkeepge
        omega
      have hkeepAdj : 0 < (alphaResult (oddParts m) σ).count ((m - 1) + 1) := by
        simpa [hsum] using hkeep
      exact not_sep_consec hpred hkeepAdj hsepR
  | 0, 2 =>
      have hone : 0 < (alphaResult (oddParts m) σ).count 1 := by
        have hformula := alpha_count (oddParts m) σ (b := 1) (by decide)
        have hσ2 : σ.count 2 = 0 := hother 2 (by decide) hm2.symm
        rw [hcount1, h1, hσ2, show σ.card = 2 by omega] at hformula
        simp at hformula
        omega
      have htwo : 0 < (alphaResult (oddParts m) σ).count 2 := by
        have hformula := alpha_count (oddParts m) σ (b := 2) (by decide)
        have hσ2 : σ.count 2 = 0 := hother 2 (by decide) hm2.symm
        have hμ2 : (oddParts m).count 2 = 0 := hcount_ne (by decide) hm2.symm
        rw [hμ2, hσ2, show σ.card = 2 by omega] at hformula
        simp at hformula
        omega
      exact not_sep_consec hone htwo hsepR
  | 1, 0 =>
      have hσ : σ = {1} := by
        ext a
        simp only [Multiset.count_singleton]
        by_cases ha : a = 1
        · simp [ha, h1]
        · have : σ.count a = 0 := by
            by_cases ham : a = m
            · simp [ham, h2]
            · exact hother a ha ham
          simp [ha, this]
      have hle1 : ({1} : Multiset ℕ) ≤ oddParts m := by simpa [hσ] using hle
      exact hneq (by simpa [hσ] using alpha_select_one (oddParts m) hle1)
  | 1, 1 =>
      have hb : 1 ≤ m := by omega
      have hge := count_alpha_ge_pred (oddParts m) σ (b := m - 1) (by omega)
      have hsum : (m - 1) + 1 = m := Nat.sub_add_cancel hb
      have hpred : 0 < (alphaResult (oddParts m) σ).count (m - 1) := by
        have hge' : σ.count m ≤ (alphaResult (oddParts m) σ).count (m - 1) := by
          simpa [hsum] using hge
        omega
      have hkeepge := count_alpha_ge_kept (oddParts m) σ (b := m) (by omega)
      have hkeep : 0 < (alphaResult (oddParts m) σ).count m := by
        have hkeep' : 2 - σ.count m ≤ (alphaResult (oddParts m) σ).count m := by
          simpa [hcountm] using hkeepge
        omega
      have hkeepAdj : 0 < (alphaResult (oddParts m) σ).count ((m - 1) + 1) := by
        simpa [hsum] using hkeep
      exact not_sep_consec hpred hkeepAdj hsepR
  | 1, 2 =>
      have hcardμ : (oddParts m).card = 3 := by
        unfold oddParts
        simp
      have hres : (alphaResult (oddParts m) σ).card = 3 := by
        rw [card_alphaResult _ _ hle h0]
        omega
      have hpos3 : 0 < (alphaResult (oddParts m) σ).count 3 := by
        have hc : σ.card = 3 := by omega
        simpa [hc] using pos_count_of_card (oddParts m) σ (by omega)
      have hzeroR : (alphaResult (oddParts m) σ).count 0 = 0 :=
        count_alpha_zero _ _ h0 hle (by omega)
      have hiff := omega_separated_iff hzeroR hsepR (by omega : 1 < (alphaResult (oddParts m) σ).card)
      have hbad := hiff.mp hΩ
      have : (alphaResult (oddParts m) σ).count (alphaResult (oddParts m) σ).card = 0 := hbad.1
      rw [hres] at this
      omega
  | 0, _ + 3 => omega
  | 1, _ + 3 => omega
  | _ + 2, _ => omega

def threeParts (m : ℕ) : Multiset ℕ := Multiset.replicate m 3 + {1}

lemma three_sum (m : ℕ) : (threeParts m).sum = 3 * m + 1 := by
  unfold threeParts
  rw [Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_singleton, nsmul_eq_mul]
  norm_cast
  ring

lemma three_count (m : ℕ) (b : ℕ) :
    (threeParts m).count b = (if b = 3 then m else 0) + (if b = 1 then 1 else 0) := by
  unfold threeParts
  simp only [Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton, eq_comm]

theorem oneAndThrees_immediateLoss (m : ℕ) (hm : 1 ≤ m) : ImmediateLoss (threeParts m) := by
  have hcount := three_count m
  have hcount1 : (threeParts m).count 1 = 1 := by rw [hcount]; simp
  have hcount3 : (threeParts m).count 3 = m := by rw [hcount]; simp
  have hcount_ne {b : ℕ} (h1 : b ≠ 1) (h3 : b ≠ 3) : (threeParts m).count b = 0 := by
    rw [hcount]; simp [h1, h3]
  have h0 : (threeParts m).count 0 = 0 := hcount_ne (by decide) (by decide)
  have hsepμ : Separated (threeParts m) := by
    intro a
    by_cases h1 : a = 1
    · subst h1
      exact Or.inr (hcount_ne (by decide) (by decide))
    · by_cases h3 : a = 3
      · subst h3
        exact Or.inr (hcount_ne (by decide) (by decide))
      · exact Or.inl (hcount_ne h1 h3)
  refine ⟨h0, hsepμ, ?_⟩
  intro σ hlegal
  obtain ⟨hle, hne, hneq, hsepR, hΩ⟩ := hlegal
  have hi : σ.count 1 ≤ 1 := by
    have hle' := (Multiset.le_iff_count.mp hle) 1
    rwa [hcount1] at hle'
  have hj : σ.count 3 ≤ m := by
    have hle' := (Multiset.le_iff_count.mp hle) 3
    rwa [hcount3] at hle'
  have hother (a : ℕ) (ha1 : a ≠ 1) (ha3 : a ≠ 3) : σ.count a = 0 := by
    have hle' := (Multiset.le_iff_count.mp hle) a
    rw [hcount_ne ha1 ha3] at hle'
    exact Nat.eq_zero_of_le_zero hle'
  have hmem : ∀ a ∈ σ, a = 1 ∨ a = 3 := by
    intro a ha
    by_contra hnot
    push Not at hnot
    exact (Multiset.count_pos.mpr ha).ne' (hother a hnot.1 hnot.2)
  have hsup : ∀ a ∈ σ, a ∈ ({1, 3} : Finset ℕ) := by
    intro a ha
    rcases hmem a ha with rfl | rfl <;> simp
  have hsumc := Multiset.sum_count_eq_card (s := ({1, 3} : Finset ℕ)) hsup
  have hpair : ∑ a ∈ ({1, 3} : Finset ℕ), σ.count a = σ.count 1 + σ.count 3 :=
    Finset.sum_pair (f := fun a => σ.count a) (by decide : 1 ≠ 3)
  have hcard : σ.card = σ.count 1 + σ.count 3 := by omega
  by_cases hj0 : σ.count 3 = 0
  · by_cases hi0 : σ.count 1 = 0
    · exact hne (Multiset.card_eq_zero.mp (by omega))
    · have hi1 : σ.count 1 = 1 := by omega
      have hσ : σ = {1} := by
        ext a
        simp only [Multiset.count_singleton]
        by_cases ha : a = 1
        · simp [ha, hi1]
        · have : σ.count a = 0 := by
            by_cases ha3 : a = 3
            · simp [ha3, hj0]
            · exact hother a ha ha3
          simp [ha, this]
      exact hneq (by simpa [hσ] using alpha_select_one (threeParts m) (by simpa [hσ] using hle))
  · by_cases hpartial : σ.count 3 < m
    · have hpos3 : 0 < σ.count 3 := Nat.pos_of_ne_zero hj0
      have htwo : 0 < (alphaResult (threeParts m) σ).count 2 :=
        lt_of_lt_of_le hpos3 (count_alpha_ge_pred (threeParts m) σ (b := 2) (by decide))
      have hgap : 0 < m - σ.count 3 := Nat.sub_pos_of_lt hpartial
      have hthree : 0 < (alphaResult (threeParts m) σ).count 3 := by
        have hge := count_alpha_ge_kept (threeParts m) σ (b := 3) (by decide)
        have hge' : m - σ.count 3 ≤ (alphaResult (threeParts m) σ).count 3 := by
          simpa [hcount3] using hge
        exact lt_of_lt_of_le hgap hge'
      exact not_sep_consec htwo hthree hsepR
    · have hjfull : σ.count 3 = m := by omega
      by_cases hi0 : σ.count 1 = 0
      · have hone : 0 < (alphaResult (threeParts m) σ).count 1 := by
          have hformula := alpha_count (threeParts m) σ (b := 1) (by decide)
          have hσ2 : σ.count 2 = 0 := hother 2 (by decide) (by decide)
          have hcard' : σ.card = m := by omega
          rw [hcount1, hi0, hσ2, hcard'] at hformula
          by_cases hm1 : m = 1
          · subst hm1
            simp at hformula
            omega
          · have hne1 : 1 ≠ m := fun h => hm1 h.symm
            simp [hne1] at hformula
            omega
        have htwo : 0 < (alphaResult (threeParts m) σ).count 2 := by
          have hpos : 0 < σ.count 3 := by rw [hjfull]; omega
          exact lt_of_lt_of_le hpos (count_alpha_ge_pred (threeParts m) σ (b := 2) (by decide))
        exact not_sep_consec hone htwo hsepR
      · have hi1 : σ.count 1 = 1 := by omega
        have hcardμ : (threeParts m).card = m + 1 := by
          unfold threeParts
          simp
        have hres : (alphaResult (threeParts m) σ).card = m + 1 := by
          rw [card_alphaResult _ _ hle h0]
          omega
        have hpos : 0 < (alphaResult (threeParts m) σ).count (m + 1) := by
          have hc : σ.card = m + 1 := by omega
          simpa [hc] using pos_count_of_card (threeParts m) σ (by omega : 0 < σ.card)
        have hzeroR : (alphaResult (threeParts m) σ).count 0 = 0 :=
          count_alpha_zero _ _ h0 hle (by omega)
        have hiff := omega_separated_iff hzeroR hsepR
          (by simpa [hres] : 1 < (alphaResult (threeParts m) σ).card)
        have hbad := hiff.mp hΩ
        have : (alphaResult (threeParts m) σ).count (m + 1) = 0 := by
          simpa [hres] using hbad.1
        omega

/-! ### The two exceptional witnesses -/

def parts18 : Multiset ℕ := {1} + Multiset.replicate 2 5 + {7}

def parts20 : Multiset ℕ := Multiset.replicate 2 4 + Multiset.replicate 2 6

lemma count18 (b : ℕ) :
    parts18.count b = (if b = 1 then 1 else 0) + (if b = 5 then 2 else 0) +
      (if b = 7 then 1 else 0) := by
  unfold parts18
  simp only [Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton, eq_comm]

lemma count20 (b : ℕ) :
    parts20.count b = (if b = 4 then 2 else 0) + (if b = 6 then 2 else 0) := by
  unfold parts20
  simp only [Multiset.count_add, Multiset.count_replicate, eq_comm]

theorem exception18_immediateLoss : ImmediateLoss parts18 := by
  have hcount := count18
  have c1 : parts18.count 1 = 1 := by rw [hcount]; decide
  have c5 : parts18.count 5 = 2 := by rw [hcount]; decide
  have c7 : parts18.count 7 = 1 := by rw [hcount]; decide
  have cne {b : ℕ} (h1 : b ≠ 1) (h5 : b ≠ 5) (h7 : b ≠ 7) : parts18.count b = 0 := by
    rw [hcount]; simp [h1, h5, h7]
  have h0 : parts18.count 0 = 0 := cne (by decide) (by decide) (by decide)
  have hsepμ : Separated parts18 := by
    intro a
    by_cases h1 : a = 1
    · subst h1
      exact Or.inr (cne (by decide) (by decide) (by decide))
    · by_cases h5 : a = 5
      · subst h5
        exact Or.inr (cne (by decide) (by decide) (by decide))
      · by_cases h7 : a = 7
        · subst h7
          exact Or.inr (cne (by decide) (by decide) (by decide))
        · exact Or.inl (cne h1 h5 h7)
  refine ⟨h0, hsepμ, ?_⟩
  intro σ hlegal
  rcases hlegal with ⟨hle, hne, hneq, hsepR, hΩ⟩
  have hi : σ.count 1 ≤ 1 := by
    have hle' := (Multiset.le_iff_count.mp hle) 1
    rwa [c1] at hle'
  have hj : σ.count 5 ≤ 2 := by
    have hle' := (Multiset.le_iff_count.mp hle) 5
    rwa [c5] at hle'
  have hk : σ.count 7 ≤ 1 := by
    have hle' := (Multiset.le_iff_count.mp hle) 7
    rwa [c7] at hle'
  have hother (a : ℕ) (ha : a ≠ 1) (hb : a ≠ 5) (hc : a ≠ 7) : σ.count a = 0 := by
    have hle' := (Multiset.le_iff_count.mp hle) a
    rw [cne ha hb hc] at hle'
    exact Nat.eq_zero_of_le_zero hle'
  have hmem : ∀ a ∈ σ, a = 1 ∨ a = 5 ∨ a = 7 := by
    intro a ha
    by_contra hnot
    push Not at hnot
    exact (Multiset.count_pos.mpr ha).ne' (hother a hnot.1 hnot.2.1 hnot.2.2)
  have hsup : ∀ a ∈ σ, a ∈ ({1, 5, 7} : Finset ℕ) := by
    intro a ha
    rcases hmem a ha with rfl | rfl | rfl <;> simp
  have hsumc := Multiset.sum_count_eq_card (s := ({1, 5, 7} : Finset ℕ)) hsup
  have htriple : ∑ a ∈ ({1, 5, 7} : Finset ℕ), σ.count a =
      σ.count 1 + σ.count 5 + σ.count 7 := by
    simp [Finset.sum_insert, Finset.sum_singleton, Nat.add_assoc]
  have hcard : σ.card = σ.count 1 + σ.count 5 + σ.count 7 := by omega
  match h1 : σ.count 1, h5 : σ.count 5, h7 : σ.count 7 with
  | _, 1, _ =>
      have hpred : 0 < (alphaResult parts18 σ).count 4 :=
        lt_of_lt_of_le (by rw [h5]; decide : 0 < σ.count 5)
          (count_alpha_ge_pred parts18 σ (b := 4) (by decide))
      have hkeep : 0 < (alphaResult parts18 σ).count 5 := by
        have hge := count_alpha_ge_kept parts18 σ (b := 5) (by decide)
        have hge' : 1 ≤ (alphaResult parts18 σ).count 5 := by
          simpa [c5, h5] using hge
        exact lt_of_lt_of_le (by decide : 0 < 1) hge'
      exact not_sep_consec hpred hkeep hsepR
  | 1, 0, 0 =>
      have hσ : σ = {1} := by
        ext a
        simp only [Multiset.count_singleton]
        by_cases ha : a = 1
        · simp [ha, h1]
        · have : σ.count a = 0 := by
            by_cases h5a : a = 5
            · simp [h5a, h5]
            · by_cases h7a : a = 7
              · simp [h7a, h7]
              · exact hother a ha h5a h7a
          simp [ha, this]
      exact hneq (by simpa [hσ] using alpha_select_one parts18 (by simpa [hσ] using hle))
  | 0, 0, 0 =>
      exact hne (Multiset.card_eq_zero.mp (by omega))
  | 0, 0, 1 =>
      have h5c : 0 < (alphaResult parts18 σ).count 5 := by
        have hge := count_alpha_ge_kept parts18 σ (b := 5) (by decide)
        exact lt_of_lt_of_le (by decide : 0 < 2) (by simpa [c5, h5] using hge)
      have h6c : 0 < (alphaResult parts18 σ).count 6 :=
        lt_of_lt_of_le (by rw [h7]; decide : 0 < σ.count 7)
          (count_alpha_ge_pred parts18 σ (b := 6) (by decide))
      exact not_sep_consec h5c h6c hsepR
  | 1, 0, 1 =>
      have h5c : 0 < (alphaResult parts18 σ).count 5 := by
        have hge := count_alpha_ge_kept parts18 σ (b := 5) (by decide)
        exact lt_of_lt_of_le (by decide : 0 < 2) (by simpa [c5, h5] using hge)
      have h6c : 0 < (alphaResult parts18 σ).count 6 :=
        lt_of_lt_of_le (by rw [h7]; decide : 0 < σ.count 7)
          (count_alpha_ge_pred parts18 σ (b := 6) (by decide))
      exact not_sep_consec h5c h6c hsepR
  | 0, 2, 0 =>
      have h1c : 0 < (alphaResult parts18 σ).count 1 := by
        have hformula := alpha_count parts18 σ (b := 1) (by decide)
        have hσ2 : σ.count 2 = 0 := hother 2 (by decide) (by decide) (by decide)
        rw [c1, h1, hσ2, show σ.card = 2 by omega] at hformula
        simp at hformula
        omega
      have h2c : 0 < (alphaResult parts18 σ).count 2 := by
        have hformula := alpha_count parts18 σ (b := 2) (by decide)
        have hσ2 : σ.count 2 = 0 := hother 2 (by decide) (by decide) (by decide)
        have hσ3 : σ.count 3 = 0 := hother 3 (by decide) (by decide) (by decide)
        have hμ2 : parts18.count 2 = 0 := cne (by decide) (by decide) (by decide)
        rw [hμ2, hσ2, hσ3, show σ.card = 2 by omega] at hformula
        simp at hformula
        omega
      exact not_sep_consec h1c h2c hsepR
  | 1, 2, 0 =>
      have h3c : 0 < (alphaResult parts18 σ).count 3 := by
        have hformula := alpha_count parts18 σ (b := 3) (by decide)
        have hσ3 : σ.count 3 = 0 := hother 3 (by decide) (by decide) (by decide)
        have hσ4 : σ.count 4 = 0 := hother 4 (by decide) (by decide) (by decide)
        have hμ3 : parts18.count 3 = 0 := cne (by decide) (by decide) (by decide)
        rw [hμ3, hσ3, hσ4, show σ.card = 3 by omega] at hformula
        simp at hformula
        omega
      have h4c : 0 < (alphaResult parts18 σ).count 4 :=
        lt_of_lt_of_le (by rw [h5]; decide : 0 < σ.count 5)
          (count_alpha_ge_pred parts18 σ (b := 4) (by decide))
      exact not_sep_consec h3c h4c hsepR
  | 0, 2, 1 =>
      have h3c : 0 < (alphaResult parts18 σ).count 3 := by
        have hformula := alpha_count parts18 σ (b := 3) (by decide)
        have hσ3 : σ.count 3 = 0 := hother 3 (by decide) (by decide) (by decide)
        have hσ4 : σ.count 4 = 0 := hother 4 (by decide) (by decide) (by decide)
        have hμ3 : parts18.count 3 = 0 := cne (by decide) (by decide) (by decide)
        rw [hμ3, hσ3, hσ4, show σ.card = 3 by omega] at hformula
        simp at hformula
        omega
      have h4c : 0 < (alphaResult parts18 σ).count 4 :=
        lt_of_lt_of_le (by rw [h5]; decide : 0 < σ.count 5)
          (count_alpha_ge_pred parts18 σ (b := 4) (by decide))
      exact not_sep_consec h3c h4c hsepR
  | 1, 2, 1 =>
      have hcardμ : parts18.card = 4 := by unfold parts18; simp
      have hres : (alphaResult parts18 σ).card = 4 := by
        rw [card_alphaResult _ _ hle h0]
        omega
      have hpos : 0 < (alphaResult parts18 σ).count 4 := by
        have hc : σ.card = 4 := by omega
        simpa [hc] using pos_count_of_card parts18 σ (by omega)
      have hzeroR : (alphaResult parts18 σ).count 0 = 0 :=
        count_alpha_zero _ _ h0 hle (by omega)
      have hiff := omega_separated_iff hzeroR hsepR (by omega : 1 < (alphaResult parts18 σ).card)
      have hbad := hiff.mp hΩ
      rw [hres] at hbad
      omega
  | _, _ + 3, _ => omega
  | _, _, _ + 2 => omega
  | _ + 2, _, _ => omega

theorem exception20_immediateLoss : ImmediateLoss parts20 := by
  have hcount := count20
  have c4 : parts20.count 4 = 2 := by rw [hcount]; decide
  have c6 : parts20.count 6 = 2 := by rw [hcount]; decide
  have cne {b : ℕ} (h4 : b ≠ 4) (h6 : b ≠ 6) : parts20.count b = 0 := by
    rw [hcount]; simp [h4, h6]
  have h0 : parts20.count 0 = 0 := cne (by decide) (by decide)
  have hsepμ : Separated parts20 := by
    intro a
    by_cases h4 : a = 4
    · subst h4
      exact Or.inr (cne (by decide) (by decide))
    · by_cases h6 : a = 6
      · subst h6
        exact Or.inr (cne (by decide) (by decide))
      · exact Or.inl (cne h4 h6)
  refine ⟨h0, hsepμ, ?_⟩
  intro σ hlegal
  rcases hlegal with ⟨hle, hne, _, hsepR, _⟩
  have h4b : σ.count 4 ≤ 2 := by
    have hle' := (Multiset.le_iff_count.mp hle) 4
    rwa [c4] at hle'
  have h6b : σ.count 6 ≤ 2 := by
    have hle' := (Multiset.le_iff_count.mp hle) 6
    rwa [c6] at hle'
  have hother (a : ℕ) (ha : a ≠ 4) (hb : a ≠ 6) : σ.count a = 0 := by
    have hle' := (Multiset.le_iff_count.mp hle) a
    rw [cne ha hb] at hle'
    exact Nat.eq_zero_of_le_zero hle'
  have hmem : ∀ a ∈ σ, a = 4 ∨ a = 6 := by
    intro a ha
    by_contra hnot
    push Not at hnot
    exact (Multiset.count_pos.mpr ha).ne' (hother a hnot.1 hnot.2)
  have hsup : ∀ a ∈ σ, a ∈ ({4, 6} : Finset ℕ) := by
    intro a ha
    rcases hmem a ha with rfl | rfl <;> simp
  have hsumc := Multiset.sum_count_eq_card (s := ({4, 6} : Finset ℕ)) hsup
  have hpair : ∑ a ∈ ({4, 6} : Finset ℕ), σ.count a = σ.count 4 + σ.count 6 :=
    Finset.sum_pair (f := fun a => σ.count a) (by decide : 4 ≠ 6)
  have hcard : σ.card = σ.count 4 + σ.count 6 := by omega
  match hc4 : σ.count 4, hc6 : σ.count 6 with
  | 0, 0 =>
      exact hne (Multiset.card_eq_zero.mp (by omega))
  | 1, _ =>
      have h3 : 0 < (alphaResult parts20 σ).count 3 :=
        lt_of_lt_of_le (by rw [hc4]; decide : 0 < σ.count 4)
          (count_alpha_ge_pred parts20 σ (b := 3) (by decide))
      have h4c : 0 < (alphaResult parts20 σ).count 4 := by
        have hge := count_alpha_ge_kept parts20 σ (b := 4) (by decide)
        exact lt_of_lt_of_le (by decide : 0 < 1) (by simpa [c4, hc4] using hge)
      exact not_sep_consec h3 h4c hsepR
  | _, 1 =>
      have h5 : 0 < (alphaResult parts20 σ).count 5 :=
        lt_of_lt_of_le (by rw [hc6]; decide : 0 < σ.count 6)
          (count_alpha_ge_pred parts20 σ (b := 5) (by decide))
      have h6c : 0 < (alphaResult parts20 σ).count 6 := by
        have hge := count_alpha_ge_kept parts20 σ (b := 6) (by decide)
        exact lt_of_lt_of_le (by decide : 0 < 1) (by simpa [c6, hc6] using hge)
      exact not_sep_consec h5 h6c hsepR
  | 0, 2 =>
      have h4c : 0 < (alphaResult parts20 σ).count 4 := by
        have hge := count_alpha_ge_kept parts20 σ (b := 4) (by decide)
        exact lt_of_lt_of_le (by decide : 0 < 2) (by simpa [c4, hc4] using hge)
      have h5 : 0 < (alphaResult parts20 σ).count 5 :=
        lt_of_lt_of_le (by rw [hc6]; decide : 0 < σ.count 6)
          (count_alpha_ge_pred parts20 σ (b := 5) (by decide))
      exact not_sep_consec h4c h5 hsepR
  | 2, 0 =>
      have h2 : 0 < (alphaResult parts20 σ).count 2 := by
        have hformula := alpha_count parts20 σ (b := 2) (by decide)
        have hσ2 : σ.count 2 = 0 := hother 2 (by decide) (by decide)
        have hσ3 : σ.count 3 = 0 := hother 3 (by decide) (by decide)
        have hμ2 : parts20.count 2 = 0 := cne (by decide) (by decide)
        rw [hμ2, hσ2, hσ3, show σ.card = 2 by omega] at hformula
        simp at hformula
        omega
      have h3 : 0 < (alphaResult parts20 σ).count 3 :=
        lt_of_lt_of_le (by rw [hc4]; decide : 0 < σ.count 4)
          (count_alpha_ge_pred parts20 σ (b := 3) (by decide))
      exact not_sep_consec h2 h3 hsepR
  | 2, 2 =>
      have h3 : 0 < (alphaResult parts20 σ).count 3 :=
        lt_of_lt_of_le (by rw [hc4]; decide : 0 < σ.count 4)
          (count_alpha_ge_pred parts20 σ (b := 3) (by decide))
      have h4c : 0 < (alphaResult parts20 σ).count 4 := by
        have hformula := alpha_count parts20 σ (b := 4) (by decide)
        have hσ5 : σ.count 5 = 0 := hother 5 (by decide) (by decide)
        have hμ4 : parts20.count 4 = 2 := c4
        rw [hμ4, hc4, hσ5, show σ.card = 4 by omega] at hformula
        simp at hformula
        omega
      exact not_sep_consec h3 h4c hsepR
  | 0, _ + 3 => omega
  | 2, _ + 3 => omega
  | _ + 3, _ => omega

/-! ### Block construction -/

def tri (h : ℕ) : ℕ := h * (h + 1) / 2

lemma two_mul_tri (h : ℕ) : 2 * tri h = h * (h + 1) := by
  unfold tri
  exact Nat.mul_div_cancel' (even_iff_two_dvd.mp (even_mul_succ_self h))

lemma tri_le_mul (h r : ℕ) (hhr : h + 1 ≤ r) : tri h ≤ h * r := by
  have e := two_mul_tri h
  have hineq : h * (h + 1) ≤ h * r := Nat.mul_le_mul_left h hhr
  rw [← e] at hineq
  omega

def upper (r h : ℕ) : ℕ := h * r - tri h

lemma tri_add_tri_le (h r : ℕ) (hr : h + 2 ≤ r) :
    tri h + tri (h + 1) ≤ h * r + 1 := by
  have e1 : 2 * tri h = h * (h + 1) := two_mul_tri h
  have e2 : 2 * tri (h + 1) = (h + 1) * (h + 2) := two_mul_tri (h + 1)
  have hsum : tri h + tri (h + 1) = (h + 1) * (h + 1) := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
    rw [Nat.mul_add, e1, e2]
    ring
  rw [hsum]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hr
  ring_nf
  omega

lemma tri_succ_le_upper (r h : ℕ) (hr : h + 2 ≤ r) :
    tri (h + 1) ≤ upper r h + 1 := by
  have hsum := tri_add_tri_le h r hr
  have htri : tri h ≤ h * r := tri_le_mul h r (by omega)
  have hle : tri (h + 1) + tri h ≤ h * r + 1 := by
    simpa [Nat.add_comm] using hsum
  have hsub : tri (h + 1) ≤ h * r + 1 - tri h :=
    (Nat.le_sub_iff_add_le (by omega : tri h ≤ h * r + 1)).mpr hle
  have heq : h * r - tri h + 1 = h * r + 1 - tri h := by
    obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le htri
    rw [hs]
    simp [Nat.add_assoc]
  simpa [upper, heq] using hsub

lemma cover_heights (r : ℕ) :
    ∀ h K, h < r → K ≤ upper r h → ∃ i, i ≤ h ∧ tri i ≤ K ∧ K ≤ upper r i := by
  intro h
  induction h with
  | zero =>
      intro K _ hK
      refine ⟨0, le_rfl, ?_, ?_⟩
      · simp [tri]
      · simpa [upper, tri] using hK
  | succ h ih =>
      intro K hr hK
      by_cases hle : K ≤ upper r h
      · obtain ⟨i, hi, h1, h2⟩ := ih K (Nat.lt_of_succ_lt hr) hle
        exact ⟨i, hi.trans (Nat.le_succ _), h1, h2⟩
      · refine ⟨h + 1, le_rfl, ?_, hK⟩
        have hlt : upper r h < K := Nat.lt_of_not_ge hle
        have hstep : tri (h + 1) ≤ upper r h + 1 :=
          tri_succ_le_upper r h (by omega)
        omega

lemma upper_pred (r : ℕ) (hr : 1 ≤ r) : upper r (r - 1) = tri (r - 1) := by
  have e := two_mul_tri (r - 1)
  have hadd : (r - 1) + 1 = r := by omega
  have hmul : 2 * tri (r - 1) = (r - 1) * r := by
    simpa [hadd] using e
  unfold upper
  have hle : tri (r - 1) ≤ (r - 1) * r := by omega
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hle
  have hs' : s = tri (r - 1) := by omega
  simpa [hs, hs']

lemma tri_pred (r : ℕ) (hr : 1 ≤ r) : tri (r - 1) = r * (r - 1) / 2 := by
  unfold tri
  have hadd : (r - 1) + 1 = r := by omega
  rw [hadd, Nat.mul_comm]

lemma exists_height (r K : ℕ) (hr : 1 ≤ r) (hK : K ≤ r * (r - 1) / 2) :
    ∃ h, h < r ∧ tri h ≤ K ∧ K ≤ upper r h := by
  have hupper : K ≤ upper r (r - 1) := by
    rw [upper_pred r hr, tri_pred r hr]
    exact hK
  obtain ⟨h, hh, h1, h2⟩ := cover_heights r (r - 1) K (by omega) hupper
  exact ⟨h, by omega, h1, h2⟩

def extraList (h t E : ℕ) : List ℕ :=
  if h = 0 then
    List.replicate t 0
  else
    List.replicate (E / h) h ++
      (if E % h = 0 then [] else [E % h]) ++
      List.replicate (t - E / h - (if E % h = 0 then 0 else 1)) 0

lemma extraList_spec (h t E : ℕ) (hE : E ≤ h * t) (hzero : h = 0 → E = 0) :
    (extraList h t E).length = t ∧ (extraList h t E).sum = E ∧
      ∀ x ∈ extraList h t E, x ≤ h := by
  by_cases h0 : h = 0
  · have hE0 : E = 0 := hzero h0
    simp [extraList, h0, hE0, List.mem_replicate]
  · have hpos : 0 < h := by omega
    set q := E / h
    set rem := E % h
    have hmod : q * h + rem = E := by
      simpa [q, rem, Nat.mul_comm] using Nat.div_add_mod E h
    have hrem : rem < h := Nat.mod_lt _ hpos
    have hq : q ≤ t := by
      have hmul : q * h ≤ h * t := by
        calc
          q * h ≤ E := by
            have : q * h ≤ q * h + rem := Nat.le_add_right _ _
            omega
          _ ≤ h * t := hE
      have : h * q ≤ h * t := by simpa [Nat.mul_comm] using hmul
      exact Nat.le_of_mul_le_mul_left this hpos
    set flag := if rem = 0 then 0 else 1
    have hqflag : q + flag ≤ t := by
      by_cases hrem0 : rem = 0
      · simp [flag, hrem0, hq]
      · have hflag : flag = 1 := by simp [flag, hrem0]
        have hqlt : q + 1 ≤ t := by
          have hne : q ≠ t := by
            intro hqt
            have hsumE : t * h + rem = E := by
              rw [← hmod, hqt, Nat.mul_comm]
            have hle : t * h + rem ≤ t * h := by
              calc
                t * h + rem = E := hsumE
                _ ≤ h * t := hE
                _ = t * h := Nat.mul_comm _ _
            exact hrem0 (Nat.eq_zero_of_le_zero (Nat.le_of_add_le_add_left hle))
          exact Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hq hne)
        simp [hflag, hqlt]
    have hlenflag : (if rem = 0 then ([] : List ℕ) else [rem]).length = flag := by
      by_cases hrem0 : rem = 0 <;> simp [flag, hrem0]
    have hsumflag : (if rem = 0 then ([] : List ℕ) else [rem]).sum = rem := by
      by_cases hrem0 : rem = 0 <;> simp [hrem0]
    have hsub : t - q - flag = t - (q + flag) := by
      exact Nat.sub_sub _ _ _
    unfold extraList
    simp only [h0, ↓reduceIte]
    constructor
    · rw [List.length_append, List.length_append, List.length_replicate, hlenflag,
        List.length_replicate, hsub]
      omega
    constructor
    · rw [List.sum_append_nat, List.sum_append_nat, List.sum_replicate_nat, hsumflag,
        List.sum_replicate_nat]
      omega
    · intro x hx
      by_cases hrem0 : rem = 0
      · have hx' : x ∈ List.replicate q h ++ List.replicate (t - q) 0 := by
          simpa [extraList, h0, hrem0, q, rem] using hx
        rw [List.mem_append] at hx'
        rcases hx' with hx' | hx'
        · obtain rfl := List.eq_of_mem_replicate hx'
          exact le_rfl
        · obtain rfl := List.eq_of_mem_replicate hx'
          exact Nat.zero_le _
      · have hx' : x ∈ List.replicate q h ++ ([rem] ++ List.replicate (t - q - 1) 0) := by
          simpa [extraList, h0, hrem0, q, rem, Nat.sub_sub] using hx
        rw [List.mem_append] at hx'
        rcases hx' with hx' | hx'
        · obtain rfl := List.eq_of_mem_replicate hx'
          exact le_rfl
        · rw [List.mem_append] at hx'
          rcases hx' with hx' | hx'
          · simp at hx'
            rcases hx' with rfl
            exact le_of_lt hrem
          · obtain rfl := List.eq_of_mem_replicate hx'
            exact Nat.zero_le _

def offsetList (r h K : ℕ) : List ℕ :=
  List.range (h + 1) ++ extraList h (r - (h + 1)) (K - tri h)

lemma sum_range_tri (n : ℕ) : (List.range (n + 1)).sum = tri n := by
  induction n with
  | zero => simp [tri]
  | succ n ih =>
      rw [List.range_succ, List.sum_append_nat, List.sum_singleton, ih]
      have h2 : 2 * (tri n + (n + 1)) = 2 * tri (n + 1) := by
        rw [Nat.mul_add, two_mul_tri, two_mul_tri]
        ring
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2

lemma offsetList_spec (r h K : ℕ) (hh : h < r) (hlo : tri h ≤ K) (hhi : K ≤ upper r h) :
    let ys := offsetList r h K
    ys.length = r ∧ ys.sum = K ∧ (∀ y ∈ ys, y ≤ h) ∧ ∀ j ≤ h, 0 < ys.count j := by
  have hhr : h + 1 ≤ r := by omega
  have htri : tri h ≤ h * r := tri_le_mul h r hhr
  have hEbound : K - tri h ≤ h * (r - (h + 1)) := by
    have hKle : K + tri h ≤ h * r := by
      have : K ≤ h * r - tri h := by simpa [upper] using hhi
      exact (Nat.le_sub_iff_add_le htri).mp this
    have hE : (K - tri h) + 2 * tri h ≤ h * r := by
      have : (K - tri h) + tri h = K := Nat.sub_add_cancel hlo
      omega
    have htwo : 2 * tri h = h * (h + 1) := two_mul_tri h
    have hdiff : h * r - h * (h + 1) = h * (r - (h + 1)) := by
      rw [← Nat.mul_sub_left_distrib]
    have : K - tri h ≤ h * r - h * (h + 1) := by
      have hsum : (K - tri h) + h * (h + 1) ≤ h * r := by simpa [htwo] using hE
      have hle' : h * (h + 1) ≤ h * r := Nat.mul_le_mul_left h hhr
      exact (Nat.le_sub_iff_add_le hle').mpr hsum
    simpa [hdiff] using this
  have hzero : h = 0 → K - tri h = 0 := by
    intro hh0
    have : tri h = 0 := by simp [hh0, tri]
    have : upper r h = 0 := by simp [upper, hh0, tri]
    omega
  have hspec := extraList_spec h (r - (h + 1)) (K - tri h) hEbound hzero
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hspec.1
    simp only [offsetList, List.length_append, List.length_range] at *
    omega
  · have := hspec.2.1
    rw [offsetList, List.sum_append_nat, sum_range_tri]
    omega
  · intro y hy
    rw [offsetList, List.mem_append] at hy
    rcases hy with hy | hy
    · have : y < h + 1 := List.mem_range.mp hy
      omega
    · exact hspec.2.2 y hy
  · intro j hj
    have hj' : j < h + 1 := by omega
    have hrange : (List.range (h + 1)).count j = 1 := by simp [List.count_range, hj']
    rw [offsetList, List.count_append]
    omega

def partSize (a y : ℕ) : ℕ := a + 2 * y

lemma partSize_injective (a : ℕ) : Function.Injective (partSize a) := by
  intro y1 y2 h
  unfold partSize at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (Nat.add_left_cancel h)

def fromOffsets (a : ℕ) (ys : List ℕ) : Multiset ℕ :=
  (ys.map (partSize a) : Multiset ℕ)

lemma count_fromOffsets (a : ℕ) (ys : List ℕ) (j : ℕ) :
    (fromOffsets a ys).count (partSize a j) = ys.count j := by
  unfold fromOffsets
  rw [Multiset.coe_count]
  simpa using List.count_map_of_injective ys (partSize a) (partSize_injective a) j

lemma count_fromOffsets_other (a : ℕ) (ys : List ℕ) (h : ℕ)
    (hys : ∀ y ∈ ys, y ≤ h) {b : ℕ} (hb : ∀ j ≤ h, b ≠ partSize a j) :
    (fromOffsets a ys).count b = 0 := by
  unfold fromOffsets
  rw [Multiset.coe_count, List.count_eq_zero]
  intro hbmem
  rw [List.mem_map] at hbmem
  obtain ⟨y, hy, rfl⟩ := hbmem
  exact hb y (hys y hy) rfl

lemma sum_map_partSize (a : ℕ) : ∀ ys : List ℕ,
    (ys.map (partSize a)).sum = ys.length * a + 2 * ys.sum
  | [] => by simp [partSize]
  | y :: ys => by
      rw [List.map_cons, List.sum_cons, List.length_cons, sum_map_partSize a ys, partSize,
        List.sum_cons]
      ring

lemma sum_fromOffsets (a : ℕ) (ys : List ℕ) :
    (fromOffsets a ys).sum = ys.length * a + 2 * ys.sum := by
  unfold fromOffsets
  rw [Multiset.sum_coe, sum_map_partSize]

lemma card_fromOffsets (a : ℕ) (ys : List ℕ) : (fromOffsets a ys).card = ys.length := by
  unfold fromOffsets
  rw [Multiset.coe_card, List.length_map]

theorem block_immediateLoss (r δ : ℕ) (ys : List ℕ) (h : ℕ)
    (hr : 2 ≤ r) (hδ : δ = 0 ∨ δ = 1) (hlen : ys.length = r) (hh : h < r)
    (hbound : ∀ y ∈ ys, y ≤ h) (hcover : ∀ j ≤ h, 0 < ys.count j) :
    ImmediateLoss (fromOffsets (r + 2 + 2 * δ) ys) := by
  set a := r + 2 + 2 * δ
  set μ := fromOffsets a ys
  have ha : 4 ≤ a := by
    rcases hδ with rfl | rfl <;> omega
  have hcount0 : ∀ j ≤ h, μ.count (partSize a j) = ys.count j := fun j _ =>
    count_fromOffsets a ys j
  have hother : ∀ b, (∀ j ≤ h, b ≠ partSize a j) → μ.count b = 0 :=
    fun b hb => count_fromOffsets_other a ys h hbound hb
  have h0 : μ.count 0 = 0 := by
    apply hother
    intro j hj
    unfold partSize
    omega
  have hsepμ : Separated μ := by
    intro b
    by_cases hb : μ.count b = 0
    · exact Or.inl hb
    · right
      by_contra hpos
      have hb' : 0 < μ.count b := by omega
      have hb1 : 0 < μ.count (b + 1) := by omega
      have hbmem : ∃ j ≤ h, b = partSize a j := by
        by_contra hnot
        push Not at hnot
        exact hb'.ne' (hother b hnot)
      have hb1mem : ∃ k ≤ h, b + 1 = partSize a k := by
        by_contra hnot
        push Not at hnot
        exact hb1.ne' (hother (b + 1) hnot)
      obtain ⟨j, _, rfl⟩ := hbmem
      obtain ⟨k, _, hk⟩ := hb1mem
      unfold partSize at hk
      omega
  refine ⟨h0, hsepμ, ?_⟩
  intro σ hlegal
  rcases hlegal with ⟨hle, hne, _, hsepR, hΩ⟩
  have hleCount (b) : σ.count b ≤ μ.count b := (Multiset.le_iff_count.mp hle) b
  have hbin (j : ℕ) (hj : j ≤ h) :
      σ.count (partSize a j) = 0 ∨ σ.count (partSize a j) = μ.count (partSize a j) := by
    have hle' := hleCount (partSize a j)
    by_cases hlt : σ.count (partSize a j) < μ.count (partSize a j)
    · left
      by_contra hne0
      have hpos' : 0 < σ.count (partSize a j) := Nat.pos_of_ne_zero hne0
      have hsize : 1 ≤ partSize a j := by unfold partSize; omega
      have hsumj : (partSize a j - 1) + 1 = partSize a j := Nat.sub_add_cancel hsize
      have hpred : 0 < (alphaResult μ σ).count (partSize a j - 1) := by
        have hgt : 1 < partSize a j := by unfold partSize; omega
        have hge := count_alpha_ge_pred μ σ (b := partSize a j - 1) (Nat.sub_pos_of_lt hgt)
        exact lt_of_lt_of_le hpos' (by simpa [hsumj] using hge)
      have hkeep : 0 < (alphaResult μ σ).count (partSize a j) := by
        have hge := count_alpha_ge_kept μ σ (b := partSize a j) (by unfold partSize; omega)
        have hc := hcount0 j hj
        have hcoverj := hcover j hj
        have hgap : 0 < μ.count (partSize a j) - σ.count (partSize a j) :=
          Nat.sub_pos_of_lt (by simpa [hc] using hlt)
        exact lt_of_lt_of_le hgap (by simpa [hc] using hge)
      exact not_sep_consec hpred (by simpa [hsumj] using hkeep) hsepR
    · right
      exact le_antisymm hle' (le_of_not_gt hlt)
  by_cases hpartial : ∃ j ≤ h, 0 < σ.count (partSize a j) ∧
      σ.count (partSize a j) < μ.count (partSize a j)
  · obtain ⟨j, hj, hpos, hlt⟩ := hpartial
    have hsize : 1 ≤ partSize a j := by unfold partSize; omega
    have hsumj : (partSize a j - 1) + 1 = partSize a j := Nat.sub_add_cancel hsize
    have hpred : 0 < (alphaResult μ σ).count (partSize a j - 1) := by
      have hge := count_alpha_ge_pred μ σ (b := partSize a j - 1)
        (Nat.sub_pos_of_lt (by unfold partSize; omega))
      exact lt_of_lt_of_le hpos (by simpa [hsumj] using hge)
    have hkeep : 0 < (alphaResult μ σ).count (partSize a j) := by
      have hge := count_alpha_ge_kept μ σ (b := partSize a j) (by unfold partSize; omega)
      have hc := hcount0 j hj
      have hgap : 0 < μ.count (partSize a j) - σ.count (partSize a j) :=
        Nat.sub_pos_of_lt (by simpa [hc] using hlt)
      exact lt_of_lt_of_le hgap (by simpa [hc] using hge)
    exact not_sep_consec hpred (by simpa [hsumj] using hkeep) hsepR
  · push Not at hpartial
    have hfull_or_zero (j : ℕ) (hj : j ≤ h) :
        σ.count (partSize a j) = 0 ∨ σ.count (partSize a j) = ys.count j := by
      rcases hbin j hj with hzero | heq
      · exact Or.inl hzero
      · right
        rw [← hcount0 j hj]
        exact heq
    by_cases hfull0 : σ.count (partSize a 0) = μ.count (partSize a 0)
    · have hpos0 : 0 < σ.count a := by
        have hc := hcount0 0 (Nat.zero_le _)
        have hy := hcover 0 (Nat.zero_le _)
        have hfull : σ.count (partSize a 0) = ys.count 0 := by
          rw [hfull0, hc]
        simpa [partSize] using (hfull.symm ▸ hy)
      have hsumA : (a - 1) + 1 = a := Nat.sub_add_cancel (by omega)
      have hpred : 0 < (alphaResult μ σ).count (a - 1) := by
        have hge := count_alpha_ge_pred μ σ (b := a - 1) (by omega)
        exact lt_of_lt_of_le hpos0 (by simpa [hsumA] using hge)
      have hμ1 : μ.count 1 = 0 := by
        apply hother
        intro j hj heq
        unfold partSize at heq
        omega
      have hσ1 : σ.count 1 = 0 := by
        have hle1 := hleCount 1
        rw [hμ1] at hle1
        exact Nat.eq_zero_of_le_zero hle1
      have hresCard : (alphaResult μ σ).card = r + 1 := by
        rw [card_alphaResult _ _ hle h0, card_fromOffsets, hlen, hσ1]
        omega
      have hzeroR : (alphaResult μ σ).count 0 = 0 :=
        count_alpha_zero _ _ h0 hle (by
          have : 0 < σ.card := by
            have : 0 < σ.count a := hpos0
            exact lt_of_lt_of_le this (Multiset.countP_le_card _ σ)
          omega)
      have hiff := omega_separated_iff hzeroR hsepR (by omega : 1 < (alphaResult μ σ).card)
      have hbad := hiff.mp hΩ
      rcases hδ with rfl | rfl
      · have ha1 : a - 1 = r + 1 := by
          dsimp [a]
        exact not_lt_of_ge (le_of_eq hbad.1) (by simpa [hresCard, ha1] using hpred)
      · have ha1 : a - 1 = r + 1 + 2 := by
          dsimp [a]
        exact not_lt_of_ge (le_of_eq hbad.2) (by simpa [hresCard, ha1] using hpred)
    · have hzero0 : σ.count (partSize a 0) = 0 := by
        rcases hfull_or_zero 0 (by omega) with hzero | heq
        · exact hzero
        · have hc := hcount0 0 (by omega)
          exact (hfull0 (by simpa [hc] using heq)).elim
      classical
      let P : ℕ → Prop := fun j =>
        j ≤ h ∧ σ.count (partSize a j) = μ.count (partSize a j) ∧ 0 < μ.count (partSize a j)
      have hex : ∃ j, P j := by
        obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero hne
        have hbcount : 0 < σ.count b := Multiset.count_pos.mpr hb
        have hbform : ∃ k ≤ h, b = partSize a k := by
          by_contra hnot
          push Not at hnot
          have : μ.count b = 0 := hother b hnot
          have : σ.count b = 0 := by
            have := hleCount b
            omega
          omega
        obtain ⟨k, hk, rfl⟩ := hbform
        have heq : σ.count (partSize a k) = μ.count (partSize a k) := by
          rcases hbin k hk with hzero | heq
          · omega
          · exact heq
        have hposμ : 0 < μ.count (partSize a k) := by
          have := hcover k hk
          simpa [hcount0 k hk] using this
        exact ⟨k, hk, heq, hposμ⟩
      let j := Nat.find hex
      have hj := Nat.find_spec hex
      have hmin : ∀ i, i < j → ¬ P i := fun i hi => Nat.find_min hex hi
      have hjpos : 1 ≤ j := by
        by_contra hlt
        have h0 : j = 0 := by omega
        have hfind : Nat.find hex = 0 := by simpa [j] using h0
        exact hfull0 (hfind ▸ hj).2.1
      have hpred_index : j - 1 < j := by omega
      have hnot : ¬ P (j - 1) := hmin _ hpred_index
      have hpredle : j - 1 ≤ h := by omega
      have hpredcount : σ.count (partSize a (j - 1)) = 0 := by
        have hposμ : 0 < μ.count (partSize a (j - 1)) := by
          simpa [hcount0 (j - 1) hpredle] using hcover (j - 1) hpredle
        have hnoteq : σ.count (partSize a (j - 1)) ≠ μ.count (partSize a (j - 1)) := by
          intro hEq
          exact hnot ⟨hpredle, hEq, hposμ⟩
        rcases hfull_or_zero (j - 1) hpredle with hzero | heq
        · exact hzero
        · exact (hnoteq (by
            have hc := hcount0 (j - 1) hpredle
            simpa [hc] using heq)).elim
      have hsmall : 0 < (alphaResult μ σ).count (partSize a (j - 1)) := by
        have hge := count_alpha_ge_kept μ σ (b := partSize a (j - 1))
          (by unfold partSize; omega)
        have hc := hcount0 (j - 1) hpredle
        have hy := hcover (j - 1) hpredle
        have hposμ : 0 < μ.count (partSize a (j - 1)) := by simpa [hc] using hy
        have hge' : μ.count (partSize a (j - 1)) ≤
            (alphaResult μ σ).count (partSize a (j - 1)) := by
          simpa [hpredcount, hc] using hge
        exact lt_of_lt_of_le hposμ hge'
      have hbig : 0 < (alphaResult μ σ).count (partSize a j - 1) := by
        have hsize : 1 ≤ partSize a j := by unfold partSize; omega
        have hsumj : (partSize a j - 1) + 1 = partSize a j := Nat.sub_add_cancel hsize
        have hposμ : 0 < μ.count (partSize a j) := by
          simpa [hcount0 j hj.1] using hcover j hj.1
        have hposσ : 0 < σ.count (partSize a j) := by
          have heq : σ.count (partSize a j) = μ.count (partSize a j) := hj.2.1
          exact heq.symm ▸ hposμ
        have hgt : 1 < partSize a j := by unfold partSize; omega
        have hge := count_alpha_ge_pred μ σ (b := partSize a j - 1) (Nat.sub_pos_of_lt hgt)
        exact lt_of_lt_of_le hposσ (by simpa [hsumj] using hge)
      have hadj : partSize a (j - 1) + 1 = partSize a j - 1 := by
        unfold partSize
        omega
      exact not_sep_consec hsmall (by simpa [hadj] using hbig) hsepR

lemma block_sum (r δ : ℕ) (ys : List ℕ) (K : ℕ) (hlen : ys.length = r) (hsum : ys.sum = K) :
    (fromOffsets (r + 2 + 2 * δ) ys).sum = r * (r + 2 + 2 * δ) + 2 * K := by
  rw [sum_fromOffsets, hlen, hsum]

lemma exists_block (r δ K : ℕ) (hr : 2 ≤ r) (hδ : δ = 0 ∨ δ = 1)
    (hK : K ≤ r * (r - 1) / 2) :
    ∃ μ : Multiset ℕ, μ.sum = r * (r + 2 + 2 * δ) + 2 * K ∧ ImmediateLoss μ := by
  obtain ⟨h, hh, hlo, hhi⟩ := exists_height r K (by omega) hK
  have hspec := offsetList_spec r h K hh hlo hhi
  set ys := offsetList r h K
  refine ⟨fromOffsets (r + 2 + 2 * δ) ys, ?_, ?_⟩
  · exact block_sum r δ ys K hspec.1 hspec.2.1
  · exact block_immediateLoss r δ ys h hr hδ hspec.1 hh hspec.2.2.1 hspec.2.2.2

lemma exists_of_block (n r δ K : ℕ) (hn : n = r * (r + 2 + 2 * δ) + 2 * K)
    (hr : 2 ≤ r) (hδ : δ = 0 ∨ δ = 1) (hK : K ≤ r * (r - 1) / 2) :
    ∃ μ : Multiset ℕ, μ.sum = n ∧ ImmediateLoss μ := by
  obtain ⟨μ, hsum, him⟩ := exists_block r δ K hr hδ hK
  exact ⟨μ, by rw [hsum, hn], him⟩

lemma exists_large_even_block (n : ℕ) (hn : 48 ≤ n) (he : Even n) :
    ∃ μ : Multiset ℕ, μ.sum = n ∧ ImmediateLoss μ := by
  classical
  let P : ℕ → Prop := fun r => Even r ∧ r * (r + 2) ≤ n
  letI : DecidablePred P := Classical.decPred P
  let r := Nat.findGreatest P n
  have hP6 : P 6 := by
    refine ⟨⟨3, by decide⟩, by omega⟩
  have hrge : 6 ≤ r := Nat.le_findGreatest (by omega : 6 ≤ n) hP6
  have hPr : P r := Nat.findGreatest_spec (by omega : 6 ≤ n) hP6
  have hbase : r * (r + 2) ≤ n := hPr.2
  have hnle : n ≤ 2 * r * r + r := by
    by_contra hlt
    have hlt' : 2 * r * r + r < n := by omega
    have he2 : Even (2 * r * r) := by
      simpa [Nat.mul_assoc] using even_two_mul (r * r)
    have heR : Even (2 * r * r + r) := Even.add he2 hPr.1
    have hstep : 2 * r * r + r + 2 ≤ n := by
      have : 2 * r * r + r + 1 < n := add_one_lt_of_even heR he hlt'
      omega
    have hmul : (r + 2) * (r + 4) ≤ 2 * r * r + r + 2 := by
      zify
      nlinarith
    have hmuln : (r + 2) * (r + 4) ≤ n := le_trans hmul hstep
    have hr2 : r + 2 ≤ n := by
      have : r + 2 ≤ (r + 4) * (r + 2) := by
        calc
          r + 2 = 1 * (r + 2) := by ring
          _ ≤ (r + 4) * (r + 2) := Nat.mul_le_mul_right _ (by omega)
      exact le_trans this (by simpa [Nat.mul_comm] using hmuln)
    have hnot := Nat.findGreatest_is_greatest (by omega : r < r + 2) hr2
    apply hnot
    refine ⟨Even.add hPr.1 ⟨1, by decide⟩, ?_⟩
    simpa [show (r + 2) + 2 = r + 4 by omega] using hmuln
  set K := (n - r * (r + 2)) / 2
  have hbase_even : Even (r * (r + 2)) := even_mul.mpr (Or.inl hPr.1)
  have hdiff_even : Even (n - r * (r + 2)) :=
    (even_sub hbase).mpr (iff_of_true he hbase_even)
  have hK2 : 2 * K = n - r * (r + 2) := two_mul_div_two_of_even hdiff_even
  have hKbound : K ≤ r * (r - 1) / 2 := by
    have hle : n - r * (r + 2) ≤ r * (r - 1) := by
      have hsub : r * (r - 1) = r * r - r := by
        simpa using (Nat.mul_sub_left_distrib r r 1)
      rw [Nat.sub_le_iff_le_add, hsub]
      have hrr : r ≤ r * r := by
        simpa using Nat.mul_le_mul_left r (show 1 ≤ r by omega)
      zify [hrr] at hnle ⊢
      nlinarith
    rw [Nat.le_div_iff_mul_le (by decide : 0 < 2), Nat.mul_comm]
    simpa [hK2] using hle
  have hsum : n = r * (r + 2 + 2 * 0) + 2 * K := by
    have hr0 : r * (r + 2 + 2 * 0) = r * (r + 2) := by ring
    calc
      n = r * (r + 2) + (n - r * (r + 2)) := (Nat.add_sub_of_le hbase).symm
      _ = r * (r + 2) + 2 * K := by rw [← hK2]
      _ = r * (r + 2 + 2 * 0) + 2 * K := by rw [hr0]
  exact exists_of_block n r 0 K hsum (by omega) (Or.inl rfl) hKbound

lemma exists_small_even_block (n : ℕ) (hn : 6 < n) (he : Even n) (h18 : n ≠ 18)
    (h20 : n ≠ 20) (h4 : n % 6 ≠ 4) (h48 : n < 48) :
    ∃ μ : Multiset ℕ, μ.sum = n ∧ ImmediateLoss μ := by
  have he2 : n % 2 = 0 := even_iff.mp he
  have hmem : n ∈ ({8, 12, 14, 24, 26, 30, 32, 36, 38, 42, 44} : Finset ℕ) := by
    interval_cases n <;> first | omega | decide
  fin_cases hmem
  · exact exists_of_block 8 2 0 0 (by omega) (by omega) (Or.inl rfl) (by omega)
  · exact exists_of_block 12 2 1 0 (by omega) (by omega) (Or.inr rfl) (by omega)
  · exact exists_of_block 14 2 1 1 (by omega) (by omega) (Or.inr rfl) (by omega)
  · exact exists_of_block 24 4 0 0 (by omega) (by omega) (Or.inl rfl) (by omega)
  · exact exists_of_block 26 4 0 1 (by omega) (by omega) (Or.inl rfl) (by omega)
  · exact exists_of_block 30 4 0 3 (by omega) (by omega) (Or.inl rfl) (by omega)
  · exact exists_of_block 32 4 0 4 (by omega) (by omega) (Or.inl rfl) (by omega)
  · exact exists_of_block 36 4 0 6 (by omega) (by omega) (Or.inl rfl) (by omega)
  · exact exists_of_block 38 4 1 3 (by omega) (by omega) (Or.inr rfl) (by omega)
  · exact exists_of_block 42 4 1 5 (by omega) (by omega) (Or.inr rfl) (by omega)
  · exact exists_of_block 44 4 1 6 (by omega) (by omega) (Or.inr rfl) (by omega)

/-- Every integer `n > 6` has a Floridian-solitaire immediate loss. -/
theorem exists_immediateLoss (n : ℕ) (hn : 6 < n) :
    ∃ μ : Multiset ℕ, μ.sum = n ∧ ImmediateLoss μ := by
  rcases even_or_odd n with he | ho
  · by_cases h18 : n = 18
    · refine ⟨parts18, ?_, exception18_immediateLoss⟩
      unfold parts18
      simp [h18]
    · by_cases h20 : n = 20
      · refine ⟨parts20, ?_, exception20_immediateLoss⟩
        unfold parts20
        simp [h20]
      · by_cases h4 : n % 6 = 4
        · have h10 : 10 ≤ n := by omega
          set m := (n - 1) / 3
          have hdiv : 3 ∣ n - 1 := by
            have : (n - 1) % 3 = 0 := by omega
            exact dvd_of_mod_eq_zero this
          have hm : 3 * m = n - 1 := Nat.mul_div_cancel' hdiv
          have hm1 : 1 ≤ m := by omega
          refine ⟨threeParts m, ?_, oneAndThrees_immediateLoss m hm1⟩
          rw [three_sum, hm]
          omega
        · by_cases h48 : 48 ≤ n
          · exact exists_large_even_block n h48 he
          · exact exists_small_even_block n hn he h18 h20 h4 (by omega)
  · rcases ho with ⟨m, hm⟩
    have hm3 : 3 ≤ m := by omega
    refine ⟨oddParts m, ?_, odd_immediateLoss m hm3⟩
    rw [odd_sum, hm]

end AgenticConjectures.FloridianSolitaire
