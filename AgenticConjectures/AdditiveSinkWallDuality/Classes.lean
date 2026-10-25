import AgenticConjectures.AdditiveSinkWallDuality.Games

/-!
# Additive wall and sink subtraction: the value classes

Write `P = {x | wall s₁ s₂ x = 0}` for the wall `𝒫`-positions. This file proves, from the mex
recursions alone, that every wall and sink nim-value is determined by `P`:

* `wall_eq_wallClass` (T1): `wall x` is `0, 1, 2, 3` according as `x ∈ P`, `x - s₁ ∈ P`,
  `x + s₂ ∈ P`, or none of these;
* `sink_eq_sinkClass` (T2): `sink (t + 1)` is `0, 1, 2, 3` according as `t - s₃ ∈ P`, `t ∈ P`,
  `t - s₁ ∈ P`, or none of these.

It then shows that a single gap `P ∩ [p - s₃, p) = ∅` forces `P` to be `p`-periodic
(`wall_zero_add_period`) and reflection-symmetric on `[0, p - s₃ - 1]` (`wall_zero_reflect`, T3),
and that these facts imply the duality formula modulo `p` (`conj_of_gap`).
-/

namespace AgenticConjectures.AdditiveSinkWallDuality

section soft

variable {a b : ℕ} (ha : 0 < a) (hab : a < b)
include ha hab

theorem moves_pos {s : ℕ} (hs : s ∈ moves a b) : 0 < s := by
  rcases mem_moves.1 hs with h | h | h <;> omega

omit ha in
theorem moves_ge {s : ℕ} (hs : s ∈ moves a b) : a ≤ s := by
  rcases mem_moves.1 hs with h | h | h <;> omega

omit ha hab in
theorem moves_le {s : ℕ} (hs : s ∈ moves a b) : s ≤ a + b := by
  rcases mem_moves.1 hs with h | h | h <;> omega

omit ha hab in
theorem a_mem : a ∈ moves a b := mem_moves.2 (Or.inl rfl)

omit ha hab in
theorem b_mem : b ∈ moves a b := mem_moves.2 (Or.inr (Or.inl rfl))

omit ha hab in
theorem ab_mem : a + b ∈ moves a b := mem_moves.2 (Or.inr (Or.inr rfl))

/-- (P0) A position is a wall `𝒫`-position iff none of its options is. -/
theorem wall_zero_iff (x : ℕ) :
    wall a b x = 0 ↔ ∀ s ∈ moves a b, s ≤ x → wall a b (x - s) ≠ 0 := by
  rw [wall_eq_iff ha hab]
  simp

/-- (I) No two wall `𝒫`-positions differ by a move. -/
theorem indep {u v s : ℕ} (hs : s ∈ moves a b) (hu : wall a b u = 0) (hv : wall a b v = 0)
    (h : v = u + s) : False := by
  have := (wall_zero_iff ha hab v).1 hv s hs (by omega)
  rw [show v - s = u by omega] at this
  exact this hu

/-- (D) Every wall `𝒩`-position has a `𝒫`-position as an option. -/
theorem dom {x : ℕ} (hx : wall a b x ≠ 0) :
    ∃ s ∈ moves a b, s ≤ x ∧ wall a b (x - s) = 0 := by
  by_contra h
  exact hx ((wall_zero_iff ha hab x).2 fun s hs hsx h0 => h ⟨s, hs, hsx, h0⟩)

/-- (L) The positions below `s₁` have no options. -/
theorem wall_small {x : ℕ} (hx : x < a) : wall a b x = 0 :=
  (wall_zero_iff ha hab x).2 fun s hs hsx => absurd (moves_ge hab hs) (by omega)

/-- (FD) Every wall `𝒩`-position is an option of some `𝒫`-position. -/
theorem fwd {x : ℕ} (hx : wall a b x ≠ 0) : ∃ s ∈ moves a b, wall a b (x + s) = 0 := by
  by_cases hc : wall a b (x + (a + b)) = 0
  · exact ⟨a + b, ab_mem, hc⟩
  obtain ⟨s, hs, -, h0⟩ := dom ha hab hc
  rcases mem_moves.1 hs with h | h | h <;> rw [h] at h0
  · exact ⟨b, b_mem, by rwa [show x + (a + b) - a = x + b by omega] at h0⟩
  · exact ⟨a, a_mem, by rwa [show x + (a + b) - b = x + a by omega] at h0⟩
  · exact absurd (by rwa [show x + (a + b) - (a + b) = x by omega] at h0) hx

end soft

/-- The wall value predicted by (T1). -/
def wallClass (a b x : ℕ) : ℕ :=
  if wall a b x = 0 then 0
  else if a ≤ x ∧ wall a b (x - a) = 0 then 1
  else if wall a b (x + b) = 0 then 2
  else 3

theorem wallClass_eq_one {a b y : ℕ} :
    wallClass a b y = 1 ↔ wall a b y ≠ 0 ∧ a ≤ y ∧ wall a b (y - a) = 0 := by
  unfold wallClass
  split_ifs <;> simp_all

theorem wallClass_eq_two {a b y : ℕ} :
    wallClass a b y = 2 ↔
      wall a b y ≠ 0 ∧ ¬(a ≤ y ∧ wall a b (y - a) = 0) ∧ wall a b (y + b) = 0 := by
  unfold wallClass
  split_ifs <;> simp_all

theorem wallClass_eq_three {a b y : ℕ} :
    wallClass a b y = 3 ↔
      wall a b y ≠ 0 ∧ ¬(a ≤ y ∧ wall a b (y - a) = 0) ∧ wall a b (y + b) ≠ 0 := by
  unfold wallClass
  split_ifs <;> simp_all

section T1

variable {a b : ℕ} (ha : 0 < a) (hab : a < b)
include ha hab

/-- (R3) A position of the last wall class has a `𝒫`-position `s₂ - s₁` above it. -/
theorem class3_shift {x : ℕ} (h0 : wall a b x ≠ 0) (h1 : ¬(a ≤ x ∧ wall a b (x - a) = 0))
    (h2 : wall a b (x + b) ≠ 0) : a ≤ x ∧ wall a b (x + b - a) = 0 := by
  have hax : a ≤ x := by
    by_contra h
    exact h0 (wall_small ha hab (by omega))
  refine ⟨hax, ?_⟩
  obtain ⟨s, hs, -, hP⟩ := dom ha hab h2
  rcases mem_moves.1 hs with h | h | h <;> rw [h] at hP
  · exact hP
  · rw [show x + b - b = x by omega] at hP
    exact absurd hP h0
  · rw [show x + b - (a + b) = x - a by omega] at hP
    exact absurd ⟨hax, hP⟩ h1

/-- (T1) The wall values are determined by the `𝒫`-positions: `0` on `P`, `1` on `P + s₁`,
`2` on `P - s₂`, and `3` elsewhere. -/
theorem wall_eq_wallClass (x : ℕ) : wall a b x = wallClass a b x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  have hopt : ∀ s ∈ moves a b, s ≤ x → wall a b (x - s) = wallClass a b (x - s) :=
    fun s hs _ => ih _ (by have := moves_pos ha hab hs; omega)
  -- (R1) an option of value one
  have R1 : wall a b x ≠ 0 → ¬(a ≤ x ∧ wall a b (x - a) = 0) →
      ∃ s ∈ moves a b, s ≤ x ∧ wall a b (x - s) = 1 := by
    intro h0 h1
    have hax : a ≤ x := by
      by_contra h
      exact h0 (wall_small ha hab (by omega))
    obtain ⟨s, hs, hsx, hP⟩ := dom ha hab (fun h => h1 ⟨hax, h⟩)
    refine ⟨s, hs, by omega, ?_⟩
    rw [hopt s hs (by omega), wallClass_eq_one]
    refine ⟨fun h => indep ha hab a_mem hP h (by omega), by omega, ?_⟩
    rwa [show x - s - a = x - a - s by omega]
  by_cases h0 : wall a b x = 0
  · rw [h0, wallClass, if_pos h0]
  by_cases h1 : a ≤ x ∧ wall a b (x - a) = 0
  · rw [show wallClass a b x = 1 by rw [wallClass_eq_one]; exact ⟨h0, h1⟩, wall_eq_iff ha hab]
    refine ⟨fun s hs hsx hv => ?_, fun j hj => ?_⟩
    · rw [hopt s hs hsx, wallClass_eq_one] at hv
      exact indep ha hab hs hv.2.2 h1.2 (by omega)
    · obtain rfl : j = 0 := by omega
      exact ⟨a, a_mem, h1.1, h1.2⟩
  by_cases h2 : wall a b (x + b) = 0
  · rw [show wallClass a b x = 2 by rw [wallClass_eq_two]; exact ⟨h0, h1, h2⟩, wall_eq_iff ha hab]
    refine ⟨fun s hs hsx hv => ?_, fun j hj => ?_⟩
    · rw [hopt s hs hsx, wallClass_eq_two] at hv
      exact indep ha hab hs hv.2.2 h2 (by omega)
    · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · exact dom ha hab h0
      · exact R1 h0 h1
  · rw [show wallClass a b x = 3 by rw [wallClass_eq_three]; exact ⟨h0, h1, h2⟩, wall_eq_iff ha hab]
    obtain ⟨hax, h3⟩ := class3_shift ha hab h0 h1 h2
    refine ⟨fun s hs hsx hv => ?_, fun j hj => ?_⟩
    · rw [hopt s hs hsx, wallClass_eq_three] at hv
      obtain ⟨-, h3'⟩ := class3_shift ha hab hv.1 hv.2.1 hv.2.2
      exact indep ha hab hs h3' h3 (by omega)
    · rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
      · exact dom ha hab h0
      · exact R1 h0 h1
      · refine ⟨a, a_mem, hax, ?_⟩
        rw [hopt a a_mem hax, wallClass_eq_two]
        refine ⟨fun h => h1 ⟨hax, h⟩, fun h => indep ha hab ab_mem h.2 h3 (by omega), ?_⟩
        rwa [show x - a + b = x + b - a by omega]

end T1

/-- The sink value at position `t + 1` predicted by (T2). -/
def sinkClass (a b t : ℕ) : ℕ :=
  if a + b ≤ t ∧ wall a b (t - (a + b)) = 0 then 0
  else if wall a b t = 0 then 1
  else if a ≤ t ∧ wall a b (t - a) = 0 then 2
  else 3

theorem sinkClass_eq_zero {a b t : ℕ} :
    sinkClass a b t = 0 ↔ a + b ≤ t ∧ wall a b (t - (a + b)) = 0 := by
  unfold sinkClass
  split_ifs <;> simp_all

theorem sinkClass_eq_one {a b t : ℕ} :
    sinkClass a b t = 1 ↔ ¬(a + b ≤ t ∧ wall a b (t - (a + b)) = 0) ∧ wall a b t = 0 := by
  unfold sinkClass
  split_ifs <;> simp_all

theorem sinkClass_eq_two {a b t : ℕ} :
    sinkClass a b t = 2 ↔ ¬(a + b ≤ t ∧ wall a b (t - (a + b)) = 0) ∧ wall a b t ≠ 0 ∧
      a ≤ t ∧ wall a b (t - a) = 0 := by
  unfold sinkClass
  split_ifs <;> simp_all

theorem sinkClass_eq_three {a b t : ℕ} :
    sinkClass a b t = 3 ↔ ¬(a + b ≤ t ∧ wall a b (t - (a + b)) = 0) ∧ wall a b t ≠ 0 ∧
      ¬(a ≤ t ∧ wall a b (t - a) = 0) := by
  unfold sinkClass
  split_ifs <;> simp_all

theorem sink_option {a b : ℕ} (t s : ℕ) :
    sink a b ((t : ℤ) + 1 - s) = if s ≤ t then sink a b (((t - s : ℕ) : ℤ) + 1) else 0 := by
  split_ifs with h
  · rw [show ((t : ℤ) + 1 - s) = ((t - s : ℕ) : ℤ) + 1 by omega]
  · exact sink_of_nonpos (by omega)

section T2

variable {a b : ℕ} (ha : 0 < a) (hab : a < b)
include ha hab

/-- (S3) A position `t + 1` of the last sink class has the `𝒫`-position `t - s₂`. -/
theorem sink_class3_shift {t : ℕ} (h0 : ¬(a + b ≤ t ∧ wall a b (t - (a + b)) = 0))
    (h1 : wall a b t ≠ 0) (h2 : ¬(a ≤ t ∧ wall a b (t - a) = 0)) :
    b ≤ t ∧ wall a b (t - b) = 0 := by
  obtain ⟨s, hs, hst, hP⟩ := dom ha hab h1
  rcases mem_moves.1 hs with h | h | h <;> rw [h] at hP hst
  · exact absurd ⟨hst, hP⟩ h2
  · exact ⟨hst, hP⟩
  · exact absurd ⟨hst, hP⟩ h0

/-- (T2) The sink values are determined by the wall `𝒫`-positions: `sink (t + 1)` is `0` on
`P + s₃`, `1` on `P`, `2` on `P + s₁`, and `3` elsewhere. -/
theorem sink_eq_sinkClass (t : ℕ) : sink a b ((t : ℤ) + 1) = sinkClass a b t := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  have hopt : ∀ s ∈ moves a b, sink a b ((t : ℤ) + 1 - s) =
      if s ≤ t then sinkClass a b (t - s) else 0 := by
    intro s hs
    rw [sink_option]
    split_ifs with h
    · exact ih _ (by have := moves_pos ha hab hs; omega)
    · rfl
  have hy : (0 : ℤ) < (t : ℤ) + 1 := by omega
  -- (Z0) an option of value zero
  have Z0 : ¬(a + b ≤ t ∧ wall a b (t - (a + b)) = 0) →
      ∃ s ∈ moves a b, sink a b ((t : ℤ) + 1 - s) = 0 := by
    intro h0
    by_cases hct : a + b ≤ t
    · obtain ⟨s, hs, hst, hP⟩ := dom ha hab (fun h => h0 ⟨hct, h⟩)
      refine ⟨s, hs, ?_⟩
      rw [hopt s hs, if_pos (by omega), sinkClass_eq_zero]
      exact ⟨by omega, by rwa [show t - s - (a + b) = t - (a + b) - s by omega]⟩
    · exact ⟨a + b, ab_mem, by rw [hopt _ ab_mem, if_neg hct]⟩
  by_cases h0 : a + b ≤ t ∧ wall a b (t - (a + b)) = 0
  · rw [show sinkClass a b t = 0 from sinkClass_eq_zero.2 h0, sink_eq_iff ha hab hy]
    refine ⟨fun s hs hv => ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    have hst : s ≤ t := by have := moves_le hs; omega
    rw [hopt s hs, if_pos hst, sinkClass_eq_zero] at hv
    exact indep ha hab hs hv.2 h0.2 (by omega)
  by_cases h1 : wall a b t = 0
  · rw [show sinkClass a b t = 1 from sinkClass_eq_one.2 ⟨h0, h1⟩, sink_eq_iff ha hab hy]
    refine ⟨fun s hs hv => ?_, fun j hj => ?_⟩
    · rw [hopt s hs] at hv
      by_cases hst : s ≤ t
      · rw [if_pos hst, sinkClass_eq_one] at hv
        exact indep ha hab hs hv.2 h1 (by omega)
      · rw [if_neg hst] at hv
        exact absurd hv (by decide)
    · obtain rfl : j = 0 := by omega
      exact Z0 h0
  by_cases h2 : a ≤ t ∧ wall a b (t - a) = 0
  · rw [show sinkClass a b t = 2 from sinkClass_eq_two.2 ⟨h0, h1, h2⟩, sink_eq_iff ha hab hy]
    refine ⟨fun s hs hv => ?_, fun j hj => ?_⟩
    · rw [hopt s hs] at hv
      by_cases hst : s ≤ t
      · rw [if_pos hst, sinkClass_eq_two] at hv
        exact indep ha hab hs hv.2.2.2 h2.2 (by omega)
      · rw [if_neg hst] at hv
        exact absurd hv (by decide)
    · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · exact Z0 h0
      · refine ⟨a, a_mem, ?_⟩
        rw [hopt a a_mem, if_pos h2.1, sinkClass_eq_one]
        exact ⟨fun h => indep ha hab ab_mem h.2 h2.2 (by omega), h2.2⟩
  · rw [show sinkClass a b t = 3 from sinkClass_eq_three.2 ⟨h0, h1, h2⟩, sink_eq_iff ha hab hy]
    obtain ⟨hbt, h3⟩ := sink_class3_shift ha hab h0 h1 h2
    refine ⟨fun s hs hv => ?_, fun j hj => ?_⟩
    · rw [hopt s hs] at hv
      by_cases hst : s ≤ t
      · rw [if_pos hst, sinkClass_eq_three] at hv
        obtain ⟨hb', h3'⟩ := sink_class3_shift ha hab hv.1 hv.2.1 hv.2.2
        exact indep ha hab hs h3' h3 (by omega)
      · rw [if_neg hst] at hv
        exact absurd hv (by decide)
    · rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
      · exact Z0 h0
      · refine ⟨b, b_mem, ?_⟩
        rw [hopt b b_mem, if_pos hbt, sinkClass_eq_one]
        exact ⟨fun h => indep ha hab ab_mem h.2 h3 (by omega), h3⟩
      · have hat : a ≤ t := by
          by_contra h
          exact h1 (wall_small ha hab (by omega))
        obtain ⟨s, hs, hst, hP⟩ := dom ha hab (fun h => h2 ⟨hat, h⟩)
        refine ⟨s, hs, ?_⟩
        rw [hopt s hs, if_pos (by omega), sinkClass_eq_two]
        have hP' : wall a b (t - s - a) = 0 := by rwa [show t - s - a = t - a - s by omega]
        exact ⟨fun h => indep ha hab b_mem h.2 hP' (by omega),
          fun h => indep ha hab a_mem hP' h (by omega), by omega, hP'⟩

end T2

section gap

variable {a b p : ℕ} (ha : 0 < a) (hab : a < b)
  (hgap : ∀ n, p - (a + b) ≤ n → n < p → wall a b n ≠ 0)
include ha hab hgap

/-- (A3) If `P` misses `[p - s₃, p)`, then `P` is `p`-periodic. -/
theorem wall_zero_add_period (hp : a + b < p) (x : ℕ) :
    wall a b (x + p) = 0 ↔ wall a b x = 0 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  rw [wall_zero_iff ha hab (x + p), wall_zero_iff ha hab x]
  constructor
  · intro h s hs hsx h'
    exact h s hs (by omega) (by
      rwa [show x + p - s = x - s + p by omega,
        ih (x - s) (by have := moves_pos ha hab hs; omega)])
  · intro h s hs _ h'
    by_cases hsx : s ≤ x
    · rw [show x + p - s = x - s + p by omega,
        ih (x - s) (by have := moves_pos ha hab hs; omega)] at h'
      exact h s hs hsx h'
    · exact hgap _ (by have := moves_le hs; omega) (by have := moves_pos ha hab hs; omega) h'

theorem wall_zero_add_mul_period (hp : a + b < p) (x k : ℕ) :
    wall a b (x + p * k) = 0 ↔ wall a b x = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show x + p * (k + 1) = x + p * k + p by ring, wall_zero_add_period ha hab hgap hp, ih]

/-- (T3) If `P` misses `[p - s₃, p)`, then `P ∩ [0, M]` is symmetric about `M / 2`, where
`M = p - s₃ - 1`. -/
theorem wall_zero_reflect {M : ℕ} (hM : M + (a + b) + 1 = p) {x : ℕ} (hx : x ≤ M) :
    wall a b x = 0 ↔ wall a b (M - x) = 0 := by
  have hR : ∀ x ≤ M, wall a b (M - x) = 0 ↔
      ∀ s ∈ moves a b, s ≤ x → wall a b (M - (x - s)) ≠ 0 := by
    intro x hx
    constructor
    · intro h s hs hsx h'
      exact indep ha hab hs h h' (by omega)
    · intro h
      by_contra hn
      obtain ⟨s, hs, hP⟩ := fwd ha hab hn
      by_cases hsx : s ≤ x
      · exact h s hs hsx (by rwa [show M - (x - s) = M - x + s by omega])
      · exact hgap _ (by omega) (by have := moves_le hs; omega) hP
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  rw [wall_zero_iff ha hab x, hR x hx]
  constructor
  · intro h s hs hsx h'
    exact h s hs hsx ((ih (x - s) (by have := moves_pos ha hab hs; omega) (by omega)).2 h')
  · intro h s hs hsx h'
    exact h s hs hsx ((ih (x - s) (by have := moves_pos ha hab hs; omega) (by omega)).1 h')

/-- With the gap, the wall nim-sequence is `p`-periodic. -/
theorem wall_add_period (hp : a + b < p) (x : ℕ) : wall a b (x + p) = wall a b x := by
  have hper := wall_zero_add_period ha hab hgap hp
  rw [wall_eq_wallClass ha hab, wall_eq_wallClass ha hab, wallClass, wallClass]
  refine if_congr (hper x) rfl (if_congr ?_ rfl (if_congr ?_ rfl rfl))
  · by_cases hax : a ≤ x
    · rw [show x + p - a = x - a + p by omega, hper]
      simp [hax, show a ≤ x + p by omega]
    · simp only [hax, false_and, iff_false, not_and]
      exact fun _ => hgap _ (by omega) (by omega)
  · rw [show x + p + b = x + b + p by omega, hper]

/-- With the gap, the sink nim-sequence is purely `p`-periodic on the positive positions. -/
theorem sink_add_period (hp : a + b < p) {y : ℤ} (hy : 0 < y) :
    sink a b (y + p) = sink a b y := by
  have hper := wall_zero_add_period ha hab hgap hp
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, y = (t : ℤ) + 1 := ⟨(y - 1).toNat, by omega⟩
  rw [show (t : ℤ) + 1 + p = ((t + p : ℕ) : ℤ) + 1 by push_cast; ring,
    sink_eq_sinkClass ha hab, sink_eq_sinkClass ha hab, sinkClass, sinkClass]
  refine if_congr ?_ rfl (if_congr (hper t) rfl (if_congr ?_ rfl rfl))
  · by_cases hct : a + b ≤ t
    · rw [show t + p - (a + b) = t - (a + b) + p by omega, hper]
      simp [hct, show a + b ≤ t + p by omega]
    · simp only [hct, false_and, iff_false, not_and]
      exact fun _ => hgap _ (by omega) (by omega)
  · by_cases hat : a ≤ t
    · rw [show t + p - a = t - a + p by omega, hper]
      simp [hat, show a ≤ t + p by omega]
    · simp only [hat, false_and, iff_false, not_and]
      exact fun _ => hgap _ (by omega) (by omega)

end gap

/-- The residue class of `X` modulo `p` contains a wall `𝒫`-position. -/
def Zp (a b p : ℕ) (X : ℤ) : Prop :=
  wall a b (X % (p : ℤ)).toNat = 0

instance (a b p : ℕ) : DecidablePred (Zp a b p) := fun X =>
  inferInstanceAs (Decidable (wall a b (X % (p : ℤ)).toNat = 0))

section residues

variable {a b p : ℕ} (ha : 0 < a) (hab : a < b) (hp : a + b < p)
  (hgap : ∀ n, p - (a + b) ≤ n → n < p → wall a b n ≠ 0)
include ha hab hp hgap

theorem Zp_iff {X : ℤ} (m : ℕ) (k : ℤ) (h : X = m + p * k) :
    Zp a b p X ↔ wall a b m = 0 := by
  rw [Zp, h, Int.add_mul_emod_self_left, ← Int.natCast_mod, Int.toNat_natCast]
  conv_rhs => rw [← Nat.mod_add_div m p]
  rw [wall_zero_add_mul_period ha hab hgap hp]

omit ha hab hgap in
/-- Every integer is a residue plus a multiple of `p`. -/
theorem residue_decomp (X : ℤ) :
    ∃ n : ℕ, ∃ K : ℤ, (n : ℤ) = X % (p : ℤ) ∧ n < p ∧ X = n + p * K := by
  have hp0 : (0 : ℤ) < p := by omega
  refine ⟨(X % (p : ℤ)).toNat, X / p, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), ?_, ?_⟩
  · have := Int.emod_lt_of_pos X hp0
    omega
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
    exact (Int.emod_add_mul_ediv X p).symm

/-- (Z-I) No two classes in `Z` differ by a move. -/
theorem Zp_indep {X Y : ℤ} {s : ℕ} (hs : s ∈ moves a b) (hX : Zp a b p X) (hY : Zp a b p Y)
    (h : Y = X + s) : False := by
  obtain ⟨n, K, -, hn, hXK⟩ := residue_decomp hp X
  rw [Zp_iff ha hab hp hgap n K hXK] at hX
  have := moves_le hs
  by_cases hns : n + s < p
  · rw [Zp_iff ha hab hp hgap (n + s) K (by omega)] at hY
    exact indep ha hab hs hX hY rfl
  · exact hgap n (by omega) hn hX

/-- (Z-R) The reflection `X ↦ -X - s₃ - 1` preserves `Z`. -/
theorem Zp_reflect {X Y : ℤ} (h : X + Y + (a + b) + 1 = 0) : Zp a b p X ↔ Zp a b p Y := by
  obtain ⟨n, K, -, hn, hXK⟩ := residue_decomp hp X
  rw [Zp_iff ha hab hp hgap n K hXK]
  have hmul1 : (p : ℤ) * (-K - 1) = -(p * K) - p := by ring
  have hmul2 : (p : ℤ) * (-K - 2) = -(p * K) - 2 * p := by ring
  by_cases hnM : n + (a + b) + 1 ≤ p
  · rw [Zp_iff ha hab hp hgap (p - (a + b) - 1 - n) (-K - 1) (by omega)]
    exact wall_zero_reflect ha hab hgap (M := p - (a + b) - 1) (by omega) (by omega)
  · rw [Zp_iff ha hab hp hgap (2 * p - (a + b) - 1 - n) (-K - 2) (by omega)]
    exact ⟨fun h' => absurd h' (hgap n (by omega) hn),
      fun h' => absurd h' (hgap _ (by omega) (by omega))⟩

/-- (T1) modulo `p`. -/
theorem wall_mod_eq (x : ℤ) :
    wall a b (x % (p : ℤ)).toNat =
      if Zp a b p x then 0 else if Zp a b p (x - a) then 1
      else if Zp a b p (x + b) then 2 else 3 := by
  obtain ⟨n, K, hnx, hn, hxK⟩ := residue_decomp hp x
  rw [← hnx, Int.toNat_natCast, wall_eq_wallClass ha hab n, wallClass]
  have hmul : (p : ℤ) * (K - 1) = p * K - p := by ring
  refine if_congr (Zp_iff ha hab hp hgap n K hxK).symm rfl
    (if_congr ?_ rfl (if_congr (Zp_iff ha hab hp hgap (n + b) K (by omega)).symm
      rfl rfl))
  by_cases han : a ≤ n
  · rw [Zp_iff ha hab hp hgap (n - a) K (by omega)]
    simp [han]
  · rw [Zp_iff ha hab hp hgap (n + p - a) (K - 1) (by omega)]
    simp only [han, false_and, false_iff]
    exact hgap _ (by omega) (by omega)

/-- (T2) modulo `p`. -/
theorem sink_mod_eq (y : ℤ) :
    sink a b (y % (p : ℤ)) =
      if Zp a b p (y - 1 - (a + b)) then 0 else if Zp a b p (y - 1) then 1
      else if Zp a b p (y - 1 - a) then 2 else 3 := by
  obtain ⟨n, K, hny, hn, hyK⟩ := residue_decomp hp y
  rw [← hny]
  have hmul : (p : ℤ) * (K - 1) = p * K - p := by ring
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [sink_of_nonpos (by simp), if_pos]
    rw [Zp_iff ha hab hp hgap (p - (a + b) - 1) (K - 1) (by omega)]
    have := (wall_zero_reflect ha hab hgap (M := p - (a + b) - 1) (by omega) (Nat.zero_le _)).1
      (wall_small ha hab ha)
    rwa [Nat.sub_zero] at this
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  rw [show ((t + 1 : ℕ) : ℤ) = (t : ℤ) + 1 by push_cast; ring, sink_eq_sinkClass ha hab t,
    sinkClass]
  refine if_congr ?_ rfl (if_congr (Zp_iff ha hab hp hgap t K (by omega)).symm rfl
    (if_congr ?_ rfl rfl))
  · by_cases hct : a + b ≤ t
    · rw [Zp_iff ha hab hp hgap (t - (a + b)) K (by omega)]
      simp [hct]
    · rw [Zp_iff ha hab hp hgap (t + p - (a + b)) (K - 1) (by omega)]
      simp only [hct, false_and, false_iff]
      exact hgap _ (by omega) (by omega)
  · by_cases hat : a ≤ t
    · rw [Zp_iff ha hab hp hgap (t - a) K (by omega)]
      simp [hat]
    · rw [Zp_iff ha hab hp hgap (t + p - a) (K - 1) (by omega)]
      simp only [hat, false_and, false_iff]
      exact hgap _ (by omega) (by omega)

/-- The duality formula, for any `p > s₃` such that no wall `𝒫`-position lies in
`[p - s₃, p)`. -/
theorem conj_of_gap (x : ℤ) :
    wall a b (x % (p : ℤ)).toNat = sigma (sink a b ((-(b : ℤ) - x) % (p : ℤ))) := by
  rw [wall_mod_eq ha hab hp hgap x, sink_mod_eq ha hab hp hgap]
  have r0 : Zp a b p (-(b : ℤ) - x - 1 - (a + b)) ↔ Zp a b p (x + b) :=
    Zp_reflect ha hab hp hgap (by ring)
  have r1 : Zp a b p (-(b : ℤ) - x - 1) ↔ Zp a b p (x - a) :=
    Zp_reflect ha hab hp hgap (by ring)
  have r2 : Zp a b p (-(b : ℤ) - x - 1 - a) ↔ Zp a b p x :=
    Zp_reflect ha hab hp hgap (by ring)
  rw [if_congr r0 rfl (if_congr r1 rfl (if_congr r2 rfl rfl))]
  have i01 : Zp a b p (x - a) → Zp a b p x → False := fun h1 h2 =>
    Zp_indep ha hab hp hgap a_mem h1 h2 (by ring)
  have i02 : Zp a b p x → Zp a b p (x + b) → False := fun h1 h2 =>
    Zp_indep ha hab hp hgap b_mem h1 h2 rfl
  have i12 : Zp a b p (x - a) → Zp a b p (x + b) → False := fun h1 h2 =>
    Zp_indep ha hab hp hgap ab_mem h1 h2 (by push_cast; ring)
  have s0 : sigma 0 = 2 := rfl
  have s1 : sigma 1 = 1 := rfl
  have s2 : sigma 2 = 0 := rfl
  have s3 : sigma 3 = 3 := rfl
  by_cases h0 : Zp a b p x <;> by_cases h1 : Zp a b p (x - a) <;>
    by_cases h2 : Zp a b p (x + b) <;> simp_all

end residues

/-- (B4, abstract form) A set `W ⊆ ℤ` in which no two elements differ by a move, which meets
every `{x, x - s₁, x - s₂, x - s₃}`, and which misses `[-s₃, -1]`, agrees on `ℕ` with the set of
wall `𝒫`-positions. -/
theorem wall_zero_iff_of_kernel {a b : ℕ} (ha : 0 < a) (hab : a < b) (W : ℤ → Prop)
    (hind : ∀ u v : ℤ, W u → W v → (v = u + a ∨ v = u + b ∨ v = u + (a + b)) → False)
    (hcov : ∀ x : ℤ, W x ∨ W (x - a) ∨ W (x - b) ∨ W (x - (a + b)))
    (hneg : ∀ x : ℤ, -((a : ℤ) + b) ≤ x → x < 0 → ¬ W x) (n : ℕ) :
    wall a b n = 0 ↔ W n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [wall_zero_iff ha hab n]
  constructor
  · intro h
    by_contra hW
    have key : ∀ s ∈ moves a b, ¬ W ((n : ℤ) - s) := by
      intro s hs hWs
      by_cases hsn : s ≤ n
      · refine h s hs hsn ((ih (n - s) (by have := moves_pos ha hab hs; omega)).2 ?_)
        rwa [Nat.cast_sub hsn]
      · exact hneg _ (by have := moves_le hs; omega) (by omega) hWs
    rcases hcov n with h0 | h1 | h2 | h3
    · exact hW h0
    · exact key a a_mem h1
    · exact key b b_mem h2
    · exact key (a + b) ab_mem (by push_cast; exact h3)
  · intro hW s hs hsx hP
    have hW' : W ((n - s : ℕ) : ℤ) := (ih (n - s) (by have := moves_pos ha hab hs; omega)).1 hP
    exact hind _ _ hW' hW (by rcases mem_moves.1 hs with h | h | h <;> omega)

end AgenticConjectures.AdditiveSinkWallDuality
