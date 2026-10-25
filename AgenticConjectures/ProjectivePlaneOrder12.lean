import Mathlib

/-!
# Projective planes of order 12: collineations of prime order at least 13

Elementary fixed-point counting for collineations of a finite projective plane, specialised
to order 12.  Planes are mathlib's `Configuration.ProjectivePlane P L`; a plane of order 12
means `ProjectivePlane.order P L = 12`, the same notion as `pp.order = 12` in the upstream
statement `Erdos723.erdos_723.variants.eq_12` (`upstream/723.lean`).  A collineation is a
pair of permutations of the points and of the lines preserving incidence (`Collineation`).

Main results, for a collineation `c` of a projective plane of order 12:
* `order13_fixed_antiflag`: if `c.pts ^ 13 = 1` and `c.pts ≠ 1`, then `c` fixes exactly one
  point and exactly one line, and the point is not on the line (an antiflag);
* `prime_gt_13`: if `c.pts ^ p = 1`, `c.pts ≠ 1`, `p` is prime and `13 < p`, then `p = 157`
  and `c` fixes no point and no line (so `⟨c⟩` is regular on the 157 points).

These are the structural starting points of the searches in
`problems/projective-plane-order-12` (cyclic planes, i.e. planar difference sets in `Z_157`,
and the order-13 antiflag reduction).  Nothing here decides whether a plane of order 12
exists.
-/

namespace AgenticConjectures.ProjectivePlaneOrder12

open Configuration

/-- A collineation: a permutation of the points and a permutation of the lines that
preserve incidence. -/
structure Collineation (P L : Type*) [Membership P L] where
  /-- the action on points -/
  pts : Equiv.Perm P
  /-- the action on lines -/
  lns : Equiv.Perm L
  mem_iff : ∀ (p : P) (l : L), pts p ∈ lns l ↔ p ∈ l

/-- For a permutation `σ` with `σ ^ p = 1`, `p` prime, the number of fixed points is
congruent to the number of elements modulo `p`. -/
theorem card_fixed_modEq {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ} [Fact p.Prime]
    (σ : Equiv.Perm α) (hσ : σ ^ p = 1) :
    (Finset.univ.filter fun a => σ a = a).card ≡ Fintype.card α [MOD p] := by
  have h := Equiv.Perm.card_compl_support_modEq (σ := σ) (p := p) (n := 1) (by rwa [pow_one])
  convert h using 2
  ext a
  simp [Equiv.Perm.mem_support]

namespace Collineation

variable {P L : Type*} [Membership P L]

/-- The same collineation, acting on the dual configuration. -/
def dual (c : Collineation P L) : Collineation (Dual L) (Dual P) where
  pts := c.lns
  lns := c.pts
  mem_iff l p := c.mem_iff p l

theorem pow_mem_iff (c : Collineation P L) (k : ℕ) (p : P) (l : L) :
    (c.pts ^ k) p ∈ (c.lns ^ k) l ↔ p ∈ l := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, c.mem_iff, ih]

end Collineation

variable {P L : Type*} [Membership P L]

/-- The number of fixed points is congruent to the number of points modulo `p`. -/
theorem card_fixed_points_modEq [Fintype P] (c : Collineation P L) {p : ℕ} [Fact p.Prime]
    (hp : c.pts ^ p = 1) : Nat.card {x : P // c.pts x = x} ≡ Fintype.card P [MOD p] := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_fixed_modEq c.pts hp

section ProjectivePlane

variable [ProjectivePlane P L]

/-- The line joining two fixed points is fixed. -/
theorem lns_mkLine_eq (c : Collineation P L) {x y : P} (hxy : x ≠ y) (hx : c.pts x = x)
    (hy : c.pts y = y) : c.lns (HasLines.mkLine hxy) = HasLines.mkLine hxy := by
  have h := HasLines.mkLine_ax (L := L) hxy
  have h1 : x ∈ c.lns (HasLines.mkLine hxy) := by
    have := (c.mem_iff x _).2 h.1
    rwa [hx] at this
  have h2 : y ∈ c.lns (HasLines.mkLine hxy) := by
    have := (c.mem_iff y _).2 h.2
    rwa [hy] at this
  exact (Nondegenerate.eq_or_eq h1 h2 h.1 h.2).resolve_left hxy

/-- If a fixed line `l` is fixed pointwise, a fixed point lies off `l`, and every fixed line
is either fixed pointwise or has no fixed point, then the collineation is trivial on points. -/
theorem pts_eq_one_of_fixed_off_line (c : Collineation P L)
    (hdich : ∀ m : L, c.lns m = m → (∀ x ∈ m, c.pts x = x) ∨ (∀ x ∈ m, c.pts x ≠ x))
    {l : L} (hfix : ∀ x ∈ l, c.pts x = x) {X : P} (hX : c.pts X = X) (hXl : X ∉ l) :
    c.pts = 1 := by
  ext Y
  simp only [Equiv.Perm.one_apply]
  by_cases hYl : Y ∈ l
  · exact hfix Y hYl
  by_cases hXY : X = Y
  · exact hXY ▸ hX
  have hm := HasLines.mkLine_ax (L := L) hXY
  have hml : HasLines.mkLine hXY ≠ l := fun h => hXl (h ▸ hm.1)
  have hZ := HasPoints.mkPoint_ax (P := P) hml
  have hZfix : c.pts (HasPoints.mkPoint hml) = HasPoints.mkPoint hml := hfix _ hZ.2
  have hXZ : X ≠ HasPoints.mkPoint hml := fun h => hXl (h ▸ hZ.2)
  have hmfix : c.lns (HasLines.mkLine hXY) = HasLines.mkLine hXY := by
    have h1 : X ∈ c.lns (HasLines.mkLine hXY) := by
      have := (c.mem_iff X _).2 hm.1
      rwa [hX] at this
    have h2 : HasPoints.mkPoint hml ∈ c.lns (HasLines.mkLine hXY) := by
      have := (c.mem_iff _ _).2 hZ.1
      rwa [hZfix] at this
    exact (Nondegenerate.eq_or_eq h1 h2 hm.1 hZ.1).resolve_left hXZ
  rcases hdich _ hmfix with hall | hnone
  · exact hall Y hm.2
  · exact absurd hX (hnone X hm.1)

/-- Under the dichotomy of `pts_eq_one_of_fixed_off_line`, the fixed points of a nontrivial
collineation are at most one point, or exactly the points of one fixed line. -/
theorem fixed_points_cases (c : Collineation P L) (hc : c.pts ≠ 1)
    (hdich : ∀ m : L, c.lns m = m → (∀ x ∈ m, c.pts x = x) ∨ (∀ x ∈ m, c.pts x ≠ x)) :
    (∀ x y : P, c.pts x = x → c.pts y = y → x = y) ∨
      ∃ l : L, c.lns l = l ∧ ∀ x, c.pts x = x ↔ x ∈ l := by
  by_cases h : ∃ x y : P, x ≠ y ∧ c.pts x = x ∧ c.pts y = y
  · obtain ⟨x, y, hxy, hx, hy⟩ := h
    have hl := lns_mkLine_eq c hxy hx hy
    have hall : ∀ z ∈ HasLines.mkLine (L := L) hxy, c.pts z = z := by
      rcases hdich _ hl with h | h
      · exact h
      · exact absurd hx (h x (HasLines.mkLine_ax hxy).1)
    refine Or.inr ⟨HasLines.mkLine hxy, hl, fun z => ⟨fun hz => ?_, hall z⟩⟩
    by_contra hzl
    exact hc (pts_eq_one_of_fixed_off_line c hdich hall hz hzl)
  · refine Or.inl fun x y hx hy => ?_
    by_contra hxy
    exact h ⟨x, y, hxy, hx, hy⟩

variable [Fintype P] [Fintype L]

/-- On a line fixed by a collineation `c` with `c.pts ^ p = 1`, the number of fixed points
is congruent to `order + 1` modulo `p`. -/
theorem card_fixed_on_line_modEq (c : Collineation P L) {p : ℕ} [Fact p.Prime]
    (hp : c.pts ^ p = 1) {l : L} (hl : c.lns l = l) :
    Nat.card {x : P // x ∈ l ∧ c.pts x = x} ≡ ProjectivePlane.order P L + 1 [MOD p] := by
  classical
  have hinv : ∀ x, c.pts x ∈ l ↔ x ∈ l := fun x => by
    have := c.mem_iff x l
    rwa [hl] at this
  let σ : Equiv.Perm {x : P // x ∈ l} := c.pts.subtypePerm hinv
  have hσ : σ ^ p = 1 := by
    ext x
    simp [σ, Equiv.Perm.subtypePerm_pow, hp]
  have h1 := card_fixed_modEq σ hσ
  have hcard : Fintype.card {x : P // x ∈ l} = ProjectivePlane.order P L + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact ProjectivePlane.pointCount_eq P l
  rw [hcard] at h1
  have hmap : (Finset.univ.filter fun x : {x : P // x ∈ l} => σ x = x).map
      (Function.Embedding.subtype _) =
      Finset.univ.filter fun x : P => x ∈ l ∧ c.pts x = x := by
    ext x
    simp [σ, Subtype.ext_iff, and_comm]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← hmap, Finset.card_map]
  exact h1

/-- A fixed line carries at most `order + 1` fixed points. -/
theorem card_fixed_on_line_le (c : Collineation P L) (l : L) :
    Nat.card {x : P // x ∈ l ∧ c.pts x = x} ≤ ProjectivePlane.order P L + 1 := by
  rw [← ProjectivePlane.pointCount_eq P l]
  exact Finite.card_le_of_embedding
    ⟨fun x => ⟨x.1, x.2.1⟩, fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h)⟩

/-- Fixed points on a line: if their number is `order + 1`, all points of the line are
fixed; if it is `0`, none is. -/
theorem fixed_on_line_of_card (c : Collineation P L) {l : L} :
    (Nat.card {x : P // x ∈ l ∧ c.pts x = x} = ProjectivePlane.order P L + 1 →
      ∀ x ∈ l, c.pts x = x) ∧
    (Nat.card {x : P // x ∈ l ∧ c.pts x = x} = 0 → ∀ x ∈ l, c.pts x ≠ x) := by
  classical
  constructor
  · intro hc x hx
    by_contra hfx
    have hcard : Fintype.card {x : P // x ∈ l} = ProjectivePlane.order P L + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact ProjectivePlane.pointCount_eq P l
    rw [Nat.card_eq_fintype_card] at hc
    have hlt : Fintype.card {x : P // x ∈ l ∧ c.pts x = x} <
        Fintype.card {x : P // x ∈ l} := by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_of_subset (fun y hy => ?_) |>.2 ⟨x, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        exact hy.1
      · simpa using hx
      · simp [hfx]
    omega
  · intro hc x hx hfx
    have : Nat.card {x : P // x ∈ l ∧ c.pts x = x} ≠ 0 := by
      rw [Nat.card_ne_zero]
      exact ⟨⟨⟨x, hx, hfx⟩⟩, inferInstance⟩
    exact this hc

/-- A collineation fixing every point fixes every line. -/
theorem lns_eq_one_of_pts_eq_one (c : Collineation P L) (h : c.pts = 1) : c.lns = 1 := by
  ext l
  have h3 : 1 < Nat.card {x : P // x ∈ l} :=
    lt_trans one_lt_two (ProjectivePlane.two_lt_pointCount P l)
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hne⟩ := (Finite.one_lt_card_iff_nontrivial.1 h3).exists_pair_ne
  have hxy : x ≠ y := fun e => hne (Subtype.ext e)
  have h1 : x ∈ c.lns l := by
    have := (c.mem_iff x l).2 hx
    rwa [h, Equiv.Perm.one_apply] at this
  have h2 : y ∈ c.lns l := by
    have := (c.mem_iff y l).2 hy
    rwa [h, Equiv.Perm.one_apply] at this
  simpa using (Nondegenerate.eq_or_eq h1 h2 hx hy).resolve_left hxy

/-- A collineation fixing every line fixes every point. -/
theorem pts_eq_one_of_lns_eq_one (c : Collineation P L) (h : c.lns = 1) : c.pts = 1 := by
  ext x
  have h3 : 1 < Nat.card {l : L // x ∈ l} :=
    lt_trans one_lt_two (ProjectivePlane.two_lt_lineCount L x)
  obtain ⟨⟨l, hl⟩, ⟨m, hm⟩, hne⟩ := (Finite.one_lt_card_iff_nontrivial.1 h3).exists_pair_ne
  have hlm : l ≠ m := fun e => hne (Subtype.ext e)
  have h1 : c.pts x ∈ l := by
    have := (c.mem_iff x l).2 hl
    rwa [h, Equiv.Perm.one_apply] at this
  have h2 : c.pts x ∈ m := by
    have := (c.mem_iff x m).2 hm
    rwa [h, Equiv.Perm.one_apply] at this
  simpa using (Nondegenerate.eq_or_eq h1 hl h2 hm).resolve_right hlm

/-- If `c.pts ^ k = 1` then `c.lns ^ k = 1`. -/
theorem lns_pow_eq_one (c : Collineation P L) {k : ℕ} (h : c.pts ^ k = 1) : c.lns ^ k = 1 :=
  lns_eq_one_of_pts_eq_one ⟨c.pts ^ k, c.lns ^ k, c.pow_mem_iff k⟩ h

/-- Fixed points counted: at most one, or exactly `order + 1`. -/
theorem card_fixed_points_cases (c : Collineation P L) (hc : c.pts ≠ 1)
    (hdich : ∀ m : L, c.lns m = m → (∀ x ∈ m, c.pts x = x) ∨ (∀ x ∈ m, c.pts x ≠ x)) :
    Nat.card {x : P // c.pts x = x} ≤ 1 ∨
      Nat.card {x : P // c.pts x = x} = ProjectivePlane.order P L + 1 := by
  rcases fixed_points_cases c hc hdich with h | ⟨l, -, hl⟩
  · left
    rw [Finite.card_le_one_iff_subsingleton]
    exact ⟨fun a b => Subtype.ext (h a.1 b.1 a.2 b.2)⟩
  · right
    rw [← ProjectivePlane.pointCount_eq P l]
    exact Nat.card_congr (Equiv.subtypeEquivRight hl)

/-- Order 12, `p = 13`: every fixed line is fixed pointwise or has no fixed point. -/
theorem dichotomy_of_order_13 (h12 : ProjectivePlane.order P L = 12) (c : Collineation P L)
    (h13 : c.pts ^ 13 = 1) (m : L) (hm : c.lns m = m) :
    (∀ x ∈ m, c.pts x = x) ∨ (∀ x ∈ m, c.pts x ≠ x) := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hmod := card_fixed_on_line_modEq c h13 hm
  have hle := card_fixed_on_line_le c m
  rw [h12] at hmod hle
  unfold Nat.ModEq at hmod
  have hcases : Nat.card {x : P // x ∈ m ∧ c.pts x = x} = 0 ∨
      Nat.card {x : P // x ∈ m ∧ c.pts x = x} = 12 + 1 := by
    omega
  rcases hcases with h | h
  · exact Or.inr ((fixed_on_line_of_card c).2 h)
  · exact Or.inl ((fixed_on_line_of_card c).1 (by rw [h12]; exact h))

/-- Order 12, `p = 13`: a nontrivial collineation has exactly one fixed point. -/
theorem existsUnique_fixed_point_of_order_13 (h12 : ProjectivePlane.order P L = 12)
    (c : Collineation P L) (h13 : c.pts ^ 13 = 1) (hc : c.pts ≠ 1) :
    ∃ x₀ : P, ∀ x, c.pts x = x ↔ x = x₀ := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hmod := card_fixed_points_modEq c h13
  rw [ProjectivePlane.card_points P L, h12] at hmod
  unfold Nat.ModEq at hmod
  norm_num at hmod
  rcases card_fixed_points_cases c hc (dichotomy_of_order_13 h12 c h13) with h | h
  · have h1 : Nat.card {x : P // c.pts x = x} = 1 := by omega
    obtain ⟨⟨x₀, hx₀⟩, hu⟩ := Nat.card_eq_one_iff_exists.1 h1
    exact ⟨x₀, fun x => ⟨fun hx => congrArg Subtype.val (hu ⟨x, hx⟩), fun e => e ▸ hx₀⟩⟩
  · rw [h12] at h
    omega

/-- **Collineations of order 13.**  A nontrivial collineation `c` with `c ^ 13 = 1` of a
projective plane of order 12 fixes exactly one point `x₀` and exactly one line `l₀`, and
`x₀ ∉ l₀`. -/
theorem order13_fixed_antiflag (h12 : ProjectivePlane.order P L = 12) (c : Collineation P L)
    (h13 : c.pts ^ 13 = 1) (hc : c.pts ≠ 1) :
    ∃ (x₀ : P) (l₀ : L), (∀ x, c.pts x = x ↔ x = x₀) ∧ (∀ l, c.lns l = l ↔ l = l₀) ∧
      x₀ ∉ l₀ := by
  obtain ⟨x₀, hx₀⟩ := existsUnique_fixed_point_of_order_13 h12 c h13 hc
  have hd12 : ProjectivePlane.order (Dual L) (Dual P) = 12 :=
    (ProjectivePlane.Dual.order P L).trans h12
  have hl13 : c.lns ^ 13 = 1 := lns_pow_eq_one c h13
  have hlc : c.lns ≠ 1 := fun h => hc (pts_eq_one_of_lns_eq_one c h)
  obtain ⟨l₀, hl₀⟩ := existsUnique_fixed_point_of_order_13 hd12 c.dual hl13 hlc
  refine ⟨x₀, l₀, hx₀, hl₀, fun hmem => ?_⟩
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hmod := card_fixed_on_line_modEq c.dual hl13 (l := x₀) ((hx₀ x₀).2 rfl)
  rw [hd12] at hmod
  change Nat.card {l : L // x₀ ∈ l ∧ c.lns l = l} ≡ 12 + 1 [MOD 13] at hmod
  have h1 : Nat.card {l : L // x₀ ∈ l ∧ c.lns l = l} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    exact ⟨⟨l₀, hmem, (hl₀ l₀).2 rfl⟩, fun y => Subtype.ext ((hl₀ y.1).1 y.2.2)⟩
  rw [h1] at hmod
  norm_num [Nat.ModEq] at hmod

/-- Order 12, `p > 13` prime: every fixed line is fixed pointwise. -/
theorem fixed_line_pointwise_of_gt_13 (h12 : ProjectivePlane.order P L = 12)
    (c : Collineation P L) {p : ℕ} [Fact p.Prime] (hp13 : 13 < p) (hcp : c.pts ^ p = 1)
    (m : L) (hm : c.lns m = m) : ∀ x ∈ m, c.pts x = x := by
  have hmod := card_fixed_on_line_modEq c hcp hm
  have hle := card_fixed_on_line_le c m
  rw [h12] at hmod hle
  apply (fixed_on_line_of_card c).1
  rw [h12]
  have h1 : Nat.card {x : P // x ∈ m ∧ c.pts x = x} < p := by omega
  have h2 : 12 + 1 < p := by omega
  unfold Nat.ModEq at hmod
  rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod

/-- Order 12, `p > 13` prime: a nontrivial collineation has no fixed point, and `p = 157`. -/
theorem no_fixed_point_of_gt_13 (h12 : ProjectivePlane.order P L = 12) (c : Collineation P L)
    {p : ℕ} (hp : p.Prime) (hp13 : 13 < p) (hcp : c.pts ^ p = 1) (hc : c.pts ≠ 1) :
    (∀ x, c.pts x ≠ x) ∧ p = 157 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmod := card_fixed_points_modEq c hcp
  rw [ProjectivePlane.card_points P L, h12] at hmod
  norm_num at hmod
  have hdvd : ∀ f : ℕ, f ≤ 157 → f ≡ 157 [MOD p] → p ∣ 157 - f := fun f hf h =>
    (Nat.modEq_iff_dvd' hf).1 h
  have h12' : ¬ p ∣ 12 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have h13' : ¬ p ∣ 13 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hdich : ∀ m : L, c.lns m = m → (∀ x ∈ m, c.pts x = x) ∨ (∀ x ∈ m, c.pts x ≠ x) :=
    fun m hm => Or.inl (fixed_line_pointwise_of_gt_13 h12 c hp13 hcp m hm)
  have hzero : Nat.card {x : P // c.pts x = x} = 0 := by
    rcases card_fixed_points_cases c hc hdich with h | h
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with h0 | h1
      · exact h0
      · rw [h1] at hmod
        have h156 : p ∣ 12 * 13 := hdvd 1 (by norm_num) hmod
        rcases (Nat.Prime.dvd_mul hp).1 h156 with h | h
        · exact absurd h h12'
        · exact absurd h h13'
    · rw [h, h12] at hmod
      have h144 : p ∣ 12 * 12 := hdvd 13 (by norm_num) hmod
      rcases (Nat.Prime.dvd_mul hp).1 h144 with h | h <;> exact absurd h h12'
  refine ⟨fun x hx => (Finite.card_eq_zero_iff.1 hzero).false ⟨x, hx⟩, ?_⟩
  rw [hzero] at hmod
  have h157 : p ∣ 157 := by simpa using hdvd 0 (by norm_num) hmod
  exact ((Nat.Prime.eq_one_or_self_of_dvd (by norm_num) p h157).resolve_left hp.one_lt.ne')

/-- **Collineations of prime order above 13.**  If a nontrivial collineation `c` of a
projective plane of order 12 satisfies `c ^ p = 1` for a prime `p > 13`, then `p = 157` and
`c` fixes no point and no line. -/
theorem prime_gt_13 (h12 : ProjectivePlane.order P L = 12) (c : Collineation P L) {p : ℕ}
    (hp : p.Prime) (hp13 : 13 < p) (hcp : c.pts ^ p = 1) (hc : c.pts ≠ 1) :
    p = 157 ∧ (∀ x, c.pts x ≠ x) ∧ ∀ l, c.lns l ≠ l := by
  obtain ⟨hx, h157⟩ := no_fixed_point_of_gt_13 h12 c hp hp13 hcp hc
  have hd12 : ProjectivePlane.order (Dual L) (Dual P) = 12 :=
    (ProjectivePlane.Dual.order P L).trans h12
  have hlc : c.lns ≠ 1 := fun h => hc (pts_eq_one_of_lns_eq_one c h)
  exact ⟨h157, hx, (no_fixed_point_of_gt_13 hd12 c.dual hp hp13 (lns_pow_eq_one c hcp) hlc).1⟩

end ProjectivePlane

end AgenticConjectures.ProjectivePlaneOrder12
