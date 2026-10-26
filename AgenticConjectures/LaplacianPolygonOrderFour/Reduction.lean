import AgenticConjectures.LaplacianPolygonOrderFour.Eigen

/-!
# Reduction to sparse weights

Fix an `ℝ`-linear functional `φ : ℂ →ₗ[ℝ] ℝ`. Starting from weights `b` in the box `[0, 1]`
and an eigenvalue `z` of `lap b`, we change only fractional weights (those strictly between
`0` and `1`) until at most four of them are fractional, at most two in each row (`Sparse`),
while keeping an eigenvalue `z'` of the new Laplacian with `φ z ≤ φ z'` (`exists_sparse`).

Each step moves `b` along a direction `δ` that vanishes off the fractional arcs, until one
more arc reaches `0` or `1` (`exists_move`), so the number of fractional arcs drops:

* `left_move` (at least five fractional arcs, `z ≠ 0`): for a left eigenvector `y` we have
  `∑ y = 0`. The real-linear map `(δ, μ) ↦ (y ᵥ* lap δ - μ y)` restricted to the first three
  coordinates goes from dimension `card + 2 ≥ 7` to dimension `6`, so it has a nonzero kernel
  element; the fourth coordinate then vanishes too, because both `y ᵥ* lap δ` and `μ y` have
  coordinate sum `0`. Hence `y ᵥ* lap (b + s • δ) = (z + s μ) y`, and the sign of `(δ, μ)` is
  chosen so that `φ μ ≥ 0`.
* `right_move` (three fractional arcs in a row `i`): for a right eigenvector `v`, a dimension
  count (`4 > 3`) gives a nonzero `δ` supported on the off-diagonal arcs of row `i` with
  `lap δ v = 0`, so `z` stays an eigenvalue of `lap (b + s • δ)`.
* If `z = 0`, all fractional weights are set to `0`; `0` is an eigenvalue of every `lap b`.

Weights on arcs that are not fractional at the start are never changed.
-/

namespace AgenticConjectures.LaplacianPolygonOrderFour

open Complex Matrix

/-! ### Linearity of `lap` and its action on complex vectors -/

/-- `lap` is additive in the weights. -/
theorem lap_add (b c : Fin 4 → Fin 4 → ℝ) : lap (b + c) = lap b + lap c := by
  ext i j
  by_cases h : i = j <;> simp [lap, h, Finset.sum_add_distrib] <;> ring

/-- `lap` is homogeneous in the weights. -/
theorem lap_smul (s : ℝ) (b : Fin 4 → Fin 4 → ℝ) : lap (s • b) = s • lap b := by
  ext i j
  by_cases h : i = j <;> simp [lap, h, ← Finset.mul_sum, mul_sub]

/-- `lap b` applied to a complex vector: `(lap b v) i = ∑ j, b i j (v i - v j)`. -/
theorem mulVec_lap (b : Fin 4 → Fin 4 → ℝ) (v : Fin 4 → ℂ) (i : Fin 4) :
    ((lap b).map ((↑) : ℝ → ℂ) *ᵥ v) i = ∑ j, (b i j : ℂ) * (v i - v j) := by
  simp [Matrix.mulVec, dotProduct, lap, Matrix.diagonal_apply, sub_mul, mul_sub,
    Finset.sum_sub_distrib, Finset.sum_mul, apply_ite ((↑) : ℝ → ℂ), ite_mul]

/-- The entries of `y ᵥ* lap b` sum to zero, because the rows of `lap b` do. -/
theorem sum_vecMul_lap (y : Fin 4 → ℂ) (b : Fin 4 → Fin 4 → ℝ) :
    ∑ j, (y ᵥ* (lap b).map ((↑) : ℝ → ℂ)) j = 0 := by
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, ← ofReal_sum, lap_row_sum]

/-- Complexifying a real matrix commutes with real scalars. -/
theorem map_ofReal_smul (c : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    (c • A).map ((↑) : ℝ → ℂ) = (c : ℂ) • A.map ((↑) : ℝ → ℂ) := by
  ext i j
  simp

/-- The complexified Laplacian of `b + s • δ`. -/
theorem map_lap_add_smul (b δ : Fin 4 → Fin 4 → ℝ) (s : ℝ) :
    (lap (b + s • δ)).map ((↑) : ℝ → ℂ) =
      (lap b).map ((↑) : ℝ → ℂ) + (s : ℂ) • (lap δ).map ((↑) : ℝ → ℂ) := by
  rw [lap_add, lap_smul]
  ext i j
  simp

/-- `0` is an eigenvalue of every `lap b`: the all-ones vector lies in its kernel. -/
theorem isEig_lap_zero (b : Fin 4 → Fin 4 → ℝ) : IsEig (lap b) 0 := by
  refine isEig_iff_right.2 ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0), ?_⟩
  funext i
  rw [mulVec_lap]
  simp

/-! ### Fractional arcs and weights supported on a set of arcs -/

/-- Membership in `fracArcs`. -/
theorem mem_fracArcs {b : Fin 4 → Fin 4 → ℝ} {e : Fin 4 × Fin 4} :
    e ∈ fracArcs b ↔ e.1 ≠ e.2 ∧ 0 < b e.1 e.2 ∧ b e.1 e.2 < 1 := by
  simp [fracArcs]

/-- Whether an arc is fractional depends only on its own weight. -/
theorem notMem_fracArcs_of_eq {b b' : Fin 4 → Fin 4 → ℝ} {i j : Fin 4}
    (h : (i, j) ∉ fracArcs b) (he : b' i j = b i j) : (i, j) ∉ fracArcs b' := by
  simp only [mem_fracArcs] at h ⊢
  rwa [he]

/-- Extension by zero of weights given on a set `S` of arcs. -/
def extendArcs (S : Finset (Fin 4 × Fin 4)) (d : S → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j => if h : (i, j) ∈ S then d ⟨(i, j), h⟩ else 0

/-- `extendArcs` is additive. -/
theorem extendArcs_add (S : Finset (Fin 4 × Fin 4)) (d d' : S → ℝ) :
    extendArcs S (d + d') = extendArcs S d + extendArcs S d' := by
  funext i j
  simp only [extendArcs, Pi.add_apply]
  split_ifs <;> simp

/-- `extendArcs` is homogeneous. -/
theorem extendArcs_smul (S : Finset (Fin 4 × Fin 4)) (c : ℝ) (d : S → ℝ) :
    extendArcs S (c • d) = c • extendArcs S d := by
  funext i j
  simp only [extendArcs, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- `extendArcs S d` vanishes off `S`. -/
theorem extendArcs_of_notMem {S : Finset (Fin 4 × Fin 4)} (d : S → ℝ) {i j : Fin 4}
    (h : (i, j) ∉ S) : extendArcs S d i j = 0 := by
  simp [extendArcs, h]

/-- The extension by zero of a nonzero function is nonzero. -/
theorem extendArcs_ne_zero {S : Finset (Fin 4 × Fin 4)} {d : S → ℝ} (hd : d ≠ 0) :
    extendArcs S d ≠ 0 := by
  obtain ⟨e, he⟩ := Function.ne_iff.1 hd
  intro h
  apply he
  have := congrFun (congrFun h e.1.1) e.1.2
  simpa [extendArcs, e.2] using this

/-! ### Moving until one more weight reaches `0` or `1` -/

/-- The time at which a weight `β`, moving at velocity `d ≠ 0`, reaches `0` or `1`. -/
noncomputable def hitTime (β d : ℝ) : ℝ := if 0 < d then (1 - β) / d else β / (-d)

/-- A fractional weight moving at nonzero velocity takes a positive time to reach `0` or `1`. -/
theorem hitTime_pos {β d : ℝ} (h0 : 0 < β) (h1 : β < 1) (hd : d ≠ 0) : 0 < hitTime β d := by
  unfold hitTime
  split_ifs with h
  · exact div_pos (by linarith) h
  · exact div_pos h0 (neg_pos.2 (lt_of_le_of_ne (not_lt.1 h) hd))

/-- Up to its hitting time, a fractional weight stays in `[0, 1]`. -/
theorem mem_Icc_of_le_hitTime {β d t : ℝ} (h0 : 0 < β) (h1 : β < 1) (hd : d ≠ 0)
    (ht0 : 0 ≤ t) (ht : t ≤ hitTime β d) : 0 ≤ β + t * d ∧ β + t * d ≤ 1 := by
  unfold hitTime at ht
  split_ifs at ht with h
  · rw [le_div_iff₀ h] at ht
    constructor <;> nlinarith
  · have h' : 0 < -d := neg_pos.2 (lt_of_le_of_ne (not_lt.1 h) hd)
    rw [le_div_iff₀ h'] at ht
    constructor <;> nlinarith

/-- At its hitting time, a weight is `0` or `1`. -/
theorem hitTime_hit {β d : ℝ} (hd : d ≠ 0) :
    β + hitTime β d * d = 0 ∨ β + hitTime β d * d = 1 := by
  unfold hitTime
  split_ifs with h
  · right
    field_simp
    ring
  · left
    field_simp
    ring

/-- Move along a direction supported on the fractional arcs until one more arc hits 0 or 1. -/
theorem exists_move {b δ : Fin 4 → Fin 4 → ℝ} (hb : InBox b)
    (hδ : ∀ i j, (i, j) ∉ fracArcs b → δ i j = 0) (hδ0 : δ ≠ 0) :
    ∃ s : ℝ, 0 < s ∧ InBox (b + s • δ) ∧ (fracArcs (b + s • δ)).card < (fracArcs b).card := by
  classical
  -- the fractional arcs that actually move
  set T := (fracArcs b).filter (fun e => δ e.1 e.2 ≠ 0)
  have hmemT : ∀ e, e ∈ T ↔ e ∈ fracArcs b ∧ δ e.1 e.2 ≠ 0 := fun e => Finset.mem_filter
  have hTne : T.Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hδ0
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hi
    refine ⟨(i, j), (hmemT _).2 ⟨?_, hj⟩⟩
    by_contra h
    exact hj (hδ i j h)
  -- the first arc to reach `0` or `1`
  obtain ⟨e₀, he₀, hmin⟩ :=
    T.exists_min_image (fun e => hitTime (b e.1 e.2) (δ e.1 e.2)) hTne
  obtain ⟨he₀F, he₀δ⟩ := (hmemT e₀).1 he₀
  obtain ⟨-, he₀0, he₀1⟩ := mem_fracArcs.1 he₀F
  set s := hitTime (b e₀.1 e₀.2) (δ e₀.1 e₀.2) with hs
  have hspos : 0 < s := hitTime_pos he₀0 he₀1 he₀δ
  have hval : ∀ i j, (b + s • δ) i j = b i j + s * δ i j := fun i j => rfl
  refine ⟨s, hspos, fun i j hij => ?_, ?_⟩
  · rw [hval]
    by_cases hd : δ i j = 0
    · rw [hd, mul_zero, add_zero]
      exact hb i j hij
    · have hF : (i, j) ∈ fracArcs b := by
        by_contra h
        exact hd (hδ i j h)
      obtain ⟨-, h0, h1⟩ := mem_fracArcs.1 hF
      exact mem_Icc_of_le_hitTime h0 h1 hd hspos.le (hmin (i, j) ((hmemT _).2 ⟨hF, hd⟩))
  · have hsub : fracArcs (b + s • δ) ⊆ fracArcs b := by
      intro e he
      by_contra h
      have h0 := hδ e.1 e.2 h
      rw [mem_fracArcs, hval, h0, mul_zero, add_zero] at he
      exact h (mem_fracArcs.2 he)
    have hnot : e₀ ∉ fracArcs (b + s • δ) := by
      rw [mem_fracArcs, hval]
      rintro ⟨-, h0, h1⟩
      rcases hitTime_hit (β := b e₀.1 e₀.2) he₀δ with h | h <;> rw [← hs] at h <;> linarith
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨e₀, he₀F, hnot⟩)

/-! ### The two kinds of steps -/

/-- With `z ≠ 0` and at least five fractional arcs, move along a left-eigenvector direction:
one more arc becomes `0` or `1`, and an eigenvalue `z'` with `φ z ≤ φ z'` survives. -/
theorem left_move (φ : ℂ →ₗ[ℝ] ℝ) {b : Fin 4 → Fin 4 → ℝ} (hb : InBox b) {z : ℂ}
    (hz : IsEig (lap b) z) (hz0 : z ≠ 0) (hcard : 5 ≤ (fracArcs b).card) :
    ∃ b' z', InBox b' ∧ (fracArcs b').card < (fracArcs b).card ∧ IsEig (lap b') z' ∧
      φ z ≤ φ z' ∧ ∀ i j, (i, j) ∉ fracArcs b → b' i j = b i j := by
  classical
  obtain ⟨y, hy0, hy⟩ := isEig_iff_left.1 hz
  have hsum : ∑ i, y i = 0 := by
    have h1 := sum_vecMul_lap y b
    rw [hy] at h1
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at h1
    exact (mul_eq_zero.1 h1).resolve_left hz0
  set F := fracArcs b
  -- `(d, μ) ↦ (y ᵥ* lap δ - μ y)` on the first three coordinates, with `δ` = `d` extended
  let K : (F → ℝ) × ℂ →ₗ[ℝ] (Fin 3 → ℂ) :=
    { toFun := fun p j =>
        (y ᵥ* (lap (extendArcs F p.1)).map ((↑) : ℝ → ℂ)) j.castSucc - p.2 * y j.castSucc
      map_add' := fun p q => by
        funext j
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, extendArcs_add, lap_add,
          Matrix.map_add _ ofReal_add, Matrix.vecMul_add]
        ring
      map_smul' := fun c p => by
        funext j
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, extendArcs_smul, lap_smul,
          map_ofReal_smul, Matrix.vecMul_smul, RingHom.id_apply, smul_eq_mul, real_smul]
        ring }
  have hdim : Module.finrank ℝ (Fin 3 → ℂ) < Module.finrank ℝ ((F → ℝ) × ℂ) := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
      finrank_real_complex, Module.finrank_pi_fintype]
    simp only [finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    omega
  obtain ⟨p, hpker, hp0⟩ :=
    (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := K) hdim)
  -- choose the sign so that `φ μ ≥ 0`
  obtain ⟨⟨d, μ⟩, hker, hne, hφμ⟩ : ∃ q : (F → ℝ) × ℂ, K q = 0 ∧ q ≠ 0 ∧ 0 ≤ φ q.2 := by
    rcases le_total 0 (φ p.2) with h | h
    · exact ⟨p, hpker, hp0, h⟩
    · refine ⟨-p, by rw [map_neg, LinearMap.mem_ker.1 hpker, neg_zero], neg_ne_zero.2 hp0, ?_⟩
      rw [Prod.snd_neg, map_neg]
      linarith
  have h3 : ∀ j : Fin 3,
      (y ᵥ* (lap (extendArcs F d)).map ((↑) : ℝ → ℂ)) j.castSucc = μ * y j.castSucc :=
    fun j => sub_eq_zero.1 (congrFun hker j)
  -- the last coordinate matches too, since both sides have coordinate sum `0`
  have hvec : y ᵥ* (lap (extendArcs F d)).map ((↑) : ℝ → ℂ) = μ • y := by
    funext j
    induction j using Fin.lastCases with
    | last =>
      have hw := sum_vecMul_lap y (extendArcs F d)
      rw [Fin.sum_univ_castSucc] at hw hsum
      simp only [h3, ← Finset.mul_sum] at hw
      rw [Pi.smul_apply, smul_eq_mul]
      linear_combination hw - μ * hsum
    | cast j => rw [h3 j, Pi.smul_apply, smul_eq_mul]
  have hd0 : d ≠ 0 := by
    intro hd
    apply hne
    have hδ : extendArcs F d = 0 := by
      rw [hd]
      funext i j
      simp [extendArcs]
    have hμy : μ • y = 0 := by
      rw [← hvec, hδ]
      have : lap 0 = 0 := by
        ext i j
        simp [lap]
      rw [this, Matrix.map_zero _ ofReal_zero, Matrix.vecMul_zero]
    have hμ : μ = 0 := (smul_eq_zero.1 hμy).resolve_right hy0
    rw [hd, hμ, Prod.mk_zero_zero]
  have hδF : ∀ i j, (i, j) ∉ fracArcs b → extendArcs F d i j = 0 :=
    fun i j h => extendArcs_of_notMem d h
  obtain ⟨s, hs, hbox, hlt⟩ := exists_move hb hδF (extendArcs_ne_zero hd0)
  refine ⟨b + s • extendArcs F d, z + s * μ, hbox, hlt, ?_, ?_, fun i j h => ?_⟩
  · refine isEig_iff_left.2 ⟨y, hy0, ?_⟩
    rw [map_lap_add_smul, Matrix.vecMul_add, Matrix.vecMul_smul, hy, hvec, smul_smul, add_smul]
  · have : z + (s : ℂ) * μ = z + s • μ := by rw [real_smul]
    rw [this, map_add, map_smul, smul_eq_mul]
    exact le_add_of_nonneg_right (mul_nonneg hs.le hφμ)
  · simp [hδF i j h]

/-- With three fractional arcs in row `i`, move along a direction in row `i` that kills a right
eigenvector: one more arc becomes `0` or `1`, and `z` stays an eigenvalue. -/
theorem right_move {b : Fin 4 → Fin 4 → ℝ} (hb : InBox b) {z : ℂ} (hz : IsEig (lap b) z)
    {i : Fin 4} (hrow : 3 ≤ ((fracArcs b).filter fun e => e.1 = i).card) :
    ∃ b', InBox b' ∧ (fracArcs b').card < (fracArcs b).card ∧ IsEig (lap b') z ∧
      ∀ i j, (i, j) ∉ fracArcs b → b' i j = b i j := by
  classical
  -- every off-diagonal arc of row `i` is fractional
  have hall : ∀ j, j ≠ i → (i, j) ∈ fracArcs b := by
    have hsub : ((fracArcs b).filter fun e => e.1 = i) ⊆
        (Finset.univ.erase i).image (Prod.mk i) := by
      intro e he
      obtain ⟨heF, rfl⟩ := Finset.mem_filter.1 he
      obtain ⟨hne, -, -⟩ := mem_fracArcs.1 heF
      exact Finset.mem_image.2 ⟨e.2, Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ _⟩, rfl⟩
    have hcard : ((Finset.univ.erase i).image (Prod.mk i)).card = 3 := by
      rw [Finset.card_image_of_injective _ (Prod.mk_right_injective i),
        Finset.card_erase_of_mem (Finset.mem_univ _)]
      simp
    have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    intro j hj
    have : (i, j) ∈ (Finset.univ.erase i).image (Prod.mk i) :=
      Finset.mem_image.2 ⟨j, Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩, rfl⟩
    rw [← heq] at this
    exact (Finset.mem_filter.1 this).1
  obtain ⟨v, hv0, hv⟩ := isEig_iff_right.1 hz
  -- `d ↦ (∑ j, d j (v i - v j), d i)`; a kernel element is a row-`i` direction killing `v`
  let K : (Fin 4 → ℝ) →ₗ[ℝ] ℂ × ℝ :=
    { toFun := fun d => (∑ j, (d j : ℂ) * (v i - v j), d i)
      map_add' := fun d d' => by
        simp only [Pi.add_apply, ofReal_add, add_mul, Finset.sum_add_distrib, Prod.mk_add_mk]
      map_smul' := fun c d => by
        simp only [Pi.smul_apply, smul_eq_mul, ofReal_mul, RingHom.id_apply, Prod.smul_mk,
          real_smul, Finset.mul_sum, mul_assoc] }
  have hdim : Module.finrank ℝ (ℂ × ℝ) < Module.finrank ℝ (Fin 4 → ℝ) := by
    rw [Module.finrank_prod, finrank_real_complex, Module.finrank_self,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    norm_num
  obtain ⟨d, hdker, hd0⟩ :=
    (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := K) hdim)
  have hker := LinearMap.mem_ker.1 hdker
  have hdsum : ∑ j, (d j : ℂ) * (v i - v j) = 0 := congrArg Prod.fst hker
  have hdi : d i = 0 := congrArg Prod.snd hker
  let δ : Fin 4 → Fin 4 → ℝ := fun i' j => if i' = i then d j else 0
  have hδF : ∀ i' j, (i', j) ∉ fracArcs b → δ i' j = 0 := by
    intro i' j h
    simp only [δ]
    split_ifs with hi'
    · subst hi'
      by_contra hdj
      by_cases hj : j = i'
      · subst hj
        exact hdj hdi
      · exact h (hall j hj)
    · rfl
  have hδ0 : δ ≠ 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hd0
    intro h
    apply hj
    have := congrFun (congrFun h i) j
    simpa [δ] using this
  have hδv : (lap δ).map ((↑) : ℝ → ℂ) *ᵥ v = 0 := by
    funext i'
    rw [mulVec_lap]
    by_cases hi' : i' = i
    · subst hi'
      simpa [δ] using hdsum
    · simp [δ, hi']
  obtain ⟨s, -, hbox, hlt⟩ := exists_move hb hδF hδ0
  refine ⟨b + s • δ, hbox, hlt, ?_, fun i' j h => ?_⟩
  · refine isEig_iff_right.2 ⟨v, hv0, ?_⟩
    rw [map_lap_add_smul, Matrix.add_mulVec, Matrix.smul_mulVec, hv, hδv, smul_zero, add_zero]
  · simp [hδF i' j h]

/-! ### The reduction -/

/-- Every eigenvalue `z` of `lap b` with `b` in the box is dominated, in the direction `φ`, by
an eigenvalue `z'` of `lap b'` with `b'` in the box and sparse; `b'` agrees with `b` on every
arc that is not fractional for `b`. -/
theorem exists_sparse (φ : ℂ →ₗ[ℝ] ℝ) {b : Fin 4 → Fin 4 → ℝ} (hb : InBox b) {z : ℂ}
    (hz : IsEig (lap b) z) :
    ∃ b' z', InBox b' ∧ Sparse b' ∧ IsEig (lap b') z' ∧ φ z ≤ φ z' ∧
      ∀ i j, (i, j) ∉ fracArcs b → b' i j = b i j := by
  classical
  suffices H : ∀ n (b : Fin 4 → Fin 4 → ℝ), (fracArcs b).card = n → InBox b → ∀ z,
      IsEig (lap b) z → ∃ b' z', InBox b' ∧ Sparse b' ∧ IsEig (lap b') z' ∧ φ z ≤ φ z' ∧
        ∀ i j, (i, j) ∉ fracArcs b → b' i j = b i j from H _ b rfl hb z hz
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hn hb z hz
    by_cases hz0 : z = 0
    · -- set every fractional weight to `0`
      subst hz0
      let b₀ : Fin 4 → Fin 4 → ℝ := fun i j => if (i, j) ∈ fracArcs b then 0 else b i j
      have hb₀ : fracArcs b₀ = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun e he => ?_
        obtain ⟨hne, h0, h1⟩ := mem_fracArcs.1 he
        by_cases hm : e ∈ fracArcs b
        · simp [b₀, hm] at h0
        · simp only [b₀, hm, if_false] at h0 h1
          exact hm (mem_fracArcs.2 ⟨hne, h0, h1⟩)
      refine ⟨b₀, 0, fun i j hij => ?_, ⟨by simp [hb₀], fun i => by simp [hb₀]⟩,
        isEig_lap_zero b₀, le_rfl, fun i j h => by simp [b₀, h]⟩
      simp only [b₀]
      split_ifs
      · exact ⟨le_rfl, zero_le_one⟩
      · exact hb i j hij
    by_cases hsp : Sparse b
    · exact ⟨b, z, hb, hsp, hz, le_rfl, fun _ _ _ => rfl⟩
    -- one step reduces the number of fractional arcs
    obtain ⟨b₁, z₁, hb₁, hlt, hz₁, hφ₁, hun₁⟩ : ∃ b₁ z₁, InBox b₁ ∧ (fracArcs b₁).card < n ∧
        IsEig (lap b₁) z₁ ∧ φ z ≤ φ z₁ ∧ ∀ i j, (i, j) ∉ fracArcs b → b₁ i j = b i j := by
      by_cases hc : 5 ≤ (fracArcs b).card
      · obtain ⟨b₁, z₁, h1, h2, h3, h4, h5⟩ := left_move φ hb hz hz0 hc
        exact ⟨b₁, z₁, h1, hn ▸ h2, h3, h4, h5⟩
      · obtain ⟨i, hi⟩ : ∃ i, 3 ≤ ((fracArcs b).filter fun e => e.1 = i).card := by
          by_contra hcon
          simp only [not_exists, not_le] at hcon
          exact hsp ⟨by omega, fun i => by have := hcon i; omega⟩
        obtain ⟨b₁, h1, h2, h3, h5⟩ := right_move hb hz hi
        exact ⟨b₁, z, h1, hn ▸ h2, h3, le_rfl, h5⟩
    obtain ⟨b', z', hb', hsp', hz', hφ', hun'⟩ := ih _ hlt b₁ rfl hb₁ z₁ hz₁
    refine ⟨b', z', hb', hsp', hz', hφ₁.trans hφ', fun i j hij => ?_⟩
    rw [hun' i j (notMem_fracArcs_of_eq hij (hun₁ i j hij)), hun₁ i j hij]

end AgenticConjectures.LaplacianPolygonOrderFour
