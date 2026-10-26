import AgenticConjectures.LaplacianPolygonOrderFour.Spectral

/-!
# The sector bound `|Im z| ≤ Re z` and the complement `b ↦ 1 - b`

* `re_pos_of_isEig`, `re_nonneg_of_isEig`: by Gershgorin's circle theorem, every eigenvalue `z`
  of `lap b` with nonnegative weights has `Re z ≥ 0`, and `Re z > 0` unless `z = 0`.
* `sectorPoly_eq`: `sectorPoly` evaluated at a cubic with a non-real root `α + iβ`.
* `sector_criterion`: for weights in `[0, 1]`, `Ψ b ≥ 0` forces `|Im z| ≤ Re z` for every
  eigenvalue `z` of `lap b`.
* `inBox_compl`, `isEig_compl`: the complement `b ↦ 1 - b` keeps the weights in `[0, 1]` and
  sends each nonzero eigenvalue `z` of `lap b` to the eigenvalue `4 - z` of `lap (1 - b)`,
  because `lap (1 - b) = 4 - J - lap b` with `J` the all-ones matrix.
-/

namespace AgenticConjectures.LaplacianPolygonOrderFour

open Complex Matrix

/-! ### Gershgorin's bound `Re z ≥ 0` -/

/-- A nonzero point of the closed disc with center `d` and radius `d` has positive real
part. -/
theorem re_pos_of_norm_sub_le {z : ℂ} {d : ℝ} (h : ‖z - d‖ ≤ d) (hz0 : z ≠ 0) : 0 < z.re := by
  have hd : 0 ≤ d := (norm_nonneg _).trans h
  have h2 : ‖z - d‖ ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [Complex.sq_norm, Complex.normSq_apply] at h2
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero] at h2
  have h3 := Complex.normSq_pos.2 hz0
  rw [Complex.normSq_apply] at h3
  nlinarith

/-- Gershgorin: a nonzero eigenvalue of `lap b` with nonnegative weights has positive real part. -/
theorem re_pos_of_isEig {b : Fin 4 → Fin 4 → ℝ} (hb : InBox b) {z : ℂ} (hz : IsEig (lap b) z)
    (hz0 : z ≠ 0) : 0 < z.re := by
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hz
  have hoff : ∀ j ∈ Finset.univ.erase k, ‖((lap b).map ((↑) : ℝ → ℂ)) k j‖ = b k j := by
    intro j hj
    have hkj : k ≠ j := (Finset.ne_of_mem_erase hj).symm
    rw [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs]
    simp only [lap, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hkj, Matrix.of_apply,
      zero_sub, abs_neg]
    exact abs_of_nonneg (hb k j hkj).1
  have hdiag : lap b k k = ∑ j ∈ Finset.univ.erase k, b k j := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ k)]
    simp only [lap, Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.of_apply]
  rw [mem_closedBall_iff_norm, Matrix.map_apply, Finset.sum_congr rfl hoff, ← hdiag] at hk
  exact re_pos_of_norm_sub_le hk hz0

/-- Every eigenvalue of `lap b` with nonnegative weights has nonnegative real part. -/
theorem re_nonneg_of_isEig {b : Fin 4 → Fin 4 → ℝ} (hb : InBox b) {z : ℂ}
    (hz : IsEig (lap b) z) : 0 ≤ z.re := by
  rcases eq_or_ne z 0 with h | h
  · rw [h, Complex.zero_re]
  · exact (re_pos_of_isEig hb hz h).le

/-! ### The polynomial `Ψ` -/

/-- If `α + iβ` with `β ≠ 0` is a root of `x³ - s₁ x² + s₂ x - s₃`, then the roots are `α ± iβ`
and `c = s₁ - 2α`. Their squares are `c²` and `u ± iw` with `u = α² - β²`, `w = 2αβ`, and
`sectorPoly s₁ s₂ s₃ = e₁ e₂ - e₃ = 2u ((c² + u)² + w²)`. -/
theorem sectorPoly_eq {s₁ s₂ s₃ α β : ℝ} (hβ : β ≠ 0)
    (hroot : (⟨α, β⟩ : ℂ) ^ 3 - (s₁ : ℂ) * (⟨α, β⟩ : ℂ) ^ 2 + (s₂ : ℂ) * ⟨α, β⟩ - (s₃ : ℂ) = 0) :
    sectorPoly s₁ s₂ s₃ =
      2 * (α ^ 2 - β ^ 2) * (((s₁ - 2 * α) ^ 2 + α ^ 2 - β ^ 2) ^ 2 + 4 * α ^ 2 * β ^ 2) := by
  have hre := congrArg Complex.re hroot
  have him := congrArg Complex.im hroot
  simp only [pow_succ, pow_zero, one_mul, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.zero_im] at hre him
  have h2 : s₂ = 2 * α * s₁ - 3 * α ^ 2 + β ^ 2 := by
    have h : β * (s₂ - (2 * α * s₁ - 3 * α ^ 2 + β ^ 2)) = 0 := by linear_combination him
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h hβ
    · linarith
  have h3 : s₃ = (s₁ - 2 * α) * (α ^ 2 + β ^ 2) := by linear_combination -hre + α * h2
  subst h2 h3
  unfold sectorPoly
  ring

/-- For weights in `[0, 1]`: if `Ψ b ≥ 0`, every eigenvalue `z` of `lap b` has `|Im z| ≤ Re z`. -/
theorem sector_criterion {b : Fin 4 → Fin 4 → ℝ} (hb : InBox b) {z : ℂ} (hz : IsEig (lap b) z)
    (hΨ : 0 ≤ Ψ b) : |z.im| ≤ z.re := by
  rcases eq_or_ne z.im 0 with h | h
  · rw [h, abs_zero]
    exact re_nonneg_of_isEig hb hz
  have hz0 : z ≠ 0 := fun h0 => h (by rw [h0, Complex.zero_im])
  have hα := re_pos_of_isEig hb hz hz0
  have hcub := cubic_root_of_isEig hz hz0
  have hΨB : Ψ b = 2 * (z.re ^ 2 - z.im ^ 2) *
      (((σ₁ b - 2 * z.re) ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2) :=
    sectorPoly_eq h (by rwa [Complex.eta])
  have hB : 0 < ((σ₁ b - 2 * z.re) ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2 := by
    have : 0 < z.re ^ 2 * z.im ^ 2 := by positivity
    nlinarith [sq_nonneg ((σ₁ b - 2 * z.re) ^ 2 + z.re ^ 2 - z.im ^ 2)]
  rw [hΨB] at hΨ
  have h2 := nonneg_of_mul_nonneg_left hΨ hB
  rw [← abs_of_pos hα]
  exact sq_le_sq.1 (by linarith)

/-! ### The complement `b ↦ 1 - b` -/

/-- The complement `b ↦ 1 - b` keeps the twelve weights in `[0, 1]`. -/
theorem inBox_compl {b : Fin 4 → Fin 4 → ℝ} (hb : InBox b) : InBox (fun i j => 1 - b i j) :=
  fun i j hij => ⟨by linarith [(hb i j hij).2], by linarith [(hb i j hij).1]⟩

/-- Entrywise, `lap (1 - b) = 4 - J - lap b` with `J` the all-ones matrix. -/
theorem lap_compl_apply (b : Fin 4 → Fin 4 → ℝ) (i j : Fin 4) :
    lap (fun i j => 1 - b i j) i j = (if i = j then 4 else 0) - 1 - lap b i j := by
  by_cases hij : i = j
  · subst hij
    simp only [lap, Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.of_apply, if_true,
      Fin.sum_univ_four]
    ring
  · simp only [lap, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij, Matrix.of_apply, if_neg hij]
    ring

/-- Complement: the nonzero eigenvalues of `lap (1 - b)` are `4 - z`. -/
theorem isEig_compl {b : Fin 4 → Fin 4 → ℝ} {z : ℂ} (hz : IsEig (lap b) z) (hz0 : z ≠ 0) :
    IsEig (lap (fun i j => 1 - b i j)) (4 - z) := by
  obtain ⟨y, hy0, hy⟩ := isEig_iff_left.1 hz
  refine isEig_iff_left.2 ⟨y, hy0, ?_⟩
  have hcol : ∀ j, ∑ i, y i * (lap b i j : ℂ) = z * y j := fun j => by
    simpa [Matrix.vecMul, dotProduct] using congrFun hy j
  have hsum : ∑ i, y i = 0 := by
    have h1 : ∑ i, ∑ j, y i * (lap b i j : ℂ) = z * ∑ j, y j := by
      rw [Finset.sum_comm, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => hcol j
    have h2 : ∑ i, ∑ j, y i * (lap b i j : ℂ) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Finset.mul_sum, ← Complex.ofReal_sum, lap_row_sum, Complex.ofReal_zero, mul_zero]
    rw [h2] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left hz0
  have hterm : ∀ j i, y i * (lap (fun i j => 1 - b i j) i j : ℂ) =
      (if i = j then 4 * y i else 0) - y i - y i * (lap b i j : ℂ) := by
    intro j i
    rw [lap_compl_apply]
    by_cases hij : i = j
    · simp only [if_pos hij]
      push_cast
      ring
    · simp only [if_neg hij]
      push_cast
      ring
  funext j
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun i _ => hterm j i, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq_of_mem' _ _ _ (Finset.mem_univ j), hsum, hcol j]
  ring

end AgenticConjectures.LaplacianPolygonOrderFour
