import AgenticConjectures.LaplacianPolygonOrderFour.Basic

/-!
# Eigenvalues of real `4 × 4` matrices: right and left eigenvectors, scaling, conjugation
-/

namespace AgenticConjectures.LaplacianPolygonOrderFour

open Complex Matrix

/-- `z` is an eigenvalue iff it has a nonzero right eigenvector. -/
theorem isEig_iff_right {A : Matrix (Fin 4) (Fin 4) ℝ} {z : ℂ} :
    IsEig A z ↔ ∃ v : Fin 4 → ℂ, v ≠ 0 ∧ A.map ((↑) : ℝ → ℂ) *ᵥ v = z • v := by
  unfold IsEig
  rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨v, hv, hv0⟩
    exact ⟨v, hv0, by simpa [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] using hv⟩
  · rintro ⟨v, hv0, hv⟩
    exact ⟨v, by simpa [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] using hv, hv0⟩

/-- `z` is an eigenvalue iff `det (z - A) = 0`. -/
theorem isEig_iff_det {A : Matrix (Fin 4) (Fin 4) ℝ} {z : ℂ} :
    IsEig A z ↔ (z • (1 : Matrix (Fin 4) (Fin 4) ℂ) - A.map ((↑) : ℝ → ℂ)).det = 0 := by
  rw [isEig_iff_right, ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv0, hv⟩
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, hv, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  · rintro ⟨v, hv0, hv⟩
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv.symm

/-- `z` is an eigenvalue iff it has a nonzero left eigenvector. -/
theorem isEig_iff_left {A : Matrix (Fin 4) (Fin 4) ℝ} {z : ℂ} :
    IsEig A z ↔ ∃ y : Fin 4 → ℂ, y ≠ 0 ∧ y ᵥ* A.map ((↑) : ℝ → ℂ) = z • y := by
  rw [isEig_iff_det, ← Matrix.exists_vecMul_eq_zero_iff]
  constructor
  · rintro ⟨y, hy0, hy⟩
    refine ⟨y, hy0, ?_⟩
    rw [Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one, sub_eq_zero] at hy
    exact hy.symm
  · rintro ⟨y, hy0, hy⟩
    refine ⟨y, hy0, ?_⟩
    rw [Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one, hy, sub_self]

/-- Eigenvalues of a real matrix come in conjugate pairs. -/
theorem IsEig.conj {A : Matrix (Fin 4) (Fin 4) ℝ} {z : ℂ} (h : IsEig A z) :
    IsEig A (starRingEnd ℂ z) := by
  obtain ⟨v, hv0, hv⟩ := isEig_iff_right.1 h
  refine isEig_iff_right.2 ⟨fun i => starRingEnd ℂ (v i), ?_, ?_⟩
  · intro h0
    apply hv0
    funext i
    simpa using congrFun h0 i
  · funext i
    have := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    have h2 := congrArg (starRingEnd ℂ) this
    simpa [map_sum, map_mul] using h2

/-- Scaling a matrix scales its eigenvalues. -/
theorem IsEig.smul {A : Matrix (Fin 4) (Fin 4) ℝ} {z : ℂ} (h : IsEig A z) (c : ℝ) :
    IsEig (c • A) (c * z) := by
  obtain ⟨v, hv0, hv⟩ := isEig_iff_right.1 h
  refine isEig_iff_right.2 ⟨v, hv0, ?_⟩
  have : (c • A).map ((↑) : ℝ → ℂ) = (c : ℂ) • A.map ((↑) : ℝ → ℂ) := by
    ext i j
    simp
  rw [this, Matrix.smul_mulVec, hv, smul_smul]

/-- Rows of `lap b` sum to zero. -/
theorem lap_row_sum (b : Fin 4 → Fin 4 → ℝ) (i : Fin 4) : ∑ j, lap b i j = 0 := by
  simp [lap, Matrix.sub_apply, Matrix.diagonal_apply, Finset.sum_sub_distrib]

/-- Membership in `Λ₄` in terms of unscaled weights in `[0, 1]`. -/
theorem mem_Λ₄_iff {z : ℂ} : z ∈ Λ₄ ↔ ∃ b, InBox b ∧ IsEig (lap b) (4 * z) := by
  constructor
  · rintro ⟨L, ⟨hrow, hoff⟩, hz⟩
    refine ⟨fun i j => -4 * L i j, fun i j hij => ⟨by linarith [(hoff i j hij).2],
      by linarith [(hoff i j hij).1]⟩, ?_⟩
    have hL : lap (fun i j => -4 * L i j) = (4 : ℝ) • L := by
      ext i j
      by_cases hij : i = j
      · subst hij
        have := hrow i
        simp only [lap, Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.of_apply,
          Matrix.smul_apply, smul_eq_mul]
        rw [← Finset.mul_sum, this]
        ring
      · simp [lap, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij]
    rw [hL]
    exact_mod_cast hz.smul 4
  · rintro ⟨b, hb, hz⟩
    refine ⟨(1 / 4 : ℝ) • lap b, ⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
    · simp [Matrix.smul_apply, ← Finset.mul_sum, lap_row_sum]
    · have h1 := hb i j hij
      simp only [lap, Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij,
        Matrix.of_apply, smul_eq_mul]
      constructor <;> linarith [h1.1, h1.2]
    · have := hz.smul (1 / 4)
      convert this using 1
      push_cast
      ring

end AgenticConjectures.LaplacianPolygonOrderFour
