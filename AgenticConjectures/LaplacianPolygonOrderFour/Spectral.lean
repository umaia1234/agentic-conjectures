import AgenticConjectures.LaplacianPolygonOrderFour.Eigen

/-!
# Spectral facts for `lap b`: characteristic polynomial, Bendixson bound, and `Φ`

* `det_sub_lap`: `det (x - lap b) = x (x³ - σ₁ x² + σ₂ x - σ₃)`.
* `cubic_root_of_isEig`: nonzero eigenvalues are roots of the cubic factor.
* `im_le_three_halves`: Bendixson's bound `|Im z| ≤ 3/2` for weights in `[0, 1]`.
* `phiPoly_eq`: `phiPoly` evaluated at a cubic with a non-real root `α + iβ`.
* `phi_criterion`, `phi_neg_of_im`: for weights in `[0, 1]`, `Φ b ≥ 0` forces `|Im z| ≤ 1` for
  every eigenvalue `z`, and an eigenvalue with `|Im z| > 1` forces `Φ b < 0`.
-/

namespace AgenticConjectures.LaplacianPolygonOrderFour

open Complex Matrix

/-! ### The characteristic polynomial -/

/-- Cofactor expansion of a `4 × 4` determinant along the first row. -/
theorem det_fin_four {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) :
    A.det =
      A 0 0 * (A 1 1 * A 2 2 * A 3 3 - A 1 1 * A 2 3 * A 3 2 - A 1 2 * A 2 1 * A 3 3 +
          A 1 2 * A 2 3 * A 3 1 + A 1 3 * A 2 1 * A 3 2 - A 1 3 * A 2 2 * A 3 1) -
        A 0 1 * (A 1 0 * A 2 2 * A 3 3 - A 1 0 * A 2 3 * A 3 2 - A 1 2 * A 2 0 * A 3 3 +
          A 1 2 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 2 - A 1 3 * A 2 2 * A 3 0) +
        A 0 2 * (A 1 0 * A 2 1 * A 3 3 - A 1 0 * A 2 3 * A 3 1 - A 1 1 * A 2 0 * A 3 3 +
          A 1 1 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 1 - A 1 3 * A 2 1 * A 3 0) -
        A 0 3 * (A 1 0 * A 2 1 * A 3 2 - A 1 0 * A 2 2 * A 3 1 - A 1 1 * A 2 0 * A 3 2 +
          A 1 1 * A 2 2 * A 3 0 + A 1 2 * A 2 0 * A 3 1 - A 1 2 * A 2 1 * A 3 0) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply]
  simp [show Fin.succAbove (1 : Fin 4) 2 = 3 from rfl,
    show Fin.succAbove (2 : Fin 4) 1 = 1 from rfl, show Fin.succAbove (2 : Fin 4) 2 = 3 from rfl,
    show Fin.succAbove (3 : Fin 4) 1 = 1 from rfl, show Fin.succAbove (3 : Fin 4) 2 = 2 from rfl]
  ring

/-- `det (x - A)` for a real `4 × 4` matrix `A`, in terms of its trace, `c2`, `c3` and `det`. -/
theorem det_smul_one_sub (A : Matrix (Fin 4) (Fin 4) ℝ) (x : ℂ) :
    (x • (1 : Matrix (Fin 4) (Fin 4) ℂ) - A.map ((↑) : ℝ → ℂ)).det =
      x ^ 4 - (A.trace : ℂ) * x ^ 3 + (c2 A : ℂ) * x ^ 2 - (c3 A : ℂ) * x + (A.det : ℂ) := by
  rw [det_fin_four, det_fin_four A]
  simp [Matrix.trace, Fin.sum_univ_four, c2, c3, det3]
  ring

/-- `lap b` is singular: the all-ones vector lies in its kernel. -/
theorem det_lap (b : Fin 4 → Fin 4 → ℝ) : (lap b).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0), ?_⟩
  funext i
  simp [Matrix.mulVec, dotProduct, lap_row_sum]

/-- The characteristic polynomial of `lap b`: `det (x - lap b) = x (x³ - σ₁ x² + σ₂ x - σ₃)`. -/
theorem det_sub_lap (b : Fin 4 → Fin 4 → ℝ) (x : ℂ) :
    (x • (1 : Matrix (Fin 4) (Fin 4) ℂ) - (lap b).map ((↑) : ℝ → ℂ)).det =
      x * (x ^ 3 - (σ₁ b : ℂ) * x ^ 2 + (σ₂ b : ℂ) * x - (σ₃ b : ℂ)) := by
  rw [det_smul_one_sub, det_lap, σ₁, σ₂, σ₃]
  push_cast
  ring

/-- A nonzero eigenvalue of `lap b` is a root of `x³ - σ₁ x² + σ₂ x - σ₃`. -/
theorem cubic_root_of_isEig {b : Fin 4 → Fin 4 → ℝ} {z : ℂ} (hz : IsEig (lap b) z)
    (hz0 : z ≠ 0) : z ^ 3 - (σ₁ b : ℂ) * z ^ 2 + (σ₂ b : ℂ) * z - (σ₃ b : ℂ) = 0 := by
  have h := isEig_iff_det.1 hz
  rw [det_sub_lap] at h
  exact (mul_eq_zero.1 h).resolve_left hz0

/-! ### Bendixson's bound -/

/-- `|e (p q' - q p')| ≤ (p² + q² + p'² + q'²) / 2` whenever `|e| ≤ 1`. -/
theorem abs_mul_cross_le {e p q p' q' : ℝ} (he : |e| ≤ 1) :
    |e * (p * q' - q * p')| ≤ (p ^ 2 + q ^ 2 + p' ^ 2 + q' ^ 2) / 2 := by
  have hw : |p * q' - q * p'| ≤ (p ^ 2 + q ^ 2 + p' ^ 2 + q' ^ 2) / 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (p + q'), sq_nonneg (q - p'), sq_nonneg (p - q'),
      sq_nonneg (q + p')]
  rw [abs_mul]
  calc |e| * |p * q' - q * p'| ≤ 1 * |p * q' - q * p'| :=
        mul_le_mul_of_nonneg_right he (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hw

/-- Bendixson's bound in real coordinates: if `p + i q ≠ 0` is a right eigenvector of the real
matrix `L` for `α + i β` and `|L i j - L j i| ≤ 1` off the diagonal, then `|β| ≤ 3/2`. -/
theorem bendixson_aux {L : Fin 4 → Fin 4 → ℝ} {p q : Fin 4 → ℝ} {α β : ℝ}
    (hre : ∀ i, ∑ j, L i j * p j = α * p i - β * q i)
    (him : ∀ i, ∑ j, L i j * q j = α * q i + β * p i)
    (hL : ∀ i j, i ≠ j → |L i j - L j i| ≤ 1)
    (hS : 0 < ∑ i, (p i ^ 2 + q i ^ 2)) : |β| ≤ 3 / 2 := by
  simp only [Fin.sum_univ_four] at hre him hS
  have key : β * (p 0 ^ 2 + q 0 ^ 2 + (p 1 ^ 2 + q 1 ^ 2) + (p 2 ^ 2 + q 2 ^ 2) +
      (p 3 ^ 2 + q 3 ^ 2)) =
      (L 0 1 - L 1 0) * (p 0 * q 1 - q 0 * p 1) + (L 0 2 - L 2 0) * (p 0 * q 2 - q 0 * p 2) +
        (L 0 3 - L 3 0) * (p 0 * q 3 - q 0 * p 3) + (L 1 2 - L 2 1) * (p 1 * q 2 - q 1 * p 2) +
        (L 1 3 - L 3 1) * (p 1 * q 3 - q 1 * p 3) +
        (L 2 3 - L 3 2) * (p 2 * q 3 - q 2 * p 3) := by
    linear_combination q 0 * hre 0 - p 0 * him 0 + q 1 * hre 1 - p 1 * him 1 +
      q 2 * hre 2 - p 2 * him 2 + q 3 * hre 3 - p 3 * him 3
  have h01 := abs_le.1 (abs_mul_cross_le (p := p 0) (q := q 0) (p' := p 1) (q' := q 1)
    (hL 0 1 (by decide)))
  have h02 := abs_le.1 (abs_mul_cross_le (p := p 0) (q := q 0) (p' := p 2) (q' := q 2)
    (hL 0 2 (by decide)))
  have h03 := abs_le.1 (abs_mul_cross_le (p := p 0) (q := q 0) (p' := p 3) (q' := q 3)
    (hL 0 3 (by decide)))
  have h12 := abs_le.1 (abs_mul_cross_le (p := p 1) (q := q 1) (p' := p 2) (q' := q 2)
    (hL 1 2 (by decide)))
  have h13 := abs_le.1 (abs_mul_cross_le (p := p 1) (q := q 1) (p' := p 3) (q' := q 3)
    (hL 1 3 (by decide)))
  have h23 := abs_le.1 (abs_mul_cross_le (p := p 2) (q := q 2) (p' := p 3) (q' := q 3)
    (hL 2 3 (by decide)))
  have hup : β * (p 0 ^ 2 + q 0 ^ 2 + (p 1 ^ 2 + q 1 ^ 2) + (p 2 ^ 2 + q 2 ^ 2) +
      (p 3 ^ 2 + q 3 ^ 2)) ≤ 3 / 2 * (p 0 ^ 2 + q 0 ^ 2 + (p 1 ^ 2 + q 1 ^ 2) +
      (p 2 ^ 2 + q 2 ^ 2) + (p 3 ^ 2 + q 3 ^ 2)) := by
    linarith [h01.2, h02.2, h03.2, h12.2, h13.2, h23.2]
  have hlo : -(3 / 2) * (p 0 ^ 2 + q 0 ^ 2 + (p 1 ^ 2 + q 1 ^ 2) + (p 2 ^ 2 + q 2 ^ 2) +
      (p 3 ^ 2 + q 3 ^ 2)) ≤ β * (p 0 ^ 2 + q 0 ^ 2 + (p 1 ^ 2 + q 1 ^ 2) +
      (p 2 ^ 2 + q 2 ^ 2) + (p 3 ^ 2 + q 3 ^ 2)) := by
    linarith [h01.1, h02.1, h03.1, h12.1, h13.1, h23.1]
  exact abs_le.2 ⟨le_of_mul_le_mul_right hlo hS, le_of_mul_le_mul_right hup hS⟩

/-- Bendixson's bound: for weights in `[0, 1]`, every eigenvalue of `lap b` has
`|Im z| ≤ 3/2`. -/
theorem im_le_three_halves {b : Fin 4 → Fin 4 → ℝ} (hb : InBox b) {z : ℂ}
    (hz : IsEig (lap b) z) : |z.im| ≤ 3 / 2 := by
  obtain ⟨v, hv0, hv⟩ := isEig_iff_right.1 hz
  have hrow : ∀ i, ∑ j, (lap b i j : ℂ) * v j = z * v i := fun i => by
    simpa [Matrix.mulVec, dotProduct] using congrFun hv i
  refine bendixson_aux (L := lap b) (p := fun i => (v i).re) (q := fun i => (v i).im)
    (α := z.re) (fun i => ?_) (fun i => ?_) (fun i j hij => ?_) ?_
  · simpa [Complex.re_sum, Complex.mul_re] using congrArg Complex.re (hrow i)
  · simpa [Complex.im_sum, Complex.mul_im] using congrArg Complex.im (hrow i)
  · have h1 := hb i j hij
    have h2 := hb j i (Ne.symm hij)
    simp only [lap, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij,
      Matrix.diagonal_apply_ne _ (Ne.symm hij), Matrix.of_apply]
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.1 hv0
    have h1 : 0 < (v i).re ^ 2 + (v i).im ^ 2 := by
      have := Complex.normSq_pos.2 hi
      rw [Complex.normSq_apply] at this
      nlinarith
    exact lt_of_lt_of_le h1 (Finset.single_le_sum (f := fun j => (v j).re ^ 2 + (v j).im ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i))

/-! ### The polynomial `Φ` -/

/-- If `α + iβ` with `β ≠ 0` is a root of `x³ - s₁ x² + s₂ x - s₃`, then the roots are
`α ± iβ` and `s₁ - 2α`, and `phiPoly s₁ s₂ s₃ = ∏_{a<b} ((r_a - r_b)² + 4)` takes this form. -/
theorem phiPoly_eq {s₁ s₂ s₃ α β : ℝ} (hβ : β ≠ 0)
    (hroot : (⟨α, β⟩ : ℂ) ^ 3 - (s₁ : ℂ) * (⟨α, β⟩ : ℂ) ^ 2 + (s₂ : ℂ) * ⟨α, β⟩ - (s₃ : ℂ) = 0) :
    phiPoly s₁ s₂ s₃ =
      4 * (1 - β ^ 2) * (((s₁ - 3 * α) ^ 2 - β ^ 2 + 4) ^ 2 + 4 * (s₁ - 3 * α) ^ 2 * β ^ 2) := by
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
  unfold phiPoly
  ring

/-- The second factor in `phiPoly_eq` is positive when `β ≠ 0` and `β² < 4`. -/
theorem bracket_pos {u β : ℝ} (hβ : β ≠ 0) (hβ2 : β ^ 2 < 4) :
    0 < (u ^ 2 - β ^ 2 + 4) ^ 2 + 4 * u ^ 2 * β ^ 2 := by
  rcases eq_or_ne u 0 with h | h
  · subst h
    have h4 : 0 < 4 - β ^ 2 := by linarith
    nlinarith [mul_pos h4 h4]
  · have : 0 < u ^ 2 * β ^ 2 := by positivity
    nlinarith [sq_nonneg (u ^ 2 - β ^ 2 + 4)]

/-- For weights in `[0, 1]` and a non-real eigenvalue `z` of `lap b`,
`Φ b = 4 (1 - (Im z)²) B` with `B > 0`. -/
theorem Φ_eq_of_isEig {b : Fin 4 → Fin 4 → ℝ} (hb : InBox b) {z : ℂ} (hz : IsEig (lap b) z)
    (hβ : z.im ≠ 0) : ∃ B, 0 < B ∧ Φ b = 4 * (1 - z.im ^ 2) * B := by
  have hz0 : z ≠ 0 := fun h => hβ (by rw [h, Complex.zero_im])
  have hcub := cubic_root_of_isEig hz hz0
  have hΦ : Φ b = 4 * (1 - z.im ^ 2) * (((σ₁ b - 3 * z.re) ^ 2 - z.im ^ 2 + 4) ^ 2 +
      4 * (σ₁ b - 3 * z.re) ^ 2 * z.im ^ 2) :=
    phiPoly_eq hβ (by rwa [Complex.eta])
  have h32 := im_le_three_halves hb hz
  have hsq : z.im ^ 2 < 4 := by nlinarith [abs_nonneg z.im, sq_abs z.im]
  exact ⟨_, bracket_pos hβ hsq, hΦ⟩

/-- For weights in `[0, 1]`: if `Φ b ≥ 0`, every eigenvalue `z` of `lap b` has `|Im z| ≤ 1`. -/
theorem phi_criterion {b : Fin 4 → Fin 4 → ℝ} (hb : InBox b) {z : ℂ} (hz : IsEig (lap b) z)
    (hΦ : 0 ≤ Φ b) : |z.im| ≤ 1 := by
  rcases eq_or_ne z.im 0 with h | h
  · rw [h, abs_zero]
    norm_num
  obtain ⟨B, hB, hΦB⟩ := Φ_eq_of_isEig hb hz h
  rw [hΦB] at hΦ
  have := nonneg_of_mul_nonneg_left hΦ hB
  exact (sq_le_one_iff_abs_le_one _).1 (by linarith)

/-- For weights in `[0, 1]`: an eigenvalue `z` of `lap b` with `|Im z| > 1` forces `Φ b < 0`. -/
theorem phi_neg_of_im {b : Fin 4 → Fin 4 → ℝ} (hb : InBox b) {z : ℂ} (hz : IsEig (lap b) z)
    (h1 : 1 < |z.im|) : Φ b < 0 := by
  have h : z.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at h1
    norm_num at h1
  obtain ⟨B, hB, hΦB⟩ := Φ_eq_of_isEig hb hz h
  rw [hΦB]
  have := (one_lt_sq_iff_one_lt_abs _).2 h1
  exact mul_neg_of_neg_of_pos (by linarith) hB

end AgenticConjectures.LaplacianPolygonOrderFour
