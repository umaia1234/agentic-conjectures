import AgenticConjectures.LaplacianPolygonOrderFour.Sector

/-!
# Converses of `phi_criterion` and `sector_criterion`

* `exists_cubic_root`, `isEig_of_cubic_root`: the cubic `x³ - σ₁ x² + σ₂ x - σ₃` has a complex
  root, and each of its roots is an eigenvalue of `lap b`.
* `phiPoly_factor`, `sectorPoly_factor`: `phiPoly` and `sectorPoly` of the cubic
  `(x - r) (x² - p x + q)`.
* `phi_nonneg_of_im_le`: for weights in `[0, 1]`, if every eigenvalue `z` of `lap b` has
  `|Im z| ≤ 1`, then `Φ b ≥ 0`.
* `psi_nonneg_of_sector`: if every eigenvalue `z` of `lap b` has `|Im z| ≤ Re z`, then
  `Ψ b ≥ 0`.

Together with `phi_criterion` and `sector_criterion` this makes both criteria equivalences.

Proof: take a root `z` of the cubic. If `Im z ≠ 0`, then `z` is an eigenvalue and
`Φ_eq_of_isEig`, `sectorPoly_eq` apply. If `z = r` is real, the cubic is
`(x - r) (x² - p x + q)`; when `p² < 4 q`, the eigenvalue `p / 2 + i √(q - p² / 4)` gives
`p² - 4 q + 4 ≥ 0`, resp. `p² - 2 q ≥ 0`, and the factorizations above finish.
-/

namespace AgenticConjectures.LaplacianPolygonOrderFour

open Complex

/-! ### Roots of the cubic factor -/

open Polynomial in
/-- The cubic `x³ - σ₁ x² + σ₂ x - σ₃` has a complex root (fundamental theorem of algebra). -/
theorem exists_cubic_root (b : Fin 4 → Fin 4 → ℝ) :
    ∃ z : ℂ, z ^ 3 - (σ₁ b : ℂ) * z ^ 2 + (σ₂ b : ℂ) * z - (σ₃ b : ℂ) = 0 := by
  have hdeg : (X ^ 3 - C (σ₁ b : ℂ) * X ^ 2 + C (σ₂ b : ℂ) * X - C (σ₃ b : ℂ)).natDegree = 3 := by
    compute_degree!
  obtain ⟨z, hz⟩ := Complex.exists_root (natDegree_pos_iff_degree_pos.1 (by rw [hdeg]; norm_num))
  exact ⟨z, by simpa using hz⟩

/-- A root of `x³ - σ₁ x² + σ₂ x - σ₃` is an eigenvalue of `lap b`, because
`det (z - lap b) = z (z³ - σ₁ z² + σ₂ z - σ₃)`. -/
theorem isEig_of_cubic_root {b : Fin 4 → Fin 4 → ℝ} {z : ℂ}
    (h : z ^ 3 - (σ₁ b : ℂ) * z ^ 2 + (σ₂ b : ℂ) * z - (σ₃ b : ℂ) = 0) : IsEig (lap b) z := by
  rw [isEig_iff_det, det_sub_lap, h, mul_zero]

/-- A real root `r` of `x³ - σ₁ x² + σ₂ x - σ₃` splits off the factor `x - r`: the cubic is
`(x - r) (x² - p x + q)`, i.e. `σ₁ = r + p`, `σ₂ = r p + q` and `σ₃ = r q`. -/
theorem exists_split_of_im_eq_zero {b : Fin 4 → Fin 4 → ℝ} {z : ℂ}
    (hz : z ^ 3 - (σ₁ b : ℂ) * z ^ 2 + (σ₂ b : ℂ) * z - (σ₃ b : ℂ) = 0) (him : z.im = 0) :
    ∃ r p q : ℝ, σ₁ b = r + p ∧ σ₂ b = r * p + q ∧ σ₃ b = r * q := by
  obtain ⟨r, rfl⟩ : ∃ r : ℝ, z = r := ⟨z.re, Complex.ext (by simp) (by simp [him])⟩
  have hr : r ^ 3 - σ₁ b * r ^ 2 + σ₂ b * r - σ₃ b = 0 := by exact_mod_cast hz
  exact ⟨r, σ₁ b - r, σ₂ b - r * (σ₁ b - r), by ring, by ring, by linear_combination -hr⟩

/-- If the cubic of `lap b` is `(x - r) (x² - p x + q)` with `p² < 4 q`, then `lap b` has the
non-real eigenvalue `p / 2 + i β` with `β > 0` and `β² = q - p² / 4`. -/
theorem exists_isEig_of_split {b : Fin 4 → Fin 4 → ℝ} {r p q : ℝ} (h1 : σ₁ b = r + p)
    (h2 : σ₂ b = r * p + q) (h3 : σ₃ b = r * q) (hd : p ^ 2 - 4 * q < 0) :
    ∃ β : ℝ, 0 < β ∧ β ^ 2 = q - p ^ 2 / 4 ∧ IsEig (lap b) ⟨p / 2, β⟩ := by
  obtain ⟨β, hβ, hβ2⟩ : ∃ β : ℝ, 0 < β ∧ β ^ 2 = q - p ^ 2 / 4 :=
    ⟨_, Real.sqrt_pos.2 (by linarith), Real.sq_sqrt (by linarith)⟩
  refine ⟨β, hβ, hβ2, isEig_of_cubic_root ?_⟩
  have hw : (⟨p / 2, β⟩ : ℂ) = (p : ℂ) / 2 + (β : ℂ) * I := Complex.ext (by simp) (by simp)
  have hβ2c : (β : ℂ) ^ 2 = (q : ℂ) - (p : ℂ) ^ 2 / 4 := by exact_mod_cast hβ2
  rw [hw, h1, h2, h3]
  push_cast
  linear_combination ((p : ℂ) / 2 + (β : ℂ) * I - r) * ((β : ℂ) ^ 2 * I_sq - hβ2c)

/-! ### `phiPoly` and `sectorPoly` with a real root -/

/-- `phiPoly` of the cubic `(x - r) (x² - p x + q)`, whose roots are `r` and the roots
`u, v` of `x² - p x + q`: the factors are `((r - u)² + 4) ((r - v)² + 4)` and
`(u - v)² + 4 = p² - 4 q + 4`. -/
theorem phiPoly_factor (r p q : ℝ) :
    phiPoly (r + p) (r * p + q) (r * q) =
      ((r ^ 2 - p * r + q) ^ 2 + 8 * (r - p / 2) ^ 2 + 2 * (p ^ 2 - 4 * q) + 16) *
        (p ^ 2 - 4 * q + 4) := by
  unfold phiPoly
  ring

/-- `sectorPoly` of the cubic `(x - r) (x² - p x + q)`, whose roots are `r` and the roots
`u, v` of `x² - p x + q`: the factors are `u² + v² = p² - 2 q` and
`(r² + u²) (r² + v²)`. -/
theorem sectorPoly_factor (r p q : ℝ) :
    sectorPoly (r + p) (r * p + q) (r * q) =
      (p ^ 2 - 2 * q) * (r ^ 4 + r ^ 2 * (p ^ 2 - 2 * q) + q ^ 2) := by
  unfold sectorPoly
  ring

/-! ### The converses -/

/-- For weights in `[0, 1]`: if every eigenvalue `z` of `lap b` has `|Im z| ≤ 1`, then
`Φ b ≥ 0`. This is the converse of `phi_criterion`. -/
theorem phi_nonneg_of_im_le {b : Fin 4 → Fin 4 → ℝ} (hb : InBox b)
    (h : ∀ z, IsEig (lap b) z → |z.im| ≤ 1) : 0 ≤ Φ b := by
  obtain ⟨z, hz⟩ := exists_cubic_root b
  rcases eq_or_ne z.im 0 with him | him
  · obtain ⟨r, p, q, h1, h2, h3⟩ := exists_split_of_im_eq_zero hz him
    have hG : 0 ≤ p ^ 2 - 4 * q + 4 := by
      rcases le_or_gt 0 (p ^ 2 - 4 * q) with hd | hd
      · linarith
      · obtain ⟨β, -, hβ2, hw⟩ := exists_isEig_of_split h1 h2 h3 hd
        have h1β := (sq_le_one_iff_abs_le_one β).2 (h _ hw)
        linarith
    have hF : 0 ≤ (r ^ 2 - p * r + q) ^ 2 + 8 * (r - p / 2) ^ 2 + 2 * (p ^ 2 - 4 * q) + 16 := by
      linarith [sq_nonneg (r ^ 2 - p * r + q), sq_nonneg (r - p / 2)]
    rw [Φ, h1, h2, h3, phiPoly_factor]
    exact mul_nonneg hF hG
  · have hzE := isEig_of_cubic_root hz
    obtain ⟨B, hB, hΦB⟩ := Φ_eq_of_isEig hb hzE him
    have hsq := (sq_le_one_iff_abs_le_one z.im).2 (h z hzE)
    rw [hΦB]
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hB.le

/-- If every eigenvalue `z` of `lap b` has `|Im z| ≤ Re z`, then `Ψ b ≥ 0`. This is the
converse of `sector_criterion`. -/
theorem psi_nonneg_of_sector {b : Fin 4 → Fin 4 → ℝ}
    (h : ∀ z, IsEig (lap b) z → |z.im| ≤ z.re) : 0 ≤ Ψ b := by
  obtain ⟨z, hz⟩ := exists_cubic_root b
  rcases eq_or_ne z.im 0 with him | him
  · obtain ⟨r, p, q, h1, h2, h3⟩ := exists_split_of_im_eq_zero hz him
    have hE : 0 ≤ p ^ 2 - 2 * q := by
      rcases le_or_gt 0 (p ^ 2 - 4 * q) with hd | hd
      · linarith [sq_nonneg p]
      · obtain ⟨β, hβ, hβ2, hw⟩ := exists_isEig_of_split h1 h2 h3 hd
        have hβp : β ^ 2 ≤ (p / 2) ^ 2 :=
          pow_le_pow_left₀ hβ.le ((le_abs_self β).trans (h _ hw)) 2
        linarith
    rw [Ψ, h1, h2, h3, sectorPoly_factor]
    exact mul_nonneg hE (add_nonneg (add_nonneg (by positivity) (mul_nonneg (sq_nonneg r) hE))
      (sq_nonneg q))
  · have hzE := isEig_of_cubic_root hz
    have hΨB : Ψ b = 2 * (z.re ^ 2 - z.im ^ 2) *
        (((σ₁ b - 2 * z.re) ^ 2 + z.re ^ 2 - z.im ^ 2) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2) :=
      sectorPoly_eq him (by rwa [Complex.eta])
    have hsq : z.im ^ 2 ≤ z.re ^ 2 := sq_le_sq.2 ((h z hzE).trans (le_abs_self _))
    rw [hΨB]
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)

end AgenticConjectures.LaplacianPolygonOrderFour
