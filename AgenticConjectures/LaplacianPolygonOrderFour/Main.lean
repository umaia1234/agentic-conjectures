import AgenticConjectures.LaplacianPolygonOrderFour.Converse
import AgenticConjectures.LaplacianPolygonOrderFour.Reduction
import AgenticConjectures.LaplacianPolygonOrderFour.Sector
import AgenticConjectures.LaplacianPolygonOrderFour.Polygon

/-!
# Order-four polygon question: reduction to the face bounds

`exists_sparse` moves an eigenvalue in a chosen real direction while making the weights sparse.
With the direction `Im` and `phi_criterion`, `FaceBound` gives `|Im z| ≤ 1` for every eigenvalue
of every `lap b` with `b` in the box. With the direction `Im - Re` and `sector_criterion`,
`SectorFaceBound` gives `|Im z| ≤ Re z`, and the complement `b ↦ 1 - b` gives
`|Im z| ≤ 4 - Re z`. Rescaling by `4` gives `z4_statement` and `statement`.

The converses `phi_nonneg_of_im_le` and `psi_nonneg_of_sector` give the other directions, so
`z4_statement ↔ FaceBound` and `statement ↔ FaceBound ∧ SectorFaceBound`.
-/

namespace AgenticConjectures.LaplacianPolygonOrderFour

open Complex

/-- Under `FaceBound`, every eigenvalue of `lap b`, `b` in the box, has `|Im z| ≤ 1`. -/
theorem im_le_one_of_faceBound (hF : FaceBound) {b : Fin 4 → Fin 4 → ℝ} (hb : InBox b) {z : ℂ}
    (hz : IsEig (lap b) z) : |z.im| ≤ 1 := by
  have key : ∀ {b : Fin 4 → Fin 4 → ℝ} {z : ℂ}, InBox b → IsEig (lap b) z → z.im ≤ 1 := by
    intro b z hb hz
    obtain ⟨b', z', hb', hs, hz', hle, -⟩ := exists_sparse Complex.imLm hb hz
    have h1 := phi_criterion hb' hz' (hF b' hb' hs)
    simp only [Complex.imLm_coe] at hle
    linarith [le_abs_self z'.im]
  rw [abs_le]
  refine ⟨?_, key hb hz⟩
  have := key hb hz.conj
  rw [Complex.conj_im] at this
  linarith

/-- Under `SectorFaceBound`, every eigenvalue of `lap b`, `b` in the box, has
`|Im z| ≤ Re z`. -/
theorem sector_of_sectorFaceBound (hS : SectorFaceBound) {b : Fin 4 → Fin 4 → ℝ} (hb : InBox b)
    {z : ℂ} (hz : IsEig (lap b) z) : |z.im| ≤ z.re := by
  have key : ∀ {b : Fin 4 → Fin 4 → ℝ} {z : ℂ}, InBox b → IsEig (lap b) z → z.im ≤ z.re := by
    intro b z hb hz
    obtain ⟨b', z', hb', hs, hz', hle, -⟩ := exists_sparse (Complex.imLm - Complex.reLm) hb hz
    have h1 := sector_criterion hb' hz' (hS b' hb' hs)
    simp only [LinearMap.sub_apply, Complex.imLm_coe, Complex.reLm_coe] at hle
    linarith [le_abs_self z'.im]
  rw [abs_le]
  refine ⟨?_, key hb hz⟩
  have := key hb hz.conj
  rw [Complex.conj_im, Complex.conj_re] at this
  linarith

/-- Under `SectorFaceBound`, the complement turns the sector bound at `0` into the sector
bound at `4`: `|Im z| ≤ 4 - Re z`. -/
theorem sector_four_of_sectorFaceBound (hS : SectorFaceBound) {b : Fin 4 → Fin 4 → ℝ}
    (hb : InBox b) {z : ℂ} (hz : IsEig (lap b) z) : |z.im| ≤ 4 - z.re := by
  rcases eq_or_ne z 0 with h | h
  · subst h
    norm_num
  · simpa using sector_of_sectorFaceBound hS (inBox_compl hb) (isEig_compl hz h)

/-- `|Im (4 z)| = 4 |Im z|`. -/
theorem abs_im_four_mul (z : ℂ) : |(4 * z).im| = 4 * |z.im| := by
  simp [abs_mul]

/-- `FaceBound` implies the paper's equivalent form `z(4) = 1/4`. -/
theorem z4_statement_of_faceBound (hF : FaceBound) : z4_statement := by
  refine ⟨⟨(1 + I) / 4, cycle_eig, ?_⟩, ?_⟩
  · simp [abs_of_pos]
  · rintro x ⟨z, hz, rfl⟩
    obtain ⟨b, hb, h4⟩ := mem_Λ₄_iff.1 hz
    have h := im_le_one_of_faceBound hF hb h4
    rw [abs_im_four_mul] at h
    linarith

/-- `FaceBound` and `SectorFaceBound` together settle Question 1: `Λ₄ = S₄`. -/
theorem statement_of_faceBounds (hF : FaceBound) (hS : SectorFaceBound) : statement := by
  refine Set.Subset.antisymm ?_ S4_subset_Λ4
  intro z hz
  obtain ⟨b, hb, h4⟩ := mem_Λ₄_iff.1 hz
  have h1 := im_le_one_of_faceBound hF hb h4
  have h2 := sector_of_sectorFaceBound hS hb h4
  have h3 := sector_four_of_sectorFaceBound hS hb h4
  have hre : (4 * z).re = 4 * z.re := by simp
  rw [abs_im_four_mul] at h1 h2 h3
  rw [hre] at h2 h3
  rw [S4_eq]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The paper's form `z(4) = 1/4` is equivalent to the finite-dimensional inequality
`FaceBound`. -/
theorem z4_statement_iff_faceBound : z4_statement ↔ FaceBound := by
  refine ⟨fun h b hb _ => phi_nonneg_of_im_le hb fun z hz => ?_, z4_statement_of_faceBound⟩
  obtain ⟨w, rfl⟩ : ∃ w, z = 4 * w := ⟨z / 4, by ring⟩
  have h4 := h.2 ⟨w, mem_Λ₄_iff.2 ⟨b, hb, hz⟩, rfl⟩
  rw [abs_im_four_mul]
  linarith

/-- Question 1 is equivalent to the two finite-dimensional inequalities `FaceBound` and
`SectorFaceBound`. -/
theorem statement_iff_faceBounds : statement ↔ FaceBound ∧ SectorFaceBound := by
  refine ⟨fun h => ?_, fun h => statement_of_faceBounds h.1 h.2⟩
  have hΛ : Λ₄ = S₄ := h
  have key : ∀ {b : Fin 4 → Fin 4 → ℝ}, InBox b → ∀ z, IsEig (lap b) z →
      |z.im| ≤ 1 ∧ |z.im| ≤ z.re := by
    intro b hb z hz
    obtain ⟨w, rfl⟩ : ∃ w, z = 4 * w := ⟨z / 4, by ring⟩
    have hS : w ∈ S₄ := by
      rw [← hΛ]
      exact mem_Λ₄_iff.2 ⟨b, hb, hz⟩
    rw [S4_eq] at hS
    obtain ⟨h1, -, h3⟩ := hS
    have hre : (4 * w).re = 4 * w.re := by simp
    rw [abs_im_four_mul, hre]
    exact ⟨by linarith, by linarith⟩
  exact ⟨fun b hb _ => phi_nonneg_of_im_le hb fun z hz => (key hb z hz).1,
    fun b hb _ => psi_nonneg_of_sector fun z hz => (key hb z hz).2⟩

end AgenticConjectures.LaplacianPolygonOrderFour
