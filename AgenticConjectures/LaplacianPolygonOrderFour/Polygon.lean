import AgenticConjectures.LaplacianPolygonOrderFour.Basic

/-!
# Order-four polygon question: the hexagon `S₄` lies in `Λ₄`

We describe the hexagon `S₄` by linear inequalities (`S4_eq`) and show that every point of
`S₄` is an eigenvalue of a circulant standardized Laplacian (`S4_subset_Λ4`). Two explicit
eigenvalues serve as sanity checks: `(1 + i)/4` (the directed 4-cycle, a vertex of `S₄`) and
`(3 + 2i)/8` (a 4-cycle with two chords; it lies on the top edge `Im z = 1/4` of `S₄`).
-/

namespace AgenticConjectures.LaplacianPolygonOrderFour

open Complex Matrix

/-- A nonzero vector `v` with `A v = z v` over `ℂ` shows that `z` is an eigenvalue of `A`. -/
theorem isEig_of_mulVec {A : Matrix (Fin 4) (Fin 4) ℝ} {z : ℂ} (v : Fin 4 → ℂ) (hv : v ≠ 0)
    (h : A.map ((↑) : ℝ → ℂ) *ᵥ v = z • v) : IsEig A z :=
  Module.End.hasEigenvalue_of_hasEigenvector
    (Module.End.hasEigenvector_iff.2
      ⟨Module.End.mem_eigenspace_iff.2 (by rw [Matrix.toLin'_apply]; exact h), hv⟩)

/-- The half-plane description of the hexagon is a convex set. -/
lemma convex_hexagon :
    Convex ℝ {z : ℂ | |z.im| ≤ z.re ∧ |z.im| ≤ 1 - z.re ∧ |z.im| ≤ 1 / 4} := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  have key : |(a • p + b • q).im| ≤ a * |p.im| + b * |q.im| := by
    calc |(a • p + b • q).im| = |a * p.im + b * q.im| := by simp
      _ ≤ |a * p.im| + |b * q.im| := abs_add_le _ _
      _ = a * |p.im| + b * |q.im| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hre : (a • p + b • q).re = a * p.re + b * q.re := by simp
  have e1 := mul_le_mul_of_nonneg_left hp1 ha
  have e2 := mul_le_mul_of_nonneg_left hq1 hb
  have e3 := mul_le_mul_of_nonneg_left hp2 ha
  have e4 := mul_le_mul_of_nonneg_left hq2 hb
  have e5 := mul_le_mul_of_nonneg_left hp3 ha
  have e6 := mul_le_mul_of_nonneg_left hq3 hb
  refine ⟨?_, ?_, ?_⟩
  · rw [hre]; linarith
  · rw [hre]; linarith
  · linarith

/-- The six vertices of `S₄` satisfy the half-plane inequalities. -/
lemma vertices_subset_hexagon :
    ({0, (1 + I) / 4, (1 - I) / 4, (3 + I) / 4, (3 - I) / 4, 1} : Set ℂ) ⊆
      {z : ℂ | |z.im| ≤ z.re ∧ |z.im| ≤ 1 - z.re ∧ |z.im| ≤ 1 / 4} := by
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_setOf_eq]
  norm_num [abs_div]

/-- Zonotope coordinates: a point `x + y i` of the hexagon equals
`s₁ (1 + i)/4 + s₂/2 + s₃ (1 - i)/4` with `s₁, s₂, s₃ ∈ [0, 1]`. -/
lemma zono_coords {x y : ℝ} (h1 : |y| ≤ x) (h2 : |y| ≤ 1 - x) (h3 : |y| ≤ 1 / 4) :
    ∃ s1 s2 s3 : ℝ, 0 ≤ s1 ∧ s1 ≤ 1 ∧ 0 ≤ s2 ∧ s2 ≤ 1 ∧ 0 ≤ s3 ∧ s3 ≤ 1 ∧
      x = s1 / 4 + s2 / 2 + s3 / 4 ∧ y = s1 / 4 - s3 / 4 := by
  have hy1 := le_abs_self y
  have hy2 := neg_abs_le y
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = max (4 * |y|) (4 * x - 2) := ⟨_, rfl⟩
  have hu1 : 4 * |y| ≤ u := by rw [hu]; exact le_max_left _ _
  have hu2 : 4 * x - 2 ≤ u := by rw [hu]; exact le_max_right _ _
  have hu3 : u ≤ 2 - 4 * y := by rw [hu]; exact max_le (by linarith) (by linarith)
  have hu4 : u ≤ 2 + 4 * y := by rw [hu]; exact max_le (by linarith) (by linarith)
  have hu5 : u ≤ 4 * x := by rw [hu]; exact max_le (by linarith) (by linarith)
  refine ⟨(u + 4 * y) / 2, 2 * x - u / 2, (u - 4 * y) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals linarith

/-- A convex combination of two points of a convex set lies in the set. -/
lemma combo_mem {K : Set ℂ} (hK : Convex ℝ K) {p q : ℂ} (hp : p ∈ K) (hq : q ∈ K) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : (1 - t) • p + t • q ∈ K :=
  hK hp hq (by linarith) h0 (by ring)

/-- `S₄` is the hexagon cut out by `|Im z| ≤ Re z`, `|Im z| ≤ 1 - Re z` and `|Im z| ≤ 1/4`. -/
theorem S4_eq : S₄ = {z : ℂ | |z.im| ≤ z.re ∧ |z.im| ≤ 1 - z.re ∧ |z.im| ≤ 1 / 4} := by
  apply Set.Subset.antisymm
  · exact convexHull_min vertices_subset_hexagon convex_hexagon
  · rintro z ⟨h1, h2, h3⟩
    obtain ⟨s1, s2, s3, a0, a1, b0, b1, c0, c1, hx, hy⟩ := zono_coords h1 h2 h3
    have hK : Convex ℝ S₄ := convex_convexHull ℝ _
    have mem : ∀ p ∈ ({0, (1 + I) / 4, (1 - I) / 4, (3 + I) / 4, (3 - I) / 4, 1} : Set ℂ),
        p ∈ S₄ := fun p hp => subset_convexHull ℝ _ hp
    have hO : (0 : ℂ) ∈ S₄ := mem _ (by simp)
    have hA : (1 + I) / 4 ∈ S₄ := mem _ (by simp)
    have hC : (1 - I) / 4 ∈ S₄ := mem _ (by simp)
    have hP : (3 + I) / 4 ∈ S₄ := mem _ (by simp)
    have hQ : (3 - I) / 4 ∈ S₄ := mem _ (by simp)
    have hE : (1 : ℂ) ∈ S₄ := mem _ (by simp)
    have hM : (1 / 2 : ℂ) ∈ S₄ := by
      have := combo_mem hK hO hE (t := 1 / 2) (by norm_num) (by norm_num)
      convert this using 1
      apply Complex.ext <;> simp
    -- multilinear interpolation of `s₁ (1 + i)/4 + s₂/2 + s₃ (1 - i)/4` over the cube
    have f00 := combo_mem hK hO hA a0 a1
    have f01 := combo_mem hK hC hM a0 a1
    have f10 := combo_mem hK hM hP a0 a1
    have f11 := combo_mem hK hQ hE a0 a1
    have g0 := combo_mem hK f00 f01 c0 c1
    have g1 := combo_mem hK f10 f11 c0 c1
    have h := combo_mem hK g0 g1 b0 b1
    convert h using 1
    apply Complex.ext
    · simp
      linear_combination hx
    · simp
      linear_combination hy

/-- Every point of the hexagon is an eigenvalue of a circulant standardized Laplacian. -/
theorem S4_subset_Λ4 : S₄ ⊆ Λ₄ := by
  intro z hz
  rw [S4_eq] at hz
  obtain ⟨h1, h2, h3⟩ := hz
  obtain ⟨s1, s2, s3, a0, a1, b0, b1, c0, c1, hx, hy⟩ := zono_coords h1 h2 h3
  refine ⟨!![(s1 + s2 + s3) / 4, -s1 / 4, -s2 / 4, -s3 / 4;
      -s3 / 4, (s1 + s2 + s3) / 4, -s1 / 4, -s2 / 4;
      -s2 / 4, -s3 / 4, (s1 + s2 + s3) / 4, -s1 / 4;
      -s1 / 4, -s2 / 4, -s3 / 4, (s1 + s2 + s3) / 4], ⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> simp [Fin.sum_univ_four] <;> ring
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> constructor <;> linarith
  · refine isEig_of_mulVec ![1, -I, -1, I] (fun h => by simpa using congrFun h 0) ?_
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      apply Complex.ext <;> simp <;> linarith

/-- The directed 4-cycle, scaled to a standardized Laplacian, has the eigenvalue `(1 + i)/4`. -/
theorem cycle_eig : (1 + I) / 4 ∈ Λ₄ := by
  refine ⟨!![1 / 4, -1 / 4, 0, 0; 0, 1 / 4, -1 / 4, 0; 0, 0, 1 / 4, -1 / 4; -1 / 4, 0, 0, 1 / 4],
    ⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> simp [Fin.sum_univ_four] <;> norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> norm_num
  · refine isEig_of_mulVec ![1, -I, -1, I] (fun h => by simpa using congrFun h 0) ?_
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      apply Complex.ext <;> simp <;> norm_num

/-- The matrix `(1/4) M`, where `M` is the Laplacian of the directed 4-cycle `0 → 1 → 2 → 3 → 0`
with full weights plus the chords `0 → 2` and `1 → 3` of weight `1/2`, is a standardized
Laplacian with the eigenvalue `(3 + 2i)/8`. -/
theorem h4_eig : (3 + 2 * I) / 8 ∈ Λ₄ := by
  refine ⟨!![3 / 8, -1 / 4, -1 / 8, 0; 0, 3 / 8, -1 / 4, -1 / 8; 0, 0, 1 / 4, -1 / 4;
    -1 / 4, 0, 0, 1 / 4], ⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> simp [Fin.sum_univ_four] <;> norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> norm_num
  · refine isEig_of_mulVec ![-1 / 2 - I, -4 / 5 + I / 10, -2 / 5 + 4 * I / 5, 1]
      (fun h => by simpa using congrFun h 3) ?_
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      apply Complex.ext <;> simp <;> norm_num

end AgenticConjectures.LaplacianPolygonOrderFour
