import Mathlib

/-!
# Order-four polygon question: definitions

Standardized Laplacians of order 4, the eigenvalue set `Λ₄`, the hexagon `S₄`, the question
`Λ₄ = S₄` and its equivalent form `z(4) = 1/4`. For the proofs we also use unscaled arc
weights `b i j ∈ [0, 1]` with Laplacian `lap b = D - B`; then `4 • L` is such a Laplacian.
-/

namespace AgenticConjectures.LaplacianPolygonOrderFour

open Complex Matrix

/-- A standardized Laplacian of order 4: a real `4 × 4` matrix with zero row sums whose
off-diagonal entries lie in `[-1/4, 0]`. -/
def IsStdLaplacian (L : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  (∀ i, ∑ j, L i j = 0) ∧ ∀ i j, i ≠ j → -(1 / 4 : ℝ) ≤ L i j ∧ L i j ≤ 0

/-- `z` is an eigenvalue of the real matrix `A`, viewed as a matrix over `ℂ`. -/
def IsEig (A : Matrix (Fin 4) (Fin 4) ℝ) (z : ℂ) : Prop :=
  Module.End.HasEigenvalue (toLin' (A.map ((↑) : ℝ → ℂ))) z

/-- `Λ₄`: all eigenvalues of all standardized Laplacians of order 4. -/
def Λ₄ : Set ℂ := {z | ∃ L, IsStdLaplacian L ∧ IsEig L z}

/-- `S₄`: the convex hull of the six points `0, (1 ± i)/4, (3 ± i)/4, 1`. -/
def S₄ : Set ℂ :=
  convexHull ℝ {0, (1 + I) / 4, (1 - I) / 4, (3 + I) / 4, (3 - I) / 4, 1}

/-- Question 1 of arXiv:2610.14100v2: is `Λ₄ = S₄`? -/
def statement : Prop := Λ₄ = S₄

/-- The equivalent form: the largest `|Im z|` over `z ∈ Λ₄` exists and equals `1/4`. -/
def z4_statement : Prop := IsGreatest {x : ℝ | ∃ z ∈ Λ₄, x = |z.im|} (1 / 4)

/-! ### Unscaled arc weights -/

/-- Laplacian `D - B` of the weighted digraph with arc weights `b i j`. The diagonal of `b`
cancels, so only the twelve off-diagonal weights matter. -/
def lap (b : Fin 4 → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (fun i => ∑ k, b i k) - Matrix.of b

/-- All twelve arc weights lie in `[0, 1]`. -/
def InBox (b : Fin 4 → Fin 4 → ℝ) : Prop := ∀ i j, i ≠ j → 0 ≤ b i j ∧ b i j ≤ 1

/-- The arcs whose weight lies strictly between `0` and `1`. -/
noncomputable def fracArcs (b : Fin 4 → Fin 4 → ℝ) : Finset (Fin 4 × Fin 4) :=
  Finset.univ.filter fun e => e.1 ≠ e.2 ∧ 0 < b e.1 e.2 ∧ b e.1 e.2 < 1

/-- At most four fractional weights, and at most two of them in each row. -/
def Sparse (b : Fin 4 → Fin 4 → ℝ) : Prop :=
  (fracArcs b).card ≤ 4 ∧ ∀ i, ((fracArcs b).filter fun e => e.1 = i).card ≤ 2

/-! ### Characteristic polynomial coefficients and the polynomial `Φ` -/

/-- Sum of the principal `2 × 2` minors. -/
def c2 (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0 + (A 0 0 * A 2 2 - A 0 2 * A 2 0) +
    (A 0 0 * A 3 3 - A 0 3 * A 3 0) + (A 1 1 * A 2 2 - A 1 2 * A 2 1) +
    (A 1 1 * A 3 3 - A 1 3 * A 3 1) + (A 2 2 * A 3 3 - A 2 3 * A 3 2)

/-- Determinant of a `3 × 3` matrix given by its entries (row by row). -/
def det3 (a b c d e f g h i : ℝ) : ℝ :=
  a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

/-- Sum of the principal `3 × 3` minors. -/
def c3 (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  det3 (A 1 1) (A 1 2) (A 1 3) (A 2 1) (A 2 2) (A 2 3) (A 3 1) (A 3 2) (A 3 3) +
    det3 (A 0 0) (A 0 2) (A 0 3) (A 2 0) (A 2 2) (A 2 3) (A 3 0) (A 3 2) (A 3 3) +
    det3 (A 0 0) (A 0 1) (A 0 3) (A 1 0) (A 1 1) (A 1 3) (A 3 0) (A 3 1) (A 3 3) +
    det3 (A 0 0) (A 0 1) (A 0 2) (A 1 0) (A 1 1) (A 1 2) (A 2 0) (A 2 1) (A 2 2)

/-- `σ₁, σ₂, σ₃`: the coefficients of `det (x - lap b) = x (x³ - σ₁ x² + σ₂ x - σ₃)`. -/
def σ₁ (b : Fin 4 → Fin 4 → ℝ) : ℝ := (lap b).trace

/-- See `σ₁`. -/
def σ₂ (b : Fin 4 → Fin 4 → ℝ) : ℝ := c2 (lap b)

/-- See `σ₁`. -/
def σ₃ (b : Fin 4 → Fin 4 → ℝ) : ℝ := c3 (lap b)

/-- `Disc + 4 (s₁² - 3 s₂ + 4)²` for the cubic `x³ - s₁ x² + s₂ x - s₃`. It equals
`∏_{a<b} ((r_a - r_b)² + 4)` over the roots. -/
def phiPoly (s₁ s₂ s₃ : ℝ) : ℝ :=
  s₁ ^ 2 * s₂ ^ 2 - 4 * s₂ ^ 3 - 4 * s₁ ^ 3 * s₃ + 18 * s₁ * s₂ * s₃ - 27 * s₃ ^ 2 +
    4 * (s₁ ^ 2 - 3 * s₂ + 4) ^ 2

/-- The polynomial `Φ` in the twelve weights. -/
def Φ (b : Fin 4 → Fin 4 → ℝ) : ℝ := phiPoly (σ₁ b) (σ₂ b) (σ₃ b)

/-- The finite-dimensional inequality that the reduction leaves: `Φ ≥ 0` whenever at most
four weights are fractional, at most two in each row. -/
def FaceBound : Prop := ∀ b, InBox b → Sparse b → 0 ≤ Φ b

/-- `e₁ e₂ - e₃`, where `e₁, e₂, e₃` are the elementary symmetric functions of the squared
roots of `x³ - s₁ x² + s₂ x - s₃`: `e₁ = s₁² - 2 s₂`, `e₂ = s₂² - 2 s₁ s₃`, `e₃ = s₃²`. -/
def sectorPoly (s₁ s₂ s₃ : ℝ) : ℝ :=
  (s₁ ^ 2 - 2 * s₂) * (s₂ ^ 2 - 2 * s₁ * s₃) - s₃ ^ 2

/-- The polynomial `Ψ` in the twelve weights, used for the sector bound `|Im z| ≤ Re z`. -/
def Ψ (b : Fin 4 → Fin 4 → ℝ) : ℝ := sectorPoly (σ₁ b) (σ₂ b) (σ₃ b)

/-- The finite-dimensional inequality for the sector half: `Ψ ≥ 0` on the same sparse
weights. -/
def SectorFaceBound : Prop := ∀ b, InBox b → Sparse b → 0 ≤ Ψ b

end AgenticConjectures.LaplacianPolygonOrderFour
