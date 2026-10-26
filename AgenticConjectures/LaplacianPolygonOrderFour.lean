import AgenticConjectures.LaplacianPolygonOrderFour.Basic
import AgenticConjectures.LaplacianPolygonOrderFour.Eigen
import AgenticConjectures.LaplacianPolygonOrderFour.Polygon
import AgenticConjectures.LaplacianPolygonOrderFour.Spectral
import AgenticConjectures.LaplacianPolygonOrderFour.Sector
import AgenticConjectures.LaplacianPolygonOrderFour.Reduction
import AgenticConjectures.LaplacianPolygonOrderFour.Converse
import AgenticConjectures.LaplacianPolygonOrderFour.Main

/-!
# The order-four polygon question

Source: P. Chebotarev, "Digraph Laplacian spectra: The 2005 polygon conjecture fails for all
orders above four", arXiv:2610.14100v2, Question 1. The polygon conjecture itself is due to
R. Agaev and P. Chebotarev (Linear Algebra Appl. 2005, arXiv:math/0508176).

## Statement and faithfulness

There is no upstream formal statement; the definitions in `Basic` are ours.

* `IsStdLaplacian L`: `L : Matrix (Fin 4) (Fin 4) ℝ` has zero row sums and off-diagonal
  entries in `[-1/4, 0]`. This is the paper's class of standardized Laplacians of order 4.
* `IsEig L z`: `z` is an eigenvalue of `L` viewed over `ℂ`, i.e.
  `Module.End.HasEigenvalue (Matrix.toLin' (L.map (↑))) z`. `isEig_iff_det` bridges this to
  `det (z - L) = 0`.
* `Λ₄`: all eigenvalues of all standardized Laplacians of order 4.
* `S₄`: the convex hull of `0, (1 ± i)/4, (3 ± i)/4, 1`, which is the paper's polygon for
  `n = 4`. `S4_eq` proves the half-plane description
  `|Im z| ≤ Re z`, `|Im z| ≤ 1 - Re z`, `|Im z| ≤ 1/4`.
* `statement`: Question 1, `Λ₄ = S₄`. `z4_statement`: the paper's equivalent form, that the
  largest `|Im z|` over `z ∈ Λ₄` exists and equals `1/4`.

The proofs use unscaled weights `b i j ∈ [0, 1]` and `lap b = D - B`; `mem_Λ₄_iff` says
`z ∈ Λ₄` iff `4 z` is an eigenvalue of some such `lap b`.

## What is proved

* `S4_subset_Λ4`: `S₄ ⊆ Λ₄`, by circulants. `cycle_eig`, `h4_eig`: two explicit eigenvalues.
* `exists_sparse`: in every real-linear direction, every eigenvalue is dominated by an
  eigenvalue of some `lap b'` with at most four fractional weights, at most two in each row.
* `phi_criterion`, `sector_criterion` and their converses `phi_nonneg_of_im_le`,
  `psi_nonneg_of_sector`: for weights in `[0, 1]`, all eigenvalues satisfy `|Im z| ≤ 1` iff
  `Φ b ≥ 0`, and all satisfy `|Im z| ≤ Re z` iff `Ψ b ≥ 0`.
* `z4_statement_iff_faceBound`, `statement_iff_faceBounds`: Question 1 is equivalent to the
  polynomial inequalities `FaceBound` and `SectorFaceBound` on the sparse weights, which form
  finitely many faces of the cube of dimension at most 4.

`FaceBound` and `SectorFaceBound` are not proved in Lean. The problem directory
`problems/laplacian-polygon-order-four/` checks them with an exact rational Bernstein
certificate in Python; that step is computer-assisted and outside Lean.
-/
