**English** | [한국어](README.ko.md)

# Order-four polygon question for standardized Laplacians

The polygon conjecture $\Lambda_n = S_n$ is due to R. Agaev and P. Chebotarev
(*Linear Algebra Appl.* 399 (2005) 157–168,
[arXiv:math/0508176](https://arxiv.org/abs/math/0508176)). Question 1, which asks whether
$\Lambda_4 = S_4$, and the disproof of the conjecture for every $n \ge 5$, which leaves order 4
open, are due to P. Chebotarev,
[arXiv:2610.14100v2](https://arxiv.org/abs/2610.14100v2). A preprint by Dylan Z. Liu
([Zenodo, doi:10.5281/zenodo.23630989](https://doi.org/10.5281/zenodo.23630989)) reports a
computer-assisted proof that $\Lambda_4 = S_4$; see [Prior work](#prior-work-and-credit).

## The question

A *standardized Laplacian* of order $n$ is a real $n \times n$ matrix with zero row sums whose
off-diagonal entries lie in $[-1/n, 0]$. $\Lambda_n \subset \mathbb C$ is the set of all
eigenvalues of all such matrices. Agaev and Chebotarev defined a polygon $S_n \subseteq \Lambda_n$
and conjectured $\Lambda_n = S_n$. They proved it for $n \le 3$. Chebotarev's arXiv paper
disproves it for every $n \ge 5$ and leaves $n = 4$ open as Question 1. For $n = 4$,

$$
S_4 = \operatorname{conv}\Bigl\{0,\ \tfrac{1 \pm i}{4},\ \tfrac{3 \pm i}{4},\ 1\Bigr\}
    = \bigl\{z : |\operatorname{Im} z| \le \operatorname{Re} z,\ |\operatorname{Im} z| \le 1 - \operatorname{Re} z,\ |\operatorname{Im} z| \le \tfrac14\bigr\}.
$$

**Question 1.** Is $\Lambda_4 = S_4$? The paper notes that this is equivalent to
$z(4) = 1/4$, where $z(n) = \sup\{|\operatorname{Im}\lambda| : \lambda \in \Lambda_n\}$.

## Result

Status: **partial**. The final inequalities are certified by a computer, not in Lean.

1. **Lean** (no `sorry`, only the standard axioms): Question 1 is *equivalent* to two
   polynomial inequalities on finitely many faces of the weight cube, each of dimension at
   most 4. Its form $z(4) = 1/4$ is equivalent to the first inequality alone:
   - `statement_iff_faceBounds : statement ↔ FaceBound ∧ SectorFaceBound`
   - `z4_statement_iff_faceBound : z4_statement ↔ FaceBound`

   Here we write $L = D - B$ with arc weights $b_{ij} \in [0,1]$, so that $L/4$ is a
   standardized Laplacian. Then $\det(x - L) = x(x^3 - \sigma_1 x^2 + \sigma_2 x - \sigma_3)$, and
   - `FaceBound` says $\Phi \ge 0$, where
     $\Phi = \operatorname{Disc} + 4(\sigma_1^2 - 3\sigma_2 + 4)^2 = \prod_{a<b}\bigl((r_a - r_b)^2 + 4\bigr)$
     over the three roots of the cubic;
   - `SectorFaceBound` says $\Psi \ge 0$, where
     $\Psi = (\sigma_1^2 - 2\sigma_2)(\sigma_2^2 - 2\sigma_1\sigma_3) - \sigma_3^2$;
   - both are required only for weights with at most four entries strictly between 0 and 1,
     at most two in each row.
2. **Computer-assisted** (exact integer and rational arithmetic, outside Lean):
   [`face_certificate.py`](face_certificate.py) verifies `FaceBound` and `SectorFaceBound`.
   - It enumerates the 117504 maximal sparse patterns and checks the symmetry identities.
   - It checks one face per symmetry orbit: 2533 orbits for $\Phi$ and 5021 for $\Psi$.
   - Each check is a Bernstein expansion with nonnegative coefficients, on the whole box or
     on Kuhn simplices with edge splits.

Together, (1) and (2) give $\Lambda_4 = S_4$ and $z(4) = 1/4$ as a computer-assisted result.
Liu's preprint reports the same conclusion by a related method. In Lean, `FaceBound` and
`SectorFaceBound` appear only as hypotheses or as sides of an equivalence; Lean does not check
the certificate.

[DETAILS.md](DETAILS.md) has the full argument: the reduction, both criteria, the symmetry
step, the certificate, the face-orbit statistics and the numerical checks.

## Lean declarations

Module [`AgenticConjectures/LaplacianPolygonOrderFour.lean`](../../AgenticConjectures/LaplacianPolygonOrderFour.lean)
and its folder; namespace `AgenticConjectures.LaplacianPolygonOrderFour`.

| Declaration | Statement |
|---|---|
| `statement` | Question 1: `Λ₄ = S₄` |
| `z4_statement` | `IsGreatest {x \| ∃ z ∈ Λ₄, x = \|z.im\|} (1/4)`, the paper's form $z(4) = 1/4$ |
| `statement_iff_faceBounds` | `statement ↔ FaceBound ∧ SectorFaceBound` |
| `z4_statement_iff_faceBound` | `z4_statement ↔ FaceBound` |
| `statement_of_faceBounds`, `z4_statement_of_faceBound` | the two directions used for the result |
| `S4_eq` | the convex hull equals the half-plane description |
| `S4_subset_Λ4` | $S_4 \subseteq \Lambda_4$, by circulants |
| `cycle_eig`, `h4_eig` | $(1+i)/4 \in \Lambda_4$ (directed 4-cycle) and $(3+2i)/8 \in \Lambda_4$ (a 4-cycle with two chords, on the top edge) |
| `mem_Λ₄_iff` | $z \in \Lambda_4$ iff $4z$ is an eigenvalue of some $L = D - B$ with weights in $[0,1]$ |
| `exists_sparse` | the reduction to at most four fractional weights, at most two per row |
| `phi_criterion`, `phi_nonneg_of_im_le` | all eigenvalues have $\lvert\operatorname{Im}\rvert \le 1$ iff $\Phi \ge 0$ |
| `sector_criterion`, `psi_nonneg_of_sector` | all eigenvalues have $\lvert\operatorname{Im}\rvert \le \operatorname{Re}$ iff $\Psi \ge 0$ |
| `im_le_three_halves` | Bendixson's bound $\lvert\operatorname{Im}\rvert \le 3/2$ |

## Statement faithfulness

No upstream formal statement exists, so the definitions are ours.
- **Matrices.** A standardized Laplacian of order 4 (`IsStdLaplacian`) is a
  `Matrix (Fin 4) (Fin 4) ℝ` with zero row sums and $-1/4 \le \ell_{ij} \le 0$ for $i \ne j$.
- **Eigenvalues.** An eigenvalue (`IsEig`) is an eigenvalue of the complexified matrix,
  `Module.End.HasEigenvalue (Matrix.toLin' (L.map (↑))) z`. `isEig_iff_det` shows that this is
  the same as $\det(z - L) = 0$.
- **The polygon.** `S₄` is the convex hull of the six vertices, which is the paper's
  definition for $n = 4$. `S4_eq` proves the half-plane description.
- **The paper's equivalent form.** `z4_statement` asks that the largest $|\operatorname{Im} z|$
  over $\Lambda_4$ exist and equal $1/4$. Because $(1+i)/4 \in \Lambda_4$ (`cycle_eig`), this
  is the same as $z(4) = 1/4$ for the supremum $z(4)$.

## Reproduction

From the repository root:

```bash
lake build AgenticConjectures.LaplacianPolygonOrderFour
```

This compiles the nine modules in about 28 s wall time after Mathlib is built (Apple M5 Max;
the per-module build times add up to about 38 s).

```bash
cd problems/laplacian-polygon-order-four && python3 face_certificate.py
```

This is the exact certificate: about 17 s with the default 4 worker processes (about 64 s of
CPU time). It compares its per-orbit table with [`face_orbits.tsv`](face_orbits.tsv).

```bash
cd problems/laplacian-polygon-order-four && python3 numerical_check.py
```

This is an independent floating-point check and takes about 2 s. It shares no code with the
certificate. It checks the $\Phi$ and $\Psi$ identities on random weights and runs local
ascents of $\max \operatorname{Im}$ and of the two sector violations.

Both scripts use only the Python standard library.

## Prior work and credit

- **The conjecture.** Agaev and Chebotarev (2005) proved $S_n \subseteq \Lambda_n$, proved
  $\Lambda_n = S_n$ for $n \le 3$, and posed the conjecture.
- **Question 1.** Chebotarev ([arXiv:2610.14100v2](https://arxiv.org/abs/2610.14100v2),
  2026-10-20) disproved the conjecture for every $n \ge 5$ and asked Question 1 for $n = 4$. The
  paper also gives the reduction to at most two fractional entries per row and numerical
  evidence.
- **Liu's preprint.** Dylan Z. Liu, "The Agaev–Chebotarev Polygon Conjecture Holds Exactly for
  n ≤ 4" ([Zenodo record](https://zenodo.org/records/23630989), created 2026-10-25, CC BY 4.0;
  not refereed, not formalized). It reports a computer-assisted proof of $\Lambda_4 = S_4$:
  - an LP reduction to at most six fractional weights;
  - the same polynomial $\Phi$;
  - exact Bernstein expansions on 9583 classes of faces.

  It also proves $\Lambda_n \ne S_n$ for every $n \ge 5$. Its verification script is said to
  be an ancillary file; we did not find it on the Zenodo record and have not run it.
  [DETAILS.md](DETAILS.md#relation-to-lius-preprint) compares the two approaches.
- **AFTD (related work).** The automated platform AFTD
  ([github.com/rainwangphy/aftd-platform](https://github.com/rainwangphy/aftd-platform))
  states the question in Lean as OP-465 and proves partial lemmas (listed in DETAILS). No
  code was taken from it.
- **Scouting.** An earlier scouting run of this project found the face reduction, the z3
  checks and the dead routes that this work starts from.

No novelty is claimed. No human has reviewed this work. Nothing has been reported to the
authors or submitted anywhere.
