**English** | [한국어](DETAILS.ko.md)

# Order-four polygon question: details

This file gives the full argument behind [README.md](README.md): the Lean reduction of
Question 1 to two polynomial inequalities on finitely many faces, the exact certificate for
those inequalities, the face-orbit statistics, the numerical cross-check, and the relation to
other work. Lean names refer to the namespace `AgenticConjectures.LaplacianPolygonOrderFour`
(module [`AgenticConjectures/LaplacianPolygonOrderFour.lean`](../../AgenticConjectures/LaplacianPolygonOrderFour.lean)
and its folder).

## 1. Setup

A standardized Laplacian of order 4 is a real $4 \times 4$ matrix $\tilde L$ with zero row
sums and $-1/4 \le \tilde\ell_{ij} \le 0$ for $i \ne j$ (`IsStdLaplacian`). $\Lambda_4$ is the
set of complex eigenvalues of all such matrices (`Λ₄`, with `IsEig` and `isEig_iff_det`).

**Unscaled weights.** Put $b_{ij} = -4\tilde\ell_{ij} \in [0,1]$ for the twelve arcs $i \ne j$
and $L = \operatorname{lap} b = D - B$, where $D$ is the diagonal of out-degrees. Then
$L = 4\tilde L$, and `mem_Λ₄_iff` says that $z \in \Lambda_4$ iff $4z$ is an eigenvalue of
$\operatorname{lap} b$ for some $b \in [0,1]^{12}$ (`InBox`). With the half-plane form of
$S_4$ (`S4_eq`, Section 2), Question 1 says: for every $b \in [0,1]^{12}$ and every eigenvalue
$w$ of $L$,

$$
|\operatorname{Im} w| \le 1, \qquad |\operatorname{Im} w| \le \operatorname{Re} w, \qquad
|\operatorname{Im} w| \le 4 - \operatorname{Re} w .
$$

The first bound alone is $z(4) = 1/4$ (`z4_statement`).

## 2. The hexagon and $S_4 \subseteq \Lambda_4$

- `S4_eq`: the convex hull of $0, (1 \pm i)/4, (3 \pm i)/4, 1$ is
  $\{|\operatorname{Im} z| \le \operatorname{Re} z,\ |\operatorname{Im} z| \le 1 - \operatorname{Re} z,\ |\operatorname{Im} z| \le 1/4\}$.
  The hull lies in this convex set because the six vertices do. Conversely, `zono_coords`
  writes a point of the hexagon as
  $s_1 \tfrac{1+i}{4} + s_2 \tfrac12 + s_3 \tfrac{1-i}{4}$ with $s_k \in [0,1]$, and a
  multilinear interpolation between the vertices shows that this point is in the hull.
- `S4_subset_Λ4`: the circulant with first row
  $\bigl(\tfrac{s_1+s_2+s_3}{4}, -\tfrac{s_1}{4}, -\tfrac{s_2}{4}, -\tfrac{s_3}{4}\bigr)$ is a
  standardized Laplacian, and $(1, -i, -1, i)$ is an eigenvector with eigenvalue
  $s_1 \tfrac{1+i}{4} + s_2 \tfrac12 + s_3 \tfrac{1-i}{4}$. This is the order-4 case of
  Agaev and Chebotarev's Theorem 6 (every point of $S_n$ is an eigenvalue of a circulant).
- Two explicit examples, proved in Lean: `cycle_eig` ($(1+i)/4$, directed 4-cycle) and `h4_eig`
  ($(3+2i)/8$, the 4-cycle with chords $0 \to 2$ and $1 \to 3$ of half weight). The second
  lies on the top edge $\operatorname{Im} z = 1/4$.

## 3. The characteristic polynomial and the $\Phi$ criterion

**Cubic factor.** `det_sub_lap` proves
$\det(x - L) = x(x^3 - \sigma_1 x^2 + \sigma_2 x - \sigma_3)$, where $\sigma_k$ is the sum of
the principal $k \times k$ minors of $L$ (`σ₁`, `σ₂ = c2 (lap b)`, `σ₃ = c3 (lap b)`). So
every nonzero eigenvalue is a root $r_a$ of the cubic (`cubic_root_of_isEig`), and every root
of the cubic is an eigenvalue (`isEig_of_cubic_root`).

**The polynomial.**

$$
\Phi = \underbrace{\sigma_1^2\sigma_2^2 - 4\sigma_2^3 - 4\sigma_1^3\sigma_3 + 18\sigma_1\sigma_2\sigma_3 - 27\sigma_3^2}_{\operatorname{Disc}}
  + 4(\sigma_1^2 - 3\sigma_2 + 4)^2 = \prod_{a<b}\bigl((r_a - r_b)^2 + 4\bigr).
$$

It is a polynomial of degree 6 in the twelve weights.

**Non-real roots** (`phiPoly_eq`). If the roots are $c$ and $\alpha \pm i\beta$ with
$\beta \ne 0$, then $c = \sigma_1 - 2\alpha$, and with $u = c - \alpha$,

$$
\Phi = 4(1 - \beta^2)\,\bigl|(u - i\beta)^2 + 4\bigr|^2
     = 4(1 - \beta^2)\bigl((u^2 - \beta^2 + 4)^2 + 4u^2\beta^2\bigr).
$$

The last factor vanishes only when $u = 0$ and $\beta^2 = 4$. This is the degenerate case that
the scouting run flagged: there $\Phi = 0$ although $|\beta| = 2 > 1$.

**Bendixson's bound** (`im_le_three_halves`). For weights in $[0,1]$, every eigenvalue has
$|\operatorname{Im} w| \le 3/2$. If $p + iq$ is an eigenvector for $\alpha + i\beta$, then
$\beta \sum_i (p_i^2 + q_i^2) = \sum_{i<j} (L_{ij} - L_{ji})(p_i q_j - q_i p_j)$,
$|L_{ij} - L_{ji}| \le 1$, and $|p_i q_j - q_i p_j| \le (p_i^2 + q_i^2 + p_j^2 + q_j^2)/2$;
each index occurs in three pairs. So $\beta^2 \le 9/4 < 4$ and the degenerate case cannot
occur (`bracket_pos`, `Φ_eq_of_isEig`).

**Criterion.** For $b \in [0,1]^{12}$:
- `phi_criterion`: $\Phi(b) \ge 0$ implies $|\operatorname{Im} w| \le 1$ for every
  eigenvalue $w$;
- `phi_neg_of_im`: an eigenvalue with $|\operatorname{Im} w| > 1$ forces $\Phi(b) < 0$;
- `phi_nonneg_of_im_le` (converse): if every eigenvalue has $|\operatorname{Im} w| \le 1$,
  then $\Phi(b) \ge 0$. If the cubic has a real root $r$, it equals $(x - r)(x^2 - px + q)$,
  and `phiPoly_factor` gives
  $\Phi = \bigl((r^2 - pr + q)^2 + 8(r - p/2)^2 + 2(p^2 - 4q) + 16\bigr)(p^2 - 4q + 4)$.
  The second factor is $\ge 0$ because the roots of $x^2 - px + q$ have
  $|\operatorname{Im}| \le 1$. The first factor is then $\ge 0$ as well:
  if $p^2 - 4q \ge 0$ it is a sum of nonnegative terms, and otherwise
  $2(p^2 - 4q) + 16 \ge 8$, because $p^2 - 4q \ge -4$.

## 4. The sector bound and the $\Psi$ criterion

**Gershgorin** (`re_pos_of_isEig`). For nonnegative weights every eigenvalue $w \ne 0$ has
$\operatorname{Re} w > 0$, since it lies in a disc with center $d$ and radius $d$.

**The polynomial.** Let $e_1, e_2, e_3$ be the elementary symmetric functions of the squared
roots $r_a^2$: $e_1 = \sigma_1^2 - 2\sigma_2$, $e_2 = \sigma_2^2 - 2\sigma_1\sigma_3$,
$e_3 = \sigma_3^2$. Put $\Psi = e_1 e_2 - e_3$ (`sectorPoly`, `Ψ`).

**Non-real roots** (`sectorPoly_eq`). With roots $c$ and $\alpha \pm i\beta$, $\beta \ne 0$,

$$
\Psi = 2(\alpha^2 - \beta^2)\bigl((c^2 + \alpha^2 - \beta^2)^2 + 4\alpha^2\beta^2\bigr).
$$

By Gershgorin $\alpha > 0$, so the last factor is positive and $\Psi \ge 0$ iff
$|\beta| \le \alpha$.

**Criterion.**
- `sector_criterion`: for $b \in [0,1]^{12}$, $\Psi(b) \ge 0$ implies
  $|\operatorname{Im} w| \le \operatorname{Re} w$ for every eigenvalue $w$.
- `psi_nonneg_of_sector` (converse): if every eigenvalue satisfies
  $|\operatorname{Im} w| \le \operatorname{Re} w$, then $\Psi \ge 0$. In the real-root case
  `sectorPoly_factor` gives $\Psi = (p^2 - 2q)(r^4 + r^2(p^2 - 2q) + q^2)$, and
  $p^2 - 2q = u^2 + v^2$ is the sum of the squared roots of $x^2 - px + q$. That sum is
  $\ge 0$ when the roots are real, and also when they are $\alpha' \pm i\beta'$ with
  $|\beta'| \le \alpha'$, since then it equals $2(\alpha'^2 - \beta'^2)$.

**Complement** (`isEig_compl`, `inBox_compl`). The map $b \mapsto 1 - b$ keeps the box, and
$\operatorname{lap}(1 - b) = 4I - J - \operatorname{lap} b$ with $J$ the all-ones matrix
(`lap_compl_apply`). A left eigenvector $y$ of $\operatorname{lap} b$ for $w \ne 0$ has
$\sum_i y_i = 0$, so $yJ = 0$ and $y \operatorname{lap}(1 - b) = (4 - w)y$. Applied to
$1 - b$, the sector bound at 0 gives the bound $|\operatorname{Im} w| \le 4 - \operatorname{Re} w$.
The complement also fixes $\Phi$: it maps the nonzero roots by $r \mapsto 4 - r$, so the
differences $r_a - r_b$ only change sign.

**Remark.** For $n = 4$ the two sector bounds also follow from Agaev and Chebotarev's
Theorem 5, whose region includes the angle at 0 bounded by the rays through
$e^{\pm(\pi/2 - \pi/n)i}$ and the matching angle at 1. Chebotarev's paper and Liu's preprint
use that theorem. We do not use it. Instead we certify $\Psi \ge 0$ (Section 7), so that the
Lean equivalence covers the whole statement $\Lambda_4 = S_4$ without a cited theorem.

## 5. Reduction to sparse weights

`exists_sparse` fixes a real-linear functional $\varphi : \mathbb C \to \mathbb R$. For
$b \in [0,1]^{12}$ and an eigenvalue $w$ of $\operatorname{lap} b$, it finds $b'$ in the box
with at most four fractional weights (strictly between 0 and 1), at most two in each row
(`Sparse`), and an eigenvalue $w'$ of $\operatorname{lap} b'$ with
$\varphi(w) \le \varphi(w')$. It changes only weights that are fractional in $b$. The proof
is an induction on the number of fractional arcs. Each step moves $b$ along a direction
$\delta$ supported on the fractional arcs until one more weight reaches 0 or 1
(`exists_move`):

- **Left move** (`left_move`, used when at least five weights are fractional and $w \ne 0$).
  Take a left eigenvector $y$. Since $y \operatorname{lap} b = w y$ and the rows of
  $\operatorname{lap} b$ sum to 0, we get $w \sum_i y_i = 0$, so $\sum_i y_i = 0$. Consider
  the real-linear map $(\delta, \mu) \mapsto y \operatorname{lap}\delta - \mu y$, restricted to
  the first three coordinates. Its domain has dimension $\#\text{fractional} + 2 \ge 7$ and its
  target has dimension 6, so it has a nonzero kernel element. The fourth coordinate vanishes
  too, because both $y \operatorname{lap}\delta$ and $\mu y$ have coordinate sum 0. Hence
  $y \operatorname{lap}(b + s\delta) = (w + s\mu) y$ for all $s$. The sign of $(\delta, \mu)$
  is chosen so that $\varphi(\mu) \ge 0$.
- **Right move** (`right_move`, used when a row has three fractional weights). Take a right
  eigenvector $v$. The complex equation $\sum_j \delta_{ij}(v_i - v_j) = 0$ is two real
  equations on the three off-diagonal entries of row $i$, so it has a nonzero solution
  $\delta$ supported on row $i$, and $w$ stays an eigenvalue of
  $\operatorname{lap}(b + s\delta)$.
- **$w = 0$.** Every fractional weight is set to 0; $0$ is an eigenvalue of every
  $\operatorname{lap} b$ (`isEig_lap_zero`).

Other reductions of the same kind:
- Chebotarev's Proposition `p:sparse` (arXiv:2610.14100v2) keeps the eigenvector and the
  eigenvalue fixed and takes a vertex of a polytope in each row. That gives at most two
  fractional entries per row, but up to eight in total.
- Liu's Lemma 16 maximizes $\operatorname{Im} \lambda'$ over the polytope of pairs
  $(b', \lambda')$ with $L'v = \lambda' v$ for a fixed right eigenvector $v$. Its eight real
  equations leave at most six fractional weights, at most two per row.
- With a left eigenvector, $\sum_i y_i = 0$ makes one of the four complex equations redundant.
  That is why four fractional weights remain here instead of six.

## 6. Assembly: the two equivalences

- `im_le_one_of_faceBound`: apply `exists_sparse` with $\varphi = \operatorname{Im}$, then
  `phi_criterion` at the sparse point; conjugation handles $-\operatorname{Im}$.
- `sector_of_sectorFaceBound`: apply `exists_sparse` with
  $\varphi = \operatorname{Im} - \operatorname{Re}$, then `sector_criterion`.
- `sector_four_of_sectorFaceBound`: the complement turns this into
  $|\operatorname{Im} w| \le 4 - \operatorname{Re} w$.
- `z4_statement_of_faceBound` and `statement_of_faceBounds` rescale by 4 and use
  `cycle_eig` and `S4_subset_Λ4`.
- The converses (`phi_nonneg_of_im_le`, `psi_nonneg_of_sector`) give the other directions:

```lean
theorem z4_statement_iff_faceBound : z4_statement ↔ FaceBound
theorem statement_iff_faceBounds : statement ↔ FaceBound ∧ SectorFaceBound
```

Here `FaceBound` says $\Phi(b) \ge 0$ and `SectorFaceBound` says $\Psi(b) \ge 0$, both for every
$b$ in the box with at most four fractional weights, at most two per row.

## 7. The exact certificate

[`face_certificate.py`](face_certificate.py) verifies `FaceBound` and `SectorFaceBound` with
Python integers and `fractions.Fraction` only (no floating point, no external packages).

1. **Faces.** Every sparse $b$ lies on the face of a *maximal pattern*: four free arcs, at most
   two per row, carrying $t_0, \dots, t_3 \in [0,1]$ in the order of the arcs, and the other
   eight arcs fixed at 0 or 1. The fractional arcs of $b$ can always be completed to four
   such arcs, and every non-fractional weight is 0 or 1. There are $459$ choices of free
   arcs and $2^8$ fillings, so $117504$ patterns.
2. **Symmetry.** Relabelling the vertices is a permutation similarity, so it fixes
   $\sigma_1, \sigma_2, \sigma_3$. The script checks this as a polynomial identity in the
   twelve weights for the generators $(0\,1)$ and $(0\,1\,2\,3)$ of $S_4$. It also checks the
   complement formulas $\sigma_1' = 12 - \sigma_1$,
   $\sigma_2' = 48 - 8\sigma_1 + \sigma_2$,
   $\sigma_3' = 64 - 16\sigma_1 + 4\sigma_2 - \sigma_3$, and that $\Phi$ is invariant under
   this map. A symmetry permutes the free variables and replaces some $t_k$ by $1 - t_k$, so
   nonnegativity on $[0,1]^4$ is the same for all faces of an orbit. $\Phi$ needs one face per
   orbit of $S_4 \times \{\mathrm{id}, \text{complement}\}$ (2533 orbits), and $\Psi$ one face
   per orbit of $S_4$ (5021 orbits; $\Psi$ is not complement-invariant).
3. **Box certificate.** Write the face polynomial $P(t)$ in the tensor Bernstein basis of
   $[0,1]^4$, with degree $d_k$ in $t_k$ equal to the largest exponent of $t_k$. The script
   computes $\sum_{j \le k} a_j \binom{d-j}{k-j}$ along each axis; these are the Bernstein
   coefficients times positive binomials. If all are $\ge 0$, then $P \ge 0$ on the box.
4. **Simplex certificate.** Otherwise the box is cut into the 24 Kuhn simplices through one
   corner $c$, the corners where $P$ vanishes tried first. On a simplex with vertices
   $V_0, \dots, V_4$, the script expands
   $P\bigl(\sum_j \theta_j V_j\bigr)\bigl(\sum_j \theta_j\bigr)^{d - \deg}$, a form of degree
   $d = \deg P$ in $\theta$. If all its coefficients are $\ge 0$, then $P \ge 0$ on the
   simplex. A failing simplex is split into two simplices that cover it, at a point $M$ on one
   edge; at most 6 splits are allowed below each Kuhn simplex. The point $M$ is chosen as
   follows:
   - Suppose some vertex $W$ has $P(W) = 0$, and two edge directions $d_k, d_l$ from $W$ have
     zero derivative of $P$, with Hessian form $q$ such that $q_{kk}, q_{ll} > 0 > q_{kl}$.
     Then the edge between those two neighbours is split at the ratio
     $q_{kk}/(q_{kk} - q_{kl})$. When $q$ has rank one there, this point lies on the zero
     set of the quadratic form.
   - Otherwise the longest edge is bisected.

   The rule only steers the search: every split replaces a simplex by two that cover it.
5. **Cross-check with Lean's formulas.** For each representative, the expanded face
   polynomials are compared at two random rational points with a direct evaluation of the
   formulas of `Basic.lean` (`σ₁`, `c2`, `c3`, `det3`, `phiPoly`, `sectorPoly`). The search is
   deterministic. The per-orbit table (method and number of simplices) is compared with the
   committed [`face_orbits.tsv`](face_orbits.tsv).

**Statistics**, from [`orbit_table.py`](orbit_table.py), which reads `face_orbits.tsv`:

| | orbits | box | needed simplices | simplices |
|---|---|---|---|---|
| $\Phi$ | 2533 | 2457 | 76 | 1889 |
| $\Psi$ | 5021 | 4956 | 65 | 1560 |

The run takes about 17 s with the default 4 worker processes on an Apple M5 Max. The CPU
time is 36.5 s for the $\Phi$ orbits and 27.6 s for the $\Psi$ orbits; the slowest orbit
(`00110FFF00F1` for $\Phi$) takes 1.8 s. Every orbit is certified. For an orbit closed by
simplices, the table records the corner of the Kuhn simplices and the number of final
simplices.

Patterns are written as twelve characters in arc order
$01, 02, 03, 10, 12, 13, 20, 21, 23, 30, 31, 32$ (`F` = free).

**Why simplices are needed.** If $P \ge 0$ has a zero in the open box, then not all of its
box Bernstein coefficients can be $\ge 0$, unless $P \equiv 0$, because every basis
polynomial is positive there. $\Phi$ has such zeros. An example is the orbit of
`01F1F00F1F10`, the face of Liu's family: weight 1 on the arcs $i \to i+1$ of a directed
4-cycle (here $0 \to 2 \to 3 \to 1 \to 0$), free chords $i \to i+2$, and weight 0 on
$i \to i+3$. In the arc order of the representative, $\Phi$ on this face is
$(t_0 - t_1 - t_2 + t_3)^2$ times a second factor, so it vanishes on the hyperplane
$t_0 + t_3 = t_1 + t_2$. That hyperplane is Liu's three-parameter family on which
$|\operatorname{Im} w| = 1$ is attained (written $t_0 + t_2 = t_1 + t_3$ in Liu's indexing,
where $t_i$ sits on the chord leaving the $i$-th vertex of the cycle). The certificate
closes this orbit with 32 simplices from the corner 0000.

**The eight-dimensional faces.** The faces with one fixed arc per row and two free arcs per
row number $6^4 = 1296$ and form 36 orbits under relabelling and complement. This is the
scouting run's count, recomputed here. Each maximal pattern lies on such a face. For one
representative of each orbit, `orbit_table.py` lists how many $\Phi$-orbits of maximal
patterns lie on it, and how many of those needed simplices:

| representative | faces | $\Phi$-orbits on it | needed simplices | simplices |
|---|---|---|---|---|
| `0FF 0FF 0FF 0FF` | 24 | 432 | 0 | 0 |
| `0FF 0FF 0FF 1FF` | 48 | 912 | 0 | 0 |
| `0FF 0FF 0FF F0F` | 24 | 521 | 0 | 0 |
| `0FF 0FF 0FF F1F` | 48 | 962 | 0 | 0 |
| `0FF 0FF 0FF FF0` | 48 | 804 | 0 | 0 |
| `0FF 0FF 0FF FF1` | 48 | 830 | 0 | 0 |
| `0FF 0FF 1FF 1FF` | 24 | 549 | 0 | 0 |
| `0FF 0FF 1FF F1F` | 24 | 519 | 0 | 0 |
| `0FF 0FF 1FF FF0` | 48 | 802 | 0 | 0 |
| `0FF 0FF 1FF FF1` | 48 | 827 | 0 | 0 |
| `0FF 0FF FF0 FF0` | 6 | 156 | 0 | 0 |
| `0FF 0FF FF0 FF1` | 24 | 570 | 0 | 0 |
| `0FF 0FF FF1 FF1` | 6 | 156 | 0 | 0 |
| `0FF 1FF 0FF 0FF` | 24 | 548 | 48 | 1198 |
| `0FF 1FF 0FF 1FF` | 48 | 910 | 56 | 1380 |
| `0FF 1FF 0FF F0F` | 48 | 959 | 45 | 1099 |
| `0FF 1FF 0FF F1F` | 24 | 516 | 51 | 1284 |
| `0FF 1FF 0FF FF0` | 48 | 918 | 64 | 1599 |
| `0FF 1FF 0FF FF1` | 48 | 957 | 50 | 1246 |
| `0FF 1FF 1FF 1FF` | 24 | 431 | 0 | 0 |
| `0FF 1FF 1FF F0F` | 24 | 519 | 15 | 360 |
| `0FF 1FF 1FF FF0` | 48 | 921 | 15 | 360 |
| `0FF 1FF 1FF FF1` | 48 | 960 | 58 | 1425 |
| `0FF 1FF FF0 FF1` | 12 | 297 | 33 | 842 |
| `0FF F0F 0FF 0FF` | 48 | 706 | 52 | 1296 |
| `0FF F0F 0FF 1FF` | 48 | 813 | 51 | 1273 |
| `0FF F0F 1FF 0FF` | 48 | 1000 | 39 | 961 |
| `0FF F0F 1FF 1FF` | 48 | 881 | 0 | 0 |
| `0FF F0F 1FF F0F` | 48 | 928 | 24 | 576 |
| `0FF F0F 1FF F1F` | 48 | 947 | 15 | 360 |
| `0FF F0F 1FF FF0` | 48 | 888 | 0 | 0 |
| `0FF F0F 1FF FF1` | 48 | 992 | 51 | 1256 |
| `0FF F0F FF0 0FF` | 12 | 284 | 33 | 839 |
| `0FF F0F FF0 1FF` | 48 | 1044 | 25 | 607 |
| `0FF F0F FF1 1FF` | 24 | 554 | 15 | 360 |
| `0FF F1F FF0 1FF` | 12 | 284 | 0 | 0 |

The three-character groups are the rows $0, 1, 2, 3$. The counts in the third column overlap
between rows, because one maximal pattern lies on several eight-dimensional faces. In the
scouting run, z3 (NLSAT) closed only small subfaces, with up to four free weights, and
returned `unknown` on the larger faces it tried. Here every face is reduced to
four-dimensional subfaces, and each subface closes in under 2 s.

## 8. Independent numerical check

[`numerical_check.py`](numerical_check.py) shares no code with the certificate. It computes
characteristic polynomials by the Faddeev–LeVerrier recursion and eigenvalues by
Durand–Kerner iteration, in double precision. With its defaults (seed 2026) it reports:

- On 2000 random weight vectors (partly fractional, partly 0/1), the identity
  $\Phi = \prod_{a<b}((r_a - r_b)^2 + 4)$ holds up to relative error about $5 \cdot 10^{-13}$,
  and $\Psi = e_1 e_2 - e_3$ up to about $4 \cdot 10^{-13}$ (the printed digits depend on the
  Python version).
- 30 multi-start local ascents per objective, started at random points, random 0/1 points and
  near relabelled 4-cycles, give:
  - $\max \operatorname{Im} w = 1.000000000$ (the bound is 1; it is attained on the 4-cycle);
  - $\max(|\operatorname{Im} w| - \operatorname{Re} w) = 0.000000000$;
  - $\max(|\operatorname{Im} w| - (4 - \operatorname{Re} w)) = 0.000000000$.

This is evidence only; the proof is Sections 3–7. It runs in about 2 s.

## 9. What is machine-checked

| Step | Checked by |
|---|---|
| Definitions, $S_4$ as a hexagon, $S_4 \subseteq \Lambda_4$, the two examples | Lean |
| Characteristic polynomial, Bendixson, Gershgorin, complement | Lean |
| $\Phi$ and $\Psi$ criteria and their converses | Lean |
| Reduction to sparse weights (`exists_sparse`) | Lean |
| `statement ↔ FaceBound ∧ SectorFaceBound`, `z4_statement ↔ FaceBound` | Lean |
| `FaceBound`, `SectorFaceBound` | `face_certificate.py`, exact arithmetic, outside Lean |
| Numerical agreement | `numerical_check.py`, floating point |

Lean uses only `propext`, `Classical.choice` and `Quot.sound`. The trusted base for the last
step is the Python interpreter and the certificate script (about 500 lines). Its link to the
Lean definitions is:
- the same formulas;
- the random rational cross-checks against the formulas of `Basic.lean`;
- the symmetry identities, checked as polynomial identities.

**Why the certificate is not in Lean.** `native_decide` and `ofReduceBool` are banned here, so
a Lean check would have to run in the kernel (`decide +kernel`). A local test took about two
minutes for an integer loop of 200,000 steps plus a 200,000-term list dot product. The
certificate expands polynomials with up to $5^4 = 625$ coefficients (each face polynomial has
degree at most 4 in each variable) on 7554 orbit representatives and 3449 final simplices.
Re-running it in the kernel is far beyond a CI budget, and so is a `ring`/`nlinarith` proof
per orbit. The status is therefore `partial`.

## 10. Prior work, overlap and credit

- **Agaev and Chebotarev** (Linear Algebra Appl. 399 (2005) 157–168,
  [arXiv:math/0508176](https://arxiv.org/abs/math/0508176)) posed the polygon conjecture,
  proved $S_n \subseteq \Lambda_n$ (Theorem 6), proved $\Lambda_n = S_n$ for $n \le 3$, and
  gave the region of Theorem 5 (disks, angles and the Pick band).
- **Chebotarev** ([arXiv:2610.14100v2](https://arxiv.org/abs/2610.14100v2), 2026-10-20)
  disproved the conjecture for every $n \ge 5$ and asked Question 1 for $n = 4$, with the
  reduction `p:sparse` and the equivalence with $z(4) = 1/4$. For $n = 4$ its evidence is all
  $2^{12}$ unweighted digraphs and local maximizations started near several structured
  matrices and at random. Its Question `q:top` asks whether
  $\max \operatorname{Im} \Lambda_n = \frac1n \cot\frac\pi n$ for even $n$; that is not
  treated here.

### Relation to Liu's preprint

Dylan Z. Liu, "The Agaev–Chebotarev Polygon Conjecture Holds Exactly for n ≤ 4"
([Zenodo record 23630989](https://zenodo.org/records/23630989),
[doi:10.5281/zenodo.23630989](https://doi.org/10.5281/zenodo.23630989), created 2026-10-25,
CC BY 4.0) reports a computer-assisted proof of $\Lambda_4 = S_4$ (its Theorem 6), and also
that $\Lambda_n \ne S_n$ for every $n \ge 5$. It is not refereed and not formalized. We found
it in the literature check at the start of this work. Comparison:

| | Liu's preprint | this entry |
|---|---|---|
| Inequality | the same $\Phi$ (Lemma 15, in depressed-cubic form) | $\Phi$ |
| Degenerate zero | Bendixson with $\sqrt{3/2}$ | Bendixson with $3/2$ |
| Reduction | right eigenvector, at most 6 fractional, at most 2 per row (Lemma 16) | left eigenvector, at most 4 fractional, at most 2 per row |
| Faces | 445312 patterns in 9583 orbits | 117504 maximal patterns in 2533 orbits |
| Sector half | cites Agaev–Chebotarev Theorem 5 | certifies $\Psi \ge 0$ on 5021 orbits |
| Certificate | Bernstein on boxes and Kuhn simplices with hyperplane cuts, python-flint, about one hour | Bernstein on boxes and Kuhn simplices with edge splits, standard library, about one CPU minute |
| Formalization | none | Lean equivalence of Question 1 with the two face bounds |

Liu's preprint says that its verification script and data file are ancillary files. We did not
find them on the Zenodo record, which lists only the PDF, and we have not run them. Both
certificates use the same kind of method (Bernstein expansions on boxes and on Kuhn
simplices). No code was taken from the preprint.

### Other related work

- **AFTD.** The automated platform "Auto-Formalizing Theoretical Domains"
  ([github.com/rainwangphy/aftd-platform](https://github.com/rainwangphy/aftd-platform)) lists
  the question as OP-465, stated in Lean as
  `op_465_standardized_laplacian_order_four_polygon_conjecture`. Its open stubs are
  `standardized_laplacian_order_four_im_le`,
  `standardized_laplacian_order_four_two_fractional_im_le` and
  `standardized_laplacian_order_four_two_fractional_sector`. It proves, among others:
  - $S_n \subseteq \Lambda_n$;
  - a discriminant criterion (`real_cubic_im_le_of_discriminant_bound`);
  - one two-parameter family (`two_adjacent_chord_cubic_im_le`);
  - Gershgorin, $\operatorname{Re} \ge 0$ and $|\operatorname{Im}| \le 3/4$;
  - polygon membership from the sector and Im bounds;
  - a nonzero example with at most two fractional entries per row
    (`exists_nonzero_two_fractional_standardized_laplacian_four`); the reduction `p:sparse`
    itself is not proved there.

  We downloaded its knowledge base `web/data/kb.json` again on 2026-10-25 at 23:37 UTC. It was
  unchanged since its generation at 17:13 UTC, and OP-465 and the three stubs were still
  `stated`. We read AFTD only to learn what it states and proves. No code was taken from it;
  the repository has no licence file.
- **Scouting.** An earlier scouting run of this project found the reduction to the 1296
  eight-dimensional faces and their 36 orbits, the shifted-discriminant identity for $\Phi$
  with its degenerate case, the z3 checks, and the dead routes (vertex reduction, convex hull
  in $\sigma$-space).
- **Literature check** (2026-10-25): arXiv lists v2 as the latest version of 2610.14100;
  OpenAlex shows no citing works; MathDB posts #379199 and #318272 (the general conjecture) are
  open; Formal Conjectures and GitHub searches found nothing else on Question 1.

No novelty is claimed. No human has reviewed this work. Nothing has been reported to the
authors or submitted anywhere.
