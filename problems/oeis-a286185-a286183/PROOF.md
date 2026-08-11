**English** | [한국어](PROOF.ko.md)

# Connected induced subgraphs of prisms, Möbius ladders and antiprisms

We prove the closed forms conjectured on OEIS
[A286182](https://oeis.org/A286182) (prism),
[A286185](https://oeis.org/A286185) (Möbius ladder) and
[A286183](https://oeis.org/A286183) (antiprism), and deduce the linear
recurrences and generating functions conjectured on the same entries.

The prism case is **not new**: it is Lemma 7.2 of A. Vince, *The average size of
a connected vertex set of a graph — explicit formulas and open problems*,
J. Graph Theory **97** (2021) 82–103, by a different (composition/binomial)
argument. We include it because the same three-line computation delivers all
three families, and because it validates the method against a published result.
For the Möbius ladder and the antiprism we found no proof in the literature; see
[README.md](README.md) for the search that was carried out. **No novelty is
claimed** for any of the three.

## 0. Setup

Fix `n ≥ 1`. All three graphs have vertex set `V = Z_n × {0,1}`; we call
`{i} × {0,1}` *column i* and write `(i,r)` for row `r` of column `i`. Every
graph contains the **rungs** `(i,0) ~ (i,1)`, and differs only in how
consecutive columns are joined. Every inter-column edge below is subject to
`i ≠ j`, which is what keeps the graph simple in the degenerate cases `n = 1,2`
that OEIS includes.

| graph | inter-column edges between columns `i` and `i+1` |
|---|---|
| prism `CL_n = C_n □ K₂` | `(i,0)~(i+1,0)`, `(i,1)~(i+1,1)` |
| Möbius ladder `ML_n` | the same, except that for `i = n-1` the two edges are **twisted**: `(n-1,0)~(0,1)`, `(n-1,1)~(0,0)` |
| antiprism `AP_n` | `(i,0)~(i+1,0)`, `(i,1)~(i+1,1)`, and the **diagonal** `(i,1)~(i+1,0)` |

For `ML_n` the rails form a single `2n`-cycle
`(0,0)(1,0)…(n-1,0)(0,1)(1,1)…(n-1,1)` and the rungs join antipodal vertices of
it, so `ML_n` is the Möbius ladder in the usual sense. `AP_n` is `4`-regular for
`n ≥ 3` and `AP_3` is the octahedron. At `n = 1` all three are `K₂`; at `n = 2`
the prism is `C₄` while `ML_2 = AP_2 = K₄`. These agree with the OEIS terms
`a(1) = 3` and `a(2) = 13, 15, 15`.

Let `a(n)` be the number of nonempty `S ⊆ V` whose induced subgraph is
connected. For `S ⊆ V` write `c_i = {r : (i,r) ∈ S}`; a column is *occupied* if
`c_i ≠ ∅`, and the three occupied states are abbreviated

    A = {0},   B = {1},   C = {0,1}.

Call occupied columns `i` and `i+1` **linked** if some edge of the graph joins a
vertex of column `i` in `c_i` to a vertex of column `i+1` in `c_{i+1}`. Define
the **column graph** `H(S)`: vertices are the occupied columns, edges are the
linked cyclically consecutive pairs.

**Lemma 0 (contraction).** The components of the induced subgraph on `S`
correspond to the components of `H(S)`. In particular `S` is connected iff
`H(S)` is connected.

*Proof.* Each occupied column induces a connected subgraph: `A` and `B` are
single vertices and `C` is a rung edge. Every edge of the graph either lies
inside a column or joins two cyclically consecutive columns, and such an edge is
present in the induced subgraph exactly when those columns are linked.
Projecting a path in the induced subgraph to its sequence of columns and
deleting repetitions gives a walk in `H(S)`; conversely an edge of `H(S)`
lifts to an edge of the induced subgraph. ∎

Note the "linked" relation must be read with the cyclic order: a path in `H(S)`
may wrap around. (For instance in `CL_4` the configuration `ABCC` has columns 0
and 1 unlinked, yet they lie in one component via `0–3–2–1`.)

Being linked depends only on `(c_i, c_{i+1})`, so it is described by a
`{0,1}`-matrix indexed by `A, B, C`. Two nonempty row-sets meet unless they are
`{0}` and `{1}`, so:

* **prism and Möbius rails.** Linked iff `c_i ∩ c_{i+1} ≠ ∅`, i.e. iff
  `{c_i, c_{i+1}} ≠ {A,B}`. Transfer matrix (order `A,B,C`)

      M = [[1,0,1],
           [0,1,1],
           [1,1,1]],     char. poly (x-1)(x²-2x-1),  eigenvalues 1, 1±√2.

* **Möbius twisted seam.** Column `n-1` sees column `0` through the row swap
  `σ : A↔B, C↦C`, so the seam is linked iff `c_{n-1} ∩ σ(c_0) ≠ ∅`; the seam
  matrix is `M·P_σ`, where `P_σ` is the permutation matrix of `σ`. Note
  `M P_σ = P_σ M`, since `σ` is an automorphism of the linking relation.

* **antiprism.** The diagonal `(i,1)~(i+1,0)` links the *ordered* pair `(A,B)`
  as well, and no edge links `(B,A)`. Transfer matrix

      Mₐ = [[1,1,1],
            [0,1,1],
            [1,1,1]],    char. poly (x)(x²-3x+1),  eigenvalues 0, (3±√5)/2.

Throughout, `P` = A000129 (Pell, `P₀=0, P₁=1, P_{m+2}=2P_{m+1}+P_m`),
`Q` = A002203 (`Q₀=Q₁=2`, same recurrence, `Q_m = (1+√2)^m + (1-√2)^m`),
`t` = A001333 `= Q/2` (`1,1,3,7,17,41,…`), and `F`, `L` are the Fibonacci and
Lucas numbers, so A001906`(m) = F(2m)` and A005248`(m) = L(2m)`.

## 1. Contiguity, and the two cases

If `S` is connected and some column is empty, then the occupied columns form a
cyclic interval (*arc*): an empty column carries no vertex, so by Lemma 0 no
path crosses it, and occupied columns lying in two different arcs would be in
different components. Hence every connected `S` falls into exactly one of

* **(I)** some column is empty — the occupied columns are an arc of length `m`
  with `1 ≤ m ≤ n-1`;
* **(II)** every column is occupied.

Write `g(n)` for the number of connected configurations in case (II).

## 2. Case (I): the arcs

Let `f(m)` be the number of connected configurations occupying exactly a given
arc of `m` consecutive columns, `1 ≤ m ≤ n-1`.

For `1 ≤ m ≤ n-1` the `n` translates of an arc of length `m` are distinct sets
(the complement is nonempty, so the first element of the arc is well defined),
and the arc's column graph is a **path** with exactly `m-1` edges: its endpoints
`s` and `s+m-1` are cyclically adjacent only if `m-1 ≡ ±1 (mod n)`, i.e. `m = 2`
— where that adjacency *is* the single internal one — or `m ≡ 0 (mod n)`, which
`m ≤ n-1` excludes. (This is tight at `m = n-1`.) So, by Lemma 0, `f(m)` counts
the words `w ∈ {A,B,C}^m` all of whose `m-1` consecutive pairs are linked:

    f(m) = 1ᵀ Mᵐ⁻¹ 1        (prism, Möbius),
    f(m) = 1ᵀ Mₐᵐ⁻¹ 1       (antiprism).

For the Möbius ladder the arc may contain the twisted seam; applying `σ` to
every column after the seam is a bijection on configurations that turns the
twisted link into an ordinary one and preserves all the others (`σ` is an
automorphism of the linking relation), so `f(m)` is the same as for the prism.

**Prism/Möbius.** Splitting by last letter, with `a_m, b_m, c_m` the numbers of
such words ending in `A, B, C`:

    a_{m+1} = a_m + c_m,  b_{m+1} = b_m + c_m,  c_{m+1} = a_m + b_m + c_m,
    a_1 = b_1 = c_1 = 1.

By the `A↔B` symmetry `a_m = b_m`, and then `a_{m+1} = a_m + c_m`,
`c_{m+1} = 2a_m + c_m` are exactly the Pell recurrences with
`(a_m, c_m) = (P_m, t_m)`. Hence

    f(m) = 2 P_m + t_m.                                                  (1)

Using `Σ_{m=0}^{k} t_m = P_{k+1}` and `Σ_{m=1}^{k} P_m = (P_k + P_{k+1} - 1)/2`,

    Σ_{m=1}^{n-1} f(m) = (P_{n-1} + P_n - 1) + (P_n - 1)
                       = P_{n-1} + 2P_n - 2 = P_{n+1} - 2.                (2)

**Antiprism.** Here `1ᵀ Mₐ^{m-1} 1 = F(2m+2)` (both sides satisfy
`x_{m+1} = 3x_m - x_{m-1}` with the same two initial values `3, 8`), so

    f(m) = F(2m+2) = A001906(m+1),
    Σ_{m=1}^{n-1} f(m) = Σ_{k=2}^{n} F(2k) = F(2n+1) - 2,                (2ₐ)

using `Σ_{k=1}^{n} F(2k) = F(2n+1) - 1`.

So case (I) contributes `n (P_{n+1} - 2)` for the prism and the Möbius ladder,
and `n (F(2n+1) - 2)` for the antiprism.

## 3. Case (II): every column occupied — assume `n ≥ 3`

For `n ≥ 3` the column graph of a case-(II) configuration is the `n`-cycle with
the unlinked adjacencies deleted, and a cycle minus `k` edges is connected iff
`k ≤ 1`. (This step genuinely needs `n ≥ 3`: for `n = 2` the two columns are
joined by a single adjacency, not two, and for `n = 1` there is none. Those two
cases are checked directly in §4.) Hence

    g(n) = #{0 unlinked adjacencies} + #{exactly 1 unlinked adjacency}.

**Zero unlinked.** These are the closed walks of length `n` in the transfer
digraph:

    prism:      tr(Mⁿ)        = 1 + Q_n        (eigenvalues 1, 1±√2)
    Möbius:     tr(Mⁿ P_σ)    = Q_n - 1
    antiprism:  tr(Mₐⁿ)       = L(2n)          (eigenvalues 0, (3±√5)/2)

For the Möbius trace: `P_σ` commutes with `M`; on the `σ`-antisymmetric
eigenvector `(1,-1,0)` (eigenvalue `1` of `M`) `P_σ` acts by `-1`, and on the
`σ`-symmetric plane it acts by `+1`, where `M` has eigenvalues `1±√2`. So
`tr(Mⁿ P_σ) = (1+√2)ⁿ + (1-√2)ⁿ - 1 = Q_n - 1`, whereas `tr(Mⁿ) = Q_n + 1`.
For the antiprism, `tr(Mₐⁿ) = 0ⁿ + φ^{2n} + φ^{-2n} = L(2n)` for `n ≥ 1`.

**Exactly one unlinked.** Sending a configuration to the position of its unique
unlinked adjacency is well defined, and for `n ≥ 3` the cycle has `n` distinct
adjacencies, so the fibres partition the class into `n` blocks of equal size.
(For the Möbius ladder all `n` positions carry the same count: moving the twist
by the `σ`-transform of §2 is a bijection between the blocks.) Cutting at the
bad adjacency turns a block into the set of words `w₁ … w_n` whose `n-1`
internal adjacencies are all linked and whose wrap-around pair is not:

* **prism:** `{w₁, w_n} = {A,B}`, giving `2 (M^{n-1})_{A,B}`. Writing
  `u_m = (Mᵐ)_{AA}`, `v_m = (Mᵐ)_{AB}`, the vector `(1,-1,0)` is a
  `1`-eigenvector of `M`, so `u_m - v_m = 1` for all `m`; also
  `u_m + v_m = t_m`. Hence `v_m = (t_m - 1)/2` and the block has size
  `t_{n-1} - 1`.
* **Möbius:** the seam is linked iff `c_{n-1} ∩ σ(c_0) ≠ ∅`, so *un*linked means
  `{c_{n-1}, σ(c_0)} = {A,B}`, i.e. `(c_{n-1}, c_0) ∈ {(A,A), (B,B)}`. The block
  has size `(M^{n-1})_{AA} + (M^{n-1})_{BB} = 2 u_{n-1} = t_{n-1} + 1`.
* **antiprism:** the only unlinked ordered pair is `(B,A)`, so the block has
  size `(Mₐ^{n-1})_{A,B} = F(2n-2)`.

Therefore, for `n ≥ 3`,

    prism:      g(n) = (Q_n + 1) + n (t_{n-1} - 1),
    Möbius:     g(n) = (Q_n - 1) + n (t_{n-1} + 1),                       (3)
    antiprism:  g(n) = L(2n)    + n F(2n-2).

## 4. Assembly

Add case (I) and case (II). For the prism and the Möbius ladder use
`t_{n-1} = P_{n-1} + P_{n-2}` and `P_{n+1} = 2P_n + P_{n-1}`, whence

    P_{n+1} + t_{n-1} = 2P_n + 2P_{n-1} + P_{n-2} = 2P_n + P_n = 3 P_n.   (4)

**Prism** (`n ≥ 3`):

    a(n) = n(P_{n+1} - 2) + (Q_n + 1) + n(t_{n-1} - 1)
         = Q_n + n(P_{n+1} + t_{n-1}) - 3n + 1
         = Q_n + 3 n P_n - 3 n + 1 = A002203(n) + 3n·A000129(n) - 3n + 1.

**Möbius ladder** (`n ≥ 3`):

    a(n) = n(P_{n+1} - 2) + (Q_n - 1) + n(t_{n-1} + 1)
         = Q_n + n(P_{n+1} + t_{n-1}) - n - 1
         = Q_n + 3 n P_n - n - 1 = A002203(n) + 3n·A000129(n) - n - 1.

**Antiprism** (`n ≥ 3`): from `F(2n+1) = 2F(2n) - F(2n-2)` we get
`F(2n+1) + F(2n-2) = 2 F(2n)`, so

    a(n) = n(F(2n+1) - 2) + L(2n) + n F(2n-2)
         = L(2n) + n(F(2n+1) + F(2n-2)) - 2n
         = L(2n) + 2 n F(2n) - 2 n = A005248(n) - 2n + 2n·A001906(n).

**The degenerate cases `n = 1, 2`,** where §3 does not apply, are checked
directly against the same formulas:

| | `n = 1` (`K₂`) | `n = 2` |
|---|---|---|
| prism | `3 = Q₁ + 3P₁ - 3 + 1` | `C₄`: `13 = Q₂ + 6P₂ - 6 + 1` |
| Möbius | `3 = Q₁ + 3P₁ - 1 - 1` | `K₄`: `15 = Q₂ + 6P₂ - 2 - 1` |
| antiprism | `3 = L(2) - 2 + 2F(2)` | `K₄`: `15 = L(4) - 4 + 4F(4)` |

(`K₂` has `3` connected induced non-null subgraphs, `C₄` has `13`, and `K₄` has
`2⁴ - 1 = 15` since every nonempty subset of a complete graph is connected.)
So all three closed forms hold for **every `n ≥ 1`**. ∎

## 5. The conjectured recurrences and generating functions

`Q_n` and `P_n` are annihilated by `x² - 2x - 1`, so `n P_n` is annihilated by
`(x² - 2x - 1)²`; the affine parts `-3n+1` and `-n-1` are annihilated by
`(x-1)²`. Since `x²-2x-1` and `x-1` are coprime, both the prism and the Möbius
closed forms are annihilated by

    (x-1)² (x²-2x-1)² = x⁶ - 6x⁵ + 11x⁴ - 4x³ - 5x² + 2x + 1,

which is exactly the recurrence `a(n) = 6a(n-1) - 11a(n-2) + 4a(n-3) + 5a(n-4)
- 2a(n-5) - a(n-6)` conjectured on A286182 and A286185 — valid for `n ≥ 7`,
as OEIS states (it fails at `n = 6`, where it would need the non-combinatorial
value `a(0)`). Likewise `L(2n)` and `F(2n)` are annihilated by `x² - 3x + 1`, so
the antiprism closed form is annihilated by

    (x-1)² (x²-3x+1)² = x⁶ - 8x⁵ + 24x⁴ - 34x³ + 24x² - 8x + 1,

the recurrence conjectured on A286183, again for `n ≥ 7`.

Multiplying the closed forms by those denominators leaves the numerators
conjectured on the entries (all higher coefficients vanish identically):

    prism      x(3 - 5x + 6x² - 8x³ - 5x⁴ - 3x⁵) / ((1-x)²(1-2x-x²)²)
    Möbius     x(3 - 3x - 2x² - 4x³ + 3x⁴ - x⁵) / ((1-x)²(1-2x-x²)²)
    antiprism  x(3 - 9x + 12x² - 15x³ + 9x⁴ - 2x⁵) / ((1-x)²(1-3x+x²)²)

The Möbius numerator is Robert Israel's `(3x - 3x² - 2x³ - 4x⁴ + 3x⁵ - x⁶) /
(1 - 3x + x² + x³)²`, since `1 - 3x + x² + x³ = (1-x)(1-2x-x²)`. ∎

## What is machine-checked

`certificate.py` re-derives, with exact integer arithmetic:

* the counts `a(n)` for all three graphs by exhaustive enumeration of all
  `2^{2n}` vertex subsets (`n ≤ 10`, or `n ≤ 13` with `--full`), and by a
  *generic* frontier dynamic program that is given only a graph and knows
  nothing about ladders (validated against brute force on 200 random graphs and
  run to `n = 200`);
* agreement of both with the OEIS data terms and with the closed forms;
* the intermediate quantities `f(m)`, `g(n)` of §§2–3 against direct
  enumeration, and every transfer-matrix identity of §§2–3;
* the recurrences of §5 to `n = 200` and the generating-function numerators.

`lean_graph_check.lean` prints the edge sets of the Lean definitions of the three
graphs so they can be diffed against the ones the certificate enumerates.
`AgenticConjectures/OeisA286185A286183.lean` states the three closed-form
conjectures formally and proves, sorry-free, that each closed form satisfies the
corresponding order-6 recurrence — so the recurrence conjectures follow from the
closed-form conjectures inside Lean. The graph-theoretic content of §§0–4 is
**not** formalised in Lean.
