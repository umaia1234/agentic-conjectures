**English** | [한국어](DETAILS.ko.md)

# TxGraffiti Conjecture 3: mathematical details

This file collects the arguments behind [README.md](README.md). Each section says what checks it.
"Pen and paper" means that no machine has checked the argument.

Notation. `G` is a finite simple graph with `n` vertices and `m` edges, `r`-regular unless stated
otherwise. `i(G)` is the least size of an independent dominating set, which is the same as the
least size of a maximal independent set. `µ*(G)` is the least size of a maximal matching. An edge
of a matching `M` *dominates* itself and every edge sharing a vertex with it, and a matching is
maximal exactly when it dominates every edge. `V(M)` is the set of vertices covered by `M`.

## 1. The lower bound and efficient edge dominating sets

*The inequality is checked in Lean (`card_edgeFinset_le_mul_saturationNumber`). The
characterization of equality is pen and paper.*

**Lemma 1** (Biedl, Demaine, Duncan, Fleischer and Kobourov 2004, Theorem 7). If every degree is
at most `r` and `r ≥ 1`, then `m ≤ (2r − 1)|M|` for every maximal matching `M`. Hence
`µ*(G) ≥ m/(2r − 1)`.

*Proof.* An edge `uv ∈ M` dominates itself, at most `r − 1` other edges at `u` and at most `r − 1`
other edges at `v`. Every edge is dominated by some edge of `M`. ∎

In an `r`-regular graph each edge `uv` dominates exactly `2r − 1` edges, so equality holds exactly
when every edge is dominated by exactly one edge of `M`. Such an `M` is an *efficient edge
dominating set* (EEDS; Grinstead, Slater, Sherwani and Holmes 1993). A maximal matching is an EEDS
exactly when it is *induced*, that is, no edge joins two different `M`-edges:

- an edge joining two `M`-edges is dominated by both;
- if `M` is induced, an edge outside `M` has at least one end in `V(M)` by maximality. It cannot
  have both ends there, because they would lie on two different `M`-edges or form an `M`-edge. So
  only the `M`-edge at that end dominates it.

**Corollary 2.** An `r`-regular graph has `µ* = m/(2r − 1)` exactly when it has an EEDS,
equivalently an induced maximal matching. Gupta's Proposition 2 states the same thing through the
identity `(4r − 2)|M| = rn + 2q`, where `q` counts the edges outside `M` with both ends in `V(M)`.

For example, a cubic graph on 48 vertices has `m = 72`, and `72/5` is not an integer, so `G48` has
no EEDS. The 50- and 60-vertex counterexamples of Afrasyab and Iwane do have one (`m = 75 = 5·15`
and `m = 90 = 5·18`); see section 5.

**Degrees 1 and 2** (pen and paper, standard). A 1-regular graph is a perfect matching, with
`i = µ* = n/2`. A 2-regular graph is a disjoint union of cycles, `i(C_ℓ) = µ*(C_ℓ) = ⌈ℓ/3⌉`, and
both invariants add up over components. So the conjecture holds for `r ≤ 2`, and with section 4
the open degrees are exactly the `r ≥ 4` not divisible by 3.

## 2. The cubic counterexample `G48`

*Lean, given the DRAT-certified `G48LowerBound`.*

`G48` is cubic on 48 vertices with 72 edges (`G48_degree`, `card_edgeFinset_G48`). The 15 edges
`M48 = {{0,1}, {2,3}, …, {28,29}}` form a maximal matching (`isMaximalEdgeMatching_M48`), and
Lemma 1 gives `µ* ≥ ⌈72/5⌉ = 15`, so `µ*(G48) = 15` (`saturationNumber_G48`). The set
`D48 = {0, 2, 4, …, 28, 34}` is an independent dominating set with 16 vertices
(`isNIndepDominatingSet_D48`). The DRAT certificate shows that no independent dominating set has
at most 15 vertices (`G48LowerBound`), so `i(G48) = 16` (`indepDominationNumber_G48`).

## 3. The CNF behind the certificate

*Pen and paper. CI regenerates the CNF from the Lean source and checks its SHA-256, and
`drat-trim` checks the proof.*

The variables are `x_v` for the 48 vertices, `y_i` for the 15 pairs `P_i = {2i, 2i+1}` (the edges
of `M48`), and the totalizer outputs. The clauses are:

- (D) for every vertex `v`: `x_v ∨ x_{w1} ∨ x_{w2} ∨ x_{w3}`, where `w1, w2, w3` are its neighbours;
- (I) for every edge `uw`: `¬x_u ∨ ¬x_w`;
- (P) for every `i`: `¬x_{2i} ∨ y_i` and `¬x_{2i+1} ∨ y_i`;
- (T) a totalizer over the 33 units `y_0, …, y_14, x_30, …, x_47`. Its root output `o_16` means
  "at least 16 units are true", and the unit clause `¬o_16` forbids it.

[certificates/g48_cnf.py](certificates/g48_cnf.py) documents the numbering and the order of the
clauses.

**Lemma 3.** If the CNF is unsatisfiable, every independent dominating set of `G48` has at least
16 vertices.

*Proof.* Let `D` be an independent dominating set with `|D| ≤ 15`. Put `x_v = [v ∈ D]` and
`y_i = [D ∩ P_i ≠ ∅]`.

- (D) holds because `D` is dominating, (I) because `D` is independent, and (P) by the choice of
  `y_i`.
- Each `P_i` is an edge of `G48` (the script checks this), so `|D ∩ P_i| ≤ 1`. The number of true
  units is therefore `|D ∩ {0, …, 29}| + |D ∩ {30, …, 47}| = |D| ≤ 15`.
- Give each totalizer output its intended value: an output `o_j` of a node is true when at least
  `j` units below that node are true. Each totalizer clause `¬a_i ∨ ¬b_j ∨ o_{i+j}` then holds,
  because `a_i ∧ b_j` means that at least `i + j` units below the node are true. The root output
  `o_16` is false.

So the CNF is satisfiable. ∎

Only this direction is used. The converse holds too: a satisfying assignment yields an
independent dominating set with at most 15 vertices. `--check` also builds the CNF with bound 16
and checks that the assignment above, built from `D48`, satisfies it.

## 4. The blow-up lemma

*Lean: `degree_blowup`, `isNIndepDominatingSet_of_blowup`, `isNIndepDominatingSet_blowup`,
`indepDominationNumber_blowup`, `isMaximalEdgeMatching_blowupMatching`,
`saturationNumber_blowup_le`, `not_statementDeg`.*

For `t ≥ 1`, the graph `G[K̄_t]` has vertex set `V(G) × {1, …, t}`, and `(u, a) ∼ (v, b)` exactly
when `u ∼ v` in `G`. Each vertex is replaced by `t` pairwise non-adjacent twins.

**Lemma 4.**
(a) `deg(v, a) = t·deg(v)`.
(b) `i(G[K̄_t]) = t·i(G)`.
(c) `µ*(G[K̄_t]) ≤ t·µ*(G)`.

*Proof.*

(a) The neighbours of `(v, a)` are the `(w, b)` with `w ∼ v`.

(b) Let `D` be an independent dominating set of `G`.
- `D × [t]` is independent, since its vertices project into `D`.
- It is dominating: a vertex `(v, b)` with `v ∉ D` has a neighbour `w ∈ D`, and `(w, b)` is
  adjacent to it.

So `i(G[K̄_t]) ≤ t·i(G)`. Conversely, let `D'` be an independent dominating set of `G[K̄_t]`, and
let `(v, a) ∈ D'`.
- Every twin `(v, b)` lies in `D'`. Otherwise a neighbour of `(v, b)` lies in `D'`. That vertex is
  also a neighbour of `(v, a)`, which contradicts independence.
- So `D' = D × [t]`, where `D` is the projection of `D'`.
- `D` is independent: an edge of `G` inside `D` would give an edge inside `D'`.
- `D` is dominating: if `v ∉ D`, then `(v, 1)` has a neighbour `(w, b) ∈ D'`, so `w ∈ D` and
  `w ∼ v`.
- Hence `|D'| = t|D| ≥ t·i(G)`.

(c) Let `M` be a maximal matching of `G`. Then `M' = {(u, a)(v, a) : uv ∈ M, a ∈ [t]}` is a
matching with `t|M|` edges and `V(M') = V(M) × [t]`. An edge `(u, a)(w, b)` of `G[K̄_t]` has
`u ∼ w`, so by maximality `u` or `w` lies in `V(M)`, and the edge meets `V(M')`. So `M'` is
maximal. ∎

**Corollary 5.** Given `G48LowerBound`, for every `t ≥ 1` the graph `G48[K̄_t]` is `3t`-regular on
`48t` vertices with `i = 16t > 15t ≥ µ*`. So the conjecture fails in every degree divisible by 3.

For `t = 2`, CP-SAT reports `µ*(G48[K̄_2]) = 30`, so (c) is tight there; the same holds for the
50-vertex graph `G50` ([search/check_blowup.py](search/check_blowup.py)). Nothing depends on this.

## 5. Graphs with an EEDS and balanced CNF formulas

*Pen and paper. The correspondence is Iwane's (Proposition 16); Gupta uses the same
reformulation (Section 8).*

Let `G` be `r`-regular with an EEDS `M`, let `q = |M|`, and let `C = V(G) \ V(M)`.

- `C` is independent, by maximality. Every vertex of `V(M)` has its partner and `r − 1`
  neighbours in `C`, because `M` is induced.
- Read each `M`-edge as a variable whose two literals are its endpoints, and each `c ∈ C` as the
  clause made of its `r` neighbours. This gives an `r`-CNF `F(G)` with `q` variables and `|C|`
  clauses in which every literal occurs exactly `r − 1` times, so `r|C| = 2(r − 1)q`. A clause may
  contain both literals of one variable, in which case it is always true. It never contains the
  same literal twice.
- Conversely, take an `r`-CNF in which every literal occurs exactly `r − 1` times and no clause
  repeats a literal. Join the two literals of each variable, add one vertex per clause, and join
  it to its literals. The result is `r`-regular, and the variable edges form an EEDS. For proper
  formulas, whose clauses use `r` distinct variables, this is Iwane's `G(F)`.

**Lemma 6.** If `F(G)` is satisfiable, then `i(G) ≤ q = µ*(G)`.

*Proof.* Let `T` be the set of true literals of a satisfying assignment. It contains one endpoint
of every `M`-edge.
- `T` is independent, because `M` is induced.
- `T` dominates `V(M)`: each false literal is adjacent to its true partner.
- `T` dominates `C`: each clause contains a true literal.

So `i(G) ≤ |T| = q`, and `q = µ*(G)` by Corollary 2. ∎

So an `r`-regular counterexample with an EEDS needs an unsatisfiable `r`-CNF in which every
literal occurs exactly `r − 1` times. Iwane's Proposition 16 gives `i(G(F))` exactly, as a
minimum over partial assignments. Iwane's 113 cubic counterexamples are of this form, built from
unsatisfiable formulas with 15 and 18 variables. One of them is the 50-vertex graph that Afrasyab
studies (we checked this locally with nauty's `labelg`). `G48` is not of this form (section 1).

For `r = 3` such unsatisfiable formulas exist. The smallest have 20 clauses: Zhang, Peitl and
Szeider proved that no unsatisfiable `(3, 2, 2)`-formula has fewer, and Iwane's formula `F*` has
20 (Iwane, Section 2). For `r = 4` none is known. Whether an unsatisfiable `(4, 3, 3)`-formula
exists at all is open: one where each variable occurs at most 3 times positively and at most 3
times negatively (Iwane, after Problem 17; Gupta, Section 8).

## 6. Degree at least 7: graphs with an EEDS satisfy `i ≤ µ*`

*Pen and paper. This is a direct corollary of Gupta's Theorem 1, whose proof we repeat in this
special case. It is not a new result.*

**Proposition 7.** Let `r ≥ 7` and let `G` be `r`-regular with an EEDS. Then `i(G) ≤ µ*(G)`.

*Proof.* By Lemma 6 it suffices to show that `F = F(G)` is satisfiable.
- Choose the value of each variable uniformly and independently.
- Drop the clauses that contain both literals of a variable; they are always true.
- For each remaining clause `c`, let `A_c` be the event that `c` is false. Its `r` literals use
  distinct variables, so `Pr[A_c] = 2^{-r}`.
- Join `A_c` and `A_{c'}` when some literal of `c` is the complement of a literal of `c'`. The
  events are atoms of independent variables, and two events that are not joined agree on every
  variable they share. So this conflict graph is a lopsidependency graph (Erdős and Spencer 1991;
  Gupta, Section 3, spells out the argument).
- Each of the `r` literals of `c` has a complement that occurs in `r − 1` clauses. So `A_c` has at
  most `d = r(r − 1)` neighbours.
- The lopsided Local Lemma gives `Pr[no A_c occurs] > 0` when `e·2^{-r}·(d + 1) ≤ 1`, that is,
  when `g(r) = e(r² − r + 1)/2^r ≤ 1`.
- `g(7) = 43e/128 ≈ 0.913`. Moreover `g(r + 1)/g(r) = (r² + r + 1)/(2(r² − r + 1)) ≤ 1` for
  `r ≥ 3`, which is equivalent to `r² − 3r + 1 ≥ 0`. So `g(r) < 1` for every `r ≥ 7`. ∎

**Relation to Gupta's theorem.** Gupta's Theorem 1 says `γ(G) ≤ γ_e(G)` for every `r`-regular
graph with `r ≥ 7`.
- The proof takes a random transversal of a minimum maximal matching (one endpoint of each edge)
  and shows, by the same computation, that it is dominating with positive probability. Its
  lopsidependency degree is also at most `r(r − 1)`.
- The method stops at `g(6) = 31e/64 ≈ 1.317 > 1`.
- When the minimum maximal matching is induced, that is, an EEDS, every transversal is
  independent. So Gupta's dominating transversal is an independent dominating set of size `µ*`.

Proposition 7 is exactly this observation. Without an induced minimum maximal matching the
transversal need not be independent, which is the point of Gupta's Remark 1.

**Iwane's Problem 17.** It asks, for `k ≥ 4`, whether some proper `(k − 1)`-balanced `k`-CNF `F`
has `i(G(F)) > µ*(G(F))`. `G(F)` is `k`-regular with an EEDS, so Proposition 7 answers no for
every `k ≥ 7`. For `k = 4, 5, 6` the question stays open, and the counting fails there:
`g(4) ≈ 2.21`, `g(5) ≈ 1.78`, `g(6) ≈ 1.32`.

## 7. Minimally unsatisfiable formulas of deficiency 1

*Pen and paper.*

`MU(1)` is the class of minimally unsatisfiable CNF formulas with one more clause than variables.
Zhang, Peitl and Szeider (Section 4.2) recall that `MU(1)` is exactly the class of formulas built
from `{□}` by *disjunctive splitting*.
- `F = F1 ⊕_x F2`, where `x` occurs in neither `F1` nor `F2`.
- `x` is added to a nonempty set of clauses of `F1`, and `x̄` to a nonempty set of clauses of
  `F2`.

**Proposition 8.** Let `k ≥ 2`. No formula in `MU(1)` has all clauses of length exactly `k` and
every literal occurring at most `k − 1` times.

*Proof.* Suppose `F` is such a formula. Take a derivation of `F` from `{□}`, and its derivation
tree: a full binary tree whose `m` leaves are the clauses of `F`, and whose `m − 1` internal nodes
are the splitting steps. Here `m ≥ 2`, because `□` has length `0 < k`.
- A node `u` that splits on `x` adds `x` to `p_u ≥ 1` leaves of its left subtree and `x̄` to
  `q_u ≥ 1` leaves of its right subtree.
- Every literal of every clause is added at exactly one ancestor of its leaf. Counting literal
  occurrences gives `km = Σ_u (p_u + q_u)`.
- `p_u` is at most the number of leaves in the left subtree, and at most the number of
  occurrences of `x`, so at most `k − 1`. The same holds for `q_u`.

Let `a` be the number of internal nodes with two leaf children, `b` the number with exactly one,
and `d` the number with none. Then `p_u + q_u` is at most 2, `k` and `2(k − 1)` for these three
kinds. Counting leaves and internal nodes gives `2a + b = m` and `a + b + d = m − 1`, so
`d = a − 1`. Hence

`km = Σ_u (p_u + q_u) ≤ 2a + kb + 2(k − 1)d = 2a + k(m − 2a) + 2(k − 1)(a − 1) = km − 2(k − 1) < km`,

which is a contradiction. ∎

For `k = 3` this is the `∞` entry at `p = q = 2` of Zhang, Peitl and Szeider's Table 6. In
general, take an unsatisfiable `k`-CNF in which each literal occurs at most `k − 1` times.
- Each minimally unsatisfiable subformula of it has the same two properties.
- By Proposition 8 and Tarsi's lemma (deficiency at least 1), each such subformula has deficiency
  at least 2.
- So the formulas that section 5 asks for cannot be built by disjunctive splitting from `{□}`
  alone.

## 8. Other constructions that were searched

*Computer search, local only; numbers in [search/search_summary.txt](search/search_summary.txt).*

Lemma 4 multiplies all degrees by `t`. To reach degrees 4 and 5 from cubic graphs, one can instead
give each vertex its own weight: `B[t]` replaces `v` by `t(v)` twins and is `r`-regular when
`Σ_{w ∼ v} t(w) = r` for every `v`.
- A *total perfect code* `W` of a cubic graph meets every neighbourhood in exactly one vertex. It
  gives the 4-regular weighting `t = 2` on `W` and 1 elsewhere, and the 5-regular weighting
  `t = 1` on `W` and 2 elsewhere.
- None of the 114 cubic counterexamples we had has a total perfect code: `G48` and Iwane's 113
  graphs on 50 and 60 vertices. On 50 vertices this is forced, since a total perfect code needs
  `n = 3|W|`.
- All 104,109 weightings of the small cubic and quartic bases in the summary were checked, with no
  counterexample.

Line graphs of cubic graphs and the products `G□K_2` and `G□K_3` are 4- and 5-regular. None was
a counterexample for cubic `G` with at most 20 vertices. `G48□K_2` and `G48□K_3` satisfy `i ≤ µ*`
already through the lower bound `⌈m/(2r − 1)⌉`.

## References

- K. Afrasyab, A 50-vertex cubic counterexample to the domination-versus-edge-domination
  conjecture, [arXiv:2609.10783](https://arxiv.org/abs/2609.10783).
- J. Baste, M. Fürst, M. A. Henning, E. Mohr and D. Rautenbach, Domination versus edge domination,
  *Discrete Appl. Math.* 285 (2020) 343–349.
- T. Biedl, E. D. Demaine, C. A. Duncan, R. Fleischer and S. G. Kobourov, Tight bounds on maximal
  and maximum matchings, *Discrete Math.* 285 (2004) 7–15.
- R. Davila, B. Brimkov and R. Pepper, In Reverie Together: Ten Years of Mathematical Discovery
  with a Machine Collaborator, [arXiv:2507.17780](https://arxiv.org/abs/2507.17780).
- P. Erdős and J. Spencer, Lopsided Lovász local lemma and Latin transversals, *Discrete Appl.
  Math.* 30 (1991) 151–154.
- D. L. Grinstead, P. J. Slater, N. A. Sherwani and N. D. Holmes, Efficient edge domination
  problems in graphs, *Inform. Process. Lett.* 48 (1993) 221–228.
- C. Gupta, Domination versus edge domination in regular graphs of degree at least seven,
  [arXiv:2608.22498](https://arxiv.org/abs/2608.22498).
- H. Iwane, Independent domination can exceed minimum maximal matching in cubic graphs: a
  counterexample to a TxGraffiti conjecture, Zenodo
  [10.5281/zenodo.22924244](https://doi.org/10.5281/zenodo.22924244).
- T. Zhang, T. Peitl and S. Szeider, Small unsatisfiable k-CNFs with bounded literal occurrence,
  SAT 2024, LIPIcs 305, Article 31; [arXiv:2405.16149](https://arxiv.org/abs/2405.16149).
