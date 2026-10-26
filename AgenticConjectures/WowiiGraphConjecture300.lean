import Mathlib

/-!
# Written on the Wall II, Conjecture 300 is false

Conjecture 300 of E. DeLaViña's *Written on the Wall II* (conjectures of Graffiti.pc, section
"Upper bounds for Total Domination", dated March 1, 2007) states: if `G` is a simple connected
graph with `n(G) > 2`, then `γ_t(G) ≤ (1/2) [n(G) + frequency of λ_min(Ḡ)]`. Here `γ_t` is the
total domination number, `n(G)` the number of vertices, `λ(v)` the independence number of the
subgraph induced by the neighbourhood of `v`, `λ_min` its minimum over the vertices, `Ḡ` the
complement of `G`, and the frequency of `λ_min(Ḡ)` the number of vertices at which `λ`,
computed in `Ḡ`, attains its minimum. The bound is a real number; it is not rounded.

`not_statement : ¬ statement` refutes this reading with a connected graph on 15 vertices
(`family 1`), for which `γ_t = 10` while the bound is `(15 + 4) / 2 = 19/2`. More generally,
`family_gap` shows `2 γ_t = n + frequency + t` for the graph `family t`, so every `t ≥ 1` gives
a counterexample (`family_violates`), and the violation `t / 2` is unbounded. `graph12_violates`
and `not_statement_graph12` give a counterexample on 12 vertices, the smallest order: by the
computation recorded in the README (not part of this file), no connected graph on at most 11
vertices violates the bound.

## Correspondence with Formal Conjectures

Formal Conjectures has no statement of Conjecture 300; `statement` is ours. It reuses the
definitions and the statement style of google-deepmind/formal-conjectures at commit
`49ba26bac3212084999860c575fcc70af42b3128` (Apache-2.0):

* `IsTotalDominating`, `IsTotalNDominatingSet` and `totalDominationNumber` are copied from
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Domination.lean` (lines 75–91),
  `indepNeighborsCard` from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Independence.lean`
  (line 40), and `localIndependenceMin` from
  `FormalConjectures/WrittenOnTheWallII/GraphConjecture145.lean` (line 61), each under the
  section variables of its file. They are copied term for term, with three changes: they live
  in this file's namespace (upstream `SimpleGraph` and `WrittenOnTheWallII.GraphConjecture145`),
  so that they cannot clash with other modules; the generalized field notation
  `G.IsTotalDominating D` and `G.IsTotalNDominatingSet n D` of the namespace `SimpleGraph` is
  therefore written `IsTotalDominating G D` and `IsTotalNDominatingSet (G := G) n D`; and
  `localIndependenceMin` assumes `[Nonempty α]` instead of `[Nontrivial α]`, which its body
  does not need (it uses `Finset.univ_nonempty`).
* `localIndependenceMinFreq`, the frequency, is ours: the number of vertices `v` with
  `indepNeighborsCard G v = localIndependenceMin G`.
* `statement` has the binders and hypotheses of `conjecture309Statement` in
  `FormalConjectures/WrittenOnTheWallII/GraphConjecture309.lean` (another WOWII upper bound for
  `γ_t`): every vertex type `V : Type` with `[Fintype V] [DecidableEq V] [Nonempty V]`, every
  `G : SimpleGraph V` with `[DecidableRel G.Adj]`, `G.Connected` and `2 < Fintype.card V`. The
  conclusion is the real inequality
  `(totalDominationNumber G : ℝ) ≤ (1 / 2) * ((Fintype.card V : ℝ) + (localIndependenceMinFreq Gᶜ : ℝ))`.
  The conclusion does not use the binders `[DecidableEq V]` and `[DecidableRel G.Adj]`; they
  exclude no graph.

## The family

`family t` lives on `Fin 3 × Fin (t + 4)`. The vertices `(0, i)` are the *hubs*: `(0, 0)`, …,
`(0, 3)` form a `K₄`, and the `t` hubs `(0, 4)`, …, `(0, t + 3)` are pendant vertices at
`(0, 0)`. Each hub `(0, i)` carries a path `(0, i) - (1, i) - (2, i)` with *middle* vertex
`(1, i)` and *leaf* `(2, i)`. So `family t` is the 2-corona of `K₄` with `t` pendant vertices at
one vertex, and `n = 3 (t + 4)`. With the label `5 l + i` for the vertex `(l, i)`, `family 1`
is the 15-vertex graph of the README (`counterexample_adj_iff`).

* `family_connected`: every vertex is joined to `(0, 0)`.
* `totalDominationNumber_family : γ_t = 2 (t + 4)`. The hubs and the middles form a total
  dominating set. Conversely, the only neighbour of a leaf is its middle, and the neighbours of a
  middle are its hub and its leaf, so a total dominating set meets every column
  `{(0, i), (1, i), (2, i)}` in at least two vertices.
* `indepNeighborsCard_compl_family_hub : λ_Ḡ(0, i) = 2` for `i < 4`. In `Ḡ` the neighbours of
  `v` are the vertices outside the closed neighbourhood `N_G[v]`, and an independent set of `Ḡ`
  is a clique of `G`. Outside `N_G[(0, i)]` no two hubs are adjacent, so every edge of `G` there
  joins a middle to a hub or a leaf: colouring the middles `1` and the other vertices `0`
  shows that the cliques have at most two vertices. A middle and its leaf form one.
* `three_le_indepNeighborsCard_compl_family`: every other vertex `v` has `λ_Ḡ(v) ≥ 3`, because
  three of the four hubs of the `K₄` lie outside `N_G[v]`.
* Hence `λ_min(Ḡ) = 2` with frequency 4 (`localIndependenceMin_compl_family`,
  `localIndependenceMinFreq_compl_family`), and `2 γ_t = 4 (t + 4) = n + 4 + t`.
* `family_violates_ceil`: for `t ≥ 2` the violation is at least `1`, so the bound fails even
  when it is rounded up.

For the 15-vertex graph, `indepNeighborsCard_compl_counterexample` also gives every value of
`λ_Ḡ` (2 at the four hubs of the `K₄`, 3 at five vertices, 4 at six). Its certificates, cliques
of `G` outside `N_G[v]` and colourings of `G - N_G[v]`, are checked by `decide +kernel`
independently of the general argument.

## The 12-vertex graph

`graph12` on `Fin 12` has the 13 edges of `edges12`: the triangles `{8, 9, 11}` and
`{4, 5, 10}`, the path `11 - 3 - 10` between them, the leaf `0` at `11`, and the paths
`8 - 6 - 1` and `9 - 7 - 2`.

* `totalDominationNumber_graph12 : γ_t = 7`. The set `{4, 6, 7, 8, 9, 10, 11}` is total
  dominating. Conversely a total dominating set contains `11`, `6` and `7` (the neighbours of the
  leaves `0`, `1`, `2`), a neighbour of `6`, which is `1` or `8`, a neighbour of `7`, which is `2`
  or `9`, a neighbour `w` of `5`, which is `4` or `10`, and a neighbour of `w`, which lies in
  `{3, 4, 5, 10}`; these seven vertices are distinct.
* `indepNeighborsCard_compl_graph12 : λ_Ḡ(v) = lam12 v`, which is `2` at `v = 3` and `3`
  elsewhere: the closed neighbourhood `{3, 10, 11}` of `3` meets both triangles, and every other
  closed neighbourhood misses one of them. The certificates are an edge or a triangle of `G`
  outside `N_G[v]`, a 2-colouring of the forest `G - N_G[3]` and a proper 3-colouring of `G`.
* So `λ_min(Ḡ) = 2` with frequency 1, and `γ_t = 7 > (12 + 1) / 2`.
-/

namespace AgenticConjectures.WowiiGraphConjecture300

open SimpleGraph

section Domination

variable {α : Type*} {G : SimpleGraph α} [Fintype α] [DecidableEq α]

/-- Upstream definition, verbatim (modulo namespace).

A set `D` is a total dominating set if every vertex is adjacent to a vertex
in `D`. -/
def IsTotalDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

/-- Upstream definition, verbatim (modulo namespace, which turns `G.IsTotalDominating D` into
`IsTotalDominating G D`).

An `n`-total dominating set is a total dominating set with `n` vertices. -/
@[mk_iff]
structure IsTotalNDominatingSet (n : ℕ) (D : Finset α) : Prop where
  isTotalDominating : IsTotalDominating G D
  card_eq : D.card = n

/-- Upstream definition, verbatim (modulo namespace, which turns `G.IsTotalNDominatingSet n D`
into `IsTotalNDominatingSet (G := G) n D`).

The total domination number of `G`. -/
noncomputable def totalDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, IsTotalNDominatingSet (G := G) n D}

end Domination

section Independence

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Upstream definition, verbatim (modulo namespace).

Independence number of the neighbourhood of `v`. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

end Independence

section LocalIndependence

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Upstream definition, verbatim (modulo namespace), under `[Nonempty α]` instead of
`[Nontrivial α]`.

`localIndependenceMin G` is the minimum over all vertices of the local independence
number `indepNeighborsCard G v`. This equals $\mathrm{lMin}$ from DeLaVina's notation. -/
noncomputable def localIndependenceMin (G : SimpleGraph α) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (indepNeighborsCard G)

/-- Not upstream. The frequency of `localIndependenceMin G`: the number of vertices `v` with
`indepNeighborsCard G v = localIndependenceMin G`. -/
noncomputable def localIndependenceMinFreq (G : SimpleGraph α) : ℕ :=
  (Finset.univ.filter fun v => indepNeighborsCard G v = localIndependenceMin G).card

end LocalIndependence

/-- WOWII Conjecture 300: every finite simple connected graph `G` on more than two vertices
satisfies `γ_t(G) ≤ (n(G) + f) / 2` in `ℝ`, where `f` is the number of vertices at which the
local independence number in the complement `Gᶜ` attains its minimum. -/
def statement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 2 < Fintype.card V →
    (totalDominationNumber G : ℝ) ≤
      (1 / 2) * ((Fintype.card V : ℝ) + (localIndependenceMinFreq Gᶜ : ℝ))

section Local

variable {α : Type*} {G : SimpleGraph α}

/-- A set of pairwise non-adjacent neighbours of `u` has at most `indepNeighborsCard G u`
elements. -/
theorem card_le_indepNeighborsCard [Fintype α] (u : α) (S : Finset α)
    (hS : ∀ x ∈ S, G.Adj u x) (hind : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ G.Adj x y) :
    S.card ≤ indepNeighborsCard G u := by
  classical
  let T : Finset (G.neighborSet u) := S.subtype (· ∈ G.neighborSet u)
  have hT : T.card = S.card := by
    simp only [T, Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem hS
  rw [← hT]
  apply IsIndepSet.card_le_indepNum
  intro a ha b hb hab
  simp only [T, Finset.mem_coe, Finset.mem_subtype] at ha hb
  exact hind a ha b hb (fun h => hab (Subtype.ext h))

/-- A colouring `c` of the neighbours of `u` with fewer than `k` colours, in which any two
distinct neighbours of `u` with the same colour are adjacent, shows
`indepNeighborsCard G u ≤ k`. -/
theorem indepNeighborsCard_le (u : α) (k : ℕ) (c : α → ℕ) (hck : ∀ x, G.Adj u x → c x < k)
    (hc : ∀ x y, G.Adj u x → G.Adj u y → x ≠ y → c x = c y → G.Adj x y) :
    indepNeighborsCard G u ≤ k := by
  unfold indepNeighborsCard indepNum
  apply csSup_le'
  rintro n ⟨s, hs, rfl⟩
  calc s.card ≤ (Finset.range k).card := by
        refine Finset.card_le_card_of_injOn (fun x => c x.1) ?_ ?_
        · intro x _
          exact Finset.mem_coe.mpr (Finset.mem_range.mpr (hck x.1 x.2))
        · intro x hx y hy hxy
          by_contra hne
          exact hs hx hy hne (hc x.1 y.1 x.2 y.2 (fun h => hne (Subtype.ext h)) hxy)
    _ = k := Finset.card_range k

end Local

section Family

/-- The 2-corona of `K₄` with `t` pendant vertices at one vertex. The hubs `(0, i)`: `(0, 0)`,
…, `(0, 3)` form a `K₄` and `(0, 4)`, …, `(0, t + 3)` are pendant vertices at `(0, 0)`. Every
hub `(0, i)` carries the path `(0, i) - (1, i) - (2, i)`. -/
def family (t : ℕ) : SimpleGraph (Fin 3 × Fin (t + 4)) where
  Adj v w :=
    (v.1.val = 0 ∧ w.1.val = 0 ∧ v.2.val ≠ w.2.val ∧
        ((v.2.val < 4 ∧ w.2.val < 4) ∨ v.2.val = 0 ∨ w.2.val = 0)) ∨
      (v.2.val = w.2.val ∧ (v.1.val + 1 = w.1.val ∨ w.1.val + 1 = v.1.val))
  symm _ _ h := by omega
  loopless := ⟨fun _ h => by omega⟩

theorem family_adj {t : ℕ} {v w : Fin 3 × Fin (t + 4)} :
    (family t).Adj v w ↔
      (v.1.val = 0 ∧ w.1.val = 0 ∧ v.2.val ≠ w.2.val ∧
          ((v.2.val < 4 ∧ w.2.val < 4) ∨ v.2.val = 0 ∨ w.2.val = 0)) ∨
        (v.2.val = w.2.val ∧ (v.1.val + 1 = w.1.val ∨ w.1.val + 1 = v.1.val)) :=
  Iff.rfl

instance (t : ℕ) : DecidableRel (family t).Adj := fun _ _ =>
  decidable_of_iff' _ family_adj

theorem vertex_eq_iff {t : ℕ} {v w : Fin 3 × Fin (t + 4)} :
    v = w ↔ v.1.val = w.1.val ∧ v.2.val = w.2.val := by
  rw [Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]

theorem family_connected (t : ℕ) : (family t).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨(0, 0), fun ⟨l, i⟩ => ?_⟩
  have h0 : (family t).Reachable (0, 0) (0, i) := by
    by_cases hi : i.val = 0
    · rw [show i = 0 from Fin.ext hi]
    · exact Adj.reachable (family_adj.mpr (Or.inl ⟨rfl, rfl, by simp; omega, by simp⟩))
  have h1 : (family t).Reachable (0, 0) (1, i) :=
    h0.trans (Adj.reachable (family_adj.mpr (Or.inr ⟨rfl, Or.inl rfl⟩)))
  have h2 : (family t).Reachable (0, 0) (2, i) :=
    h1.trans (Adj.reachable (family_adj.mpr (Or.inr ⟨rfl, Or.inl rfl⟩)))
  fin_cases l
  · exact h0
  · exact h1
  · exact h2

theorem card_family (t : ℕ) : Fintype.card (Fin 3 × Fin (t + 4)) = 3 * (t + 4) := by
  simp

/-- The hubs and the middles. -/
def hubsAndMiddles (t : ℕ) : Finset (Fin 3 × Fin (t + 4)) :=
  ({0, 1} : Finset (Fin 3)) ×ˢ Finset.univ

theorem card_hubsAndMiddles (t : ℕ) : (hubsAndMiddles t).card = 2 * (t + 4) := by
  simp [hubsAndMiddles, Finset.card_product]

theorem isTotalDominating_hubsAndMiddles (t : ℕ) :
    IsTotalDominating (family t) (hubsAndMiddles t : Set (Fin 3 × Fin (t + 4))) := by
  rintro ⟨l, i⟩
  fin_cases l
  · exact ⟨(1, i), by simp [hubsAndMiddles], family_adj.mpr (Or.inr ⟨rfl, Or.inl rfl⟩)⟩
  · exact ⟨(0, i), by simp [hubsAndMiddles], family_adj.mpr (Or.inr ⟨rfl, Or.inr rfl⟩)⟩
  · exact ⟨(1, i), by simp [hubsAndMiddles], family_adj.mpr (Or.inr ⟨rfl, Or.inr rfl⟩)⟩

/-- A total dominating set meets every column `{(0, i), (1, i), (2, i)}` in two vertices: the
middle `(1, i)`, which is the only neighbour of the leaf `(2, i)`, and a neighbour of the middle,
which is `(0, i)` or `(2, i)`. -/
theorem le_card_of_isTotalDominating {t : ℕ} {D : Finset (Fin 3 × Fin (t + 4))}
    (hD : IsTotalDominating (family t) (D : Set (Fin 3 × Fin (t + 4)))) :
    2 * (t + 4) ≤ D.card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  calc 2 * (t + 4) = ∑ _i : Fin (t + 4), 2 := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun i _ => ?_
  obtain ⟨w, hw, hadj⟩ := hD (2, i)
  obtain ⟨u, hu, hadj'⟩ := hD (1, i)
  have hw1 : w = (1, i) := by
    rw [family_adj] at hadj
    rw [vertex_eq_iff]
    simp at hadj ⊢
    omega
  have hu1 : u.2 = i ∧ u ≠ (1, i) := by
    refine ⟨?_, hadj'.ne.symm⟩
    rw [family_adj] at hadj'
    rw [Fin.ext_iff]
    simp at hadj'
    omega
  subst hw1
  exact Finset.one_lt_card.mpr ⟨(1, i), Finset.mem_filter.mpr ⟨hw, rfl⟩, u,
    Finset.mem_filter.mpr ⟨hu, hu1.1⟩, hu1.2.symm⟩

theorem totalDominationNumber_family (t : ℕ) : totalDominationNumber (family t) = 2 * (t + 4) := by
  have hmem : 2 * (t + 4) ∈ {n | ∃ D : Finset (Fin 3 × Fin (t + 4)),
      IsTotalNDominatingSet (G := family t) n D} :=
    ⟨hubsAndMiddles t, isTotalDominating_hubsAndMiddles t, card_hubsAndMiddles t⟩
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ ?_)
  rintro n ⟨D, hD, rfl⟩
  exact le_card_of_isTotalDominating hD

/-- At a hub `(0, i)` of the `K₄`, the local independence number in the complement is `2`. -/
theorem indepNeighborsCard_compl_family_hub {t : ℕ} (v : Fin 3 × Fin (t + 4))
    (hv : v.1.val = 0 ∧ v.2.val < 4) : indepNeighborsCard (family t)ᶜ v = 2 := by
  apply le_antisymm
  · apply indepNeighborsCard_le v 2 (fun x => if x.1.val = 1 then 1 else 0)
    · intro x _
      split_ifs <;> omega
    · intro x y hx hy hxy hc
      rw [compl_adj] at hx hy ⊢
      refine ⟨hxy, fun h => ?_⟩
      simp only [ne_eq, vertex_eq_iff, family_adj] at hx hy hxy h
      have := x.1.isLt
      have := y.1.isLt
      split_ifs at hc <;> omega
  · let j : Fin (t + 4) := ⟨if v.2.val = 0 then 1 else 0, by split_ifs <;> omega⟩
    have hj : j.val ≠ v.2.val := by simp only [j]; split_ifs <;> omega
    have hne : ((1, j) : Fin 3 × Fin (t + 4)) ≠ (2, j) := by simp
    rw [← Finset.card_pair hne]
    apply card_le_indepNeighborsCard
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [compl_adj, vertex_eq_iff, family_adj] <;> omega
    · intro x hx y hy hxy
      rw [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rw [compl_adj, not_and, not_not]
      intro _
      rw [family_adj]
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp at hxy ⊢

/-- If every hub `(0, a)` of the `K₄` with `a ≠ b` is a neighbour of `v` in the complement,
then `λ_Ḡ(v) ≥ 3`: at least three such hubs exist, and they are pairwise adjacent in `G`. -/
theorem three_le_of_hubs {t : ℕ} (v : Fin 3 × Fin (t + 4)) (b : ℕ)
    (hv : ∀ x : Fin 3 × Fin (t + 4), x.1.val = 0 → x.2.val < 4 → x.2.val ≠ b →
      (family t)ᶜ.Adj v x) :
    3 ≤ indepNeighborsCard (family t)ᶜ v := by
  let S := Finset.univ.filter fun x : Fin 3 × Fin (t + 4) =>
    x.1.val = 0 ∧ x.2.val < 4 ∧ x.2.val ≠ b
  have h3 : 2 < S.card := by
    rw [Finset.two_lt_card]
    refine ⟨(0, ⟨(b + 1) % 4, by omega⟩), ?_, (0, ⟨(b + 2) % 4, by omega⟩), ?_,
      (0, ⟨(b + 3) % 4, by omega⟩), ?_, ?_, ?_, ?_⟩ <;>
      simp [S] <;> omega
  refine h3.trans_le (card_le_indepNeighborsCard v S ?_ ?_)
  · intro x hx
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hv x hx.1 hx.2.1 hx.2.2
  · intro x hx y hy hxy
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    rw [compl_adj, not_and, not_not]
    intro _
    simp only [ne_eq, vertex_eq_iff] at hxy
    rw [family_adj]
    omega

/-- Every vertex other than the four hubs of the `K₄` has `λ_Ḡ(v) ≥ 3`. -/
theorem three_le_indepNeighborsCard_compl_family {t : ℕ} (v : Fin 3 × Fin (t + 4))
    (hv : ¬ (v.1.val = 0 ∧ v.2.val < 4)) : 3 ≤ indepNeighborsCard (family t)ᶜ v := by
  have := v.1.isLt
  by_cases hm : v.1.val = 1 ∧ v.2.val < 4
  · refine three_le_of_hubs v v.2.val fun x hx0 hx4 hxb => ?_
    simp only [compl_adj, ne_eq, vertex_eq_iff, family_adj]
    omega
  · refine three_le_of_hubs v 0 fun x hx0 hx4 hxb => ?_
    simp only [compl_adj, ne_eq, vertex_eq_iff, family_adj]
    omega

theorem two_le_indepNeighborsCard_compl_family {t : ℕ} (v : Fin 3 × Fin (t + 4)) :
    2 ≤ indepNeighborsCard (family t)ᶜ v := by
  by_cases hv : v.1.val = 0 ∧ v.2.val < 4
  · exact (indepNeighborsCard_compl_family_hub v hv).ge
  · exact (three_le_indepNeighborsCard_compl_family v hv).trans' (by norm_num)

theorem localIndependenceMin_compl_family (t : ℕ) : localIndependenceMin (family t)ᶜ = 2 :=
  le_antisymm
    ((Finset.inf'_le _ (Finset.mem_univ (0, 0))).trans
      (indepNeighborsCard_compl_family_hub (t := t) (0, 0) ⟨rfl, by simp⟩).le)
    (Finset.le_inf' _ _ fun v _ => two_le_indepNeighborsCard_compl_family v)

theorem localIndependenceMinFreq_compl_family (t : ℕ) :
    localIndependenceMinFreq (family t)ᶜ = 4 := by
  unfold localIndependenceMinFreq
  rw [localIndependenceMin_compl_family]
  have hfilter : (Finset.univ.filter fun v => indepNeighborsCard (family t)ᶜ v = 2) =
      Finset.univ.filter fun v : Fin 3 × Fin (t + 4) => v.1.val = 0 ∧ v.2.val < 4 := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => ?_, indepNeighborsCard_compl_family_hub v⟩
    by_contra hv
    have := three_le_indepNeighborsCard_compl_family v hv
    omega
  rw [hfilter]
  refine Finset.card_nbij' (fun v => (⟨v.2.val % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4))
    (fun i => (0, ⟨i.val, by omega⟩)) ?_ ?_ ?_ ?_ |>.trans (Finset.card_fin 4)
  · intro v _
    simp
  · intro i _
    simp
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
    rw [vertex_eq_iff]
    simp
    omega
  · intro i _
    ext
    simp

/-- `2 γ_t(G_t) = n(G_t) + f + t`, where `f` is the frequency of `λ_min` in the complement. -/
theorem family_gap (t : ℕ) :
    2 * totalDominationNumber (family t) =
      Fintype.card (Fin 3 × Fin (t + 4)) + localIndependenceMinFreq (family t)ᶜ + t := by
  rw [totalDominationNumber_family, card_family, localIndependenceMinFreq_compl_family]
  ring

/-- For every `t ≥ 1`, `family t` violates the bound of Conjecture 300 (by `t / 2`). -/
theorem family_violates {t : ℕ} (ht : 1 ≤ t) :
    (1 / 2 : ℝ) * ((Fintype.card (Fin 3 × Fin (t + 4)) : ℝ) +
        (localIndependenceMinFreq (family t)ᶜ : ℝ)) <
      (totalDominationNumber (family t) : ℝ) := by
  rw [totalDominationNumber_family, card_family, localIndependenceMinFreq_compl_family]
  have : (1 : ℝ) ≤ t := by exact_mod_cast ht
  push_cast
  linarith

/-- For every `t ≥ 2` the violation is at least `1`, so it survives rounding the bound up:
`⌈(n + f) / 2⌉ < γ_t`. -/
theorem family_violates_ceil {t : ℕ} (ht : 2 ≤ t) :
    ⌈(1 / 2 : ℝ) * ((Fintype.card (Fin 3 × Fin (t + 4)) : ℝ) +
        (localIndependenceMinFreq (family t)ᶜ : ℝ))⌉ <
      (totalDominationNumber (family t) : ℤ) := by
  rw [totalDominationNumber_family, card_family, localIndependenceMinFreq_compl_family,
    Int.ceil_lt_iff]
  have : (2 : ℝ) ≤ t := by exact_mod_cast ht
  push_cast
  linarith

end Family

section Counterexample

/-- The edge list of the README; the vertex `(l, i)` of `family 1` has the label `5 l + i`. -/
def readmeEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 6), (2, 3), (2, 7), (3, 8),
    (4, 9), (5, 10), (6, 11), (7, 12), (8, 13), (9, 14)]

/-- `family 1` is the 15-vertex graph of the README. -/
theorem counterexample_adj_iff : ∀ v w : Fin 3 × Fin (1 + 4),
    (family 1).Adj v w ↔
      (5 * v.1.val + v.2.val, 5 * w.1.val + w.2.val) ∈ readmeEdges ∨
        (5 * w.1.val + w.2.val, 5 * v.1.val + v.2.val) ∈ readmeEdges := by
  decide +kernel

theorem counterexample_connected : (family 1).Connected := family_connected 1

theorem card_counterexample : Fintype.card (Fin 3 × Fin (1 + 4)) = 15 := card_family 1

theorem totalDominationNumber_counterexample : totalDominationNumber (family 1) = 10 :=
  totalDominationNumber_family 1

theorem localIndependenceMin_compl_counterexample : localIndependenceMin (family 1)ᶜ = 2 :=
  localIndependenceMin_compl_family 1

theorem localIndependenceMinFreq_compl_counterexample :
    localIndependenceMinFreq (family 1)ᶜ = 4 :=
  localIndependenceMinFreq_compl_family 1

/-- The values of `λ_Ḡ` on `family 1`, by the label `5 l + i` of the vertex `(l, i)`: `2` at the
hubs `0, …, 3` of the `K₄`, `3` at `4, …, 8`, and `4` at `9, …, 14`. -/
def lam15 (v : Fin 3 × Fin (1 + 4)) : ℕ :=
  if 5 * v.1.val + v.2.val < 4 then 2 else if 5 * v.1.val + v.2.val < 9 then 3 else 4

/-- Lower-bound certificates: pairwise adjacent vertices of `G` outside `N_G[v]`. Two vertices
`(1, j), (2, j)` of another column at a hub of the `K₄`; otherwise the hubs of the `K₄` other
than the one in `N_G[v]`, if any. -/
def wit15 (v : Fin 3 × Fin (1 + 4)) : Finset (Fin 3 × Fin (1 + 4)) :=
  if lam15 v = 2 then
    Finset.univ.filter fun x => x.1.val ≠ 0 ∧ x.2.val = if v.2.val = 0 then 1 else 0
  else
    let b := if lam15 v = 3 then (if v.1.val = 1 then v.2.val else 0) else 4
    Finset.univ.filter fun x => x.1.val = 0 ∧ x.2.val < 4 ∧ x.2.val ≠ b

/-- Upper-bound certificates: colourings of `G - N_G[v]` with `lam15 v` colours that are proper
for `G`, so that every clique of `G` outside `N_G[v]` has at most `lam15 v` vertices. -/
def col15 (v x : Fin 3 × Fin (1 + 4)) : ℕ :=
  if lam15 v = 2 then (if x.1.val = 1 then 1 else 0)
  else if lam15 v = 3 then
    let b := if v.1.val = 1 then v.2.val else 0
    let r := if x.2.val < b then x.2.val else x.2.val - 1
    if x.2.val = 4 then (if x.1.val = 0 then 1 else if x.1.val = 1 then 2 else 0)
    else if x.1.val = 1 then (r + 1) % 3 else r
  else
    let c := if x.2.val = 4 then 1 else x.2.val
    if x.1.val = 1 then (c + 1) % 4 else c

theorem wit15_spec : ∀ v : Fin 3 × Fin (1 + 4), lam15 v ≤ (wit15 v).card ∧
    (∀ x ∈ wit15 v, (family 1)ᶜ.Adj v x) ∧
    (∀ x ∈ wit15 v, ∀ y ∈ wit15 v, x ≠ y → ¬ (family 1)ᶜ.Adj x y) := by
  decide +kernel

theorem col15_lt : ∀ v x : Fin 3 × Fin (1 + 4), (family 1)ᶜ.Adj v x → col15 v x < lam15 v := by
  decide +kernel

theorem col15_spec : ∀ v x y : Fin 3 × Fin (1 + 4), (family 1)ᶜ.Adj v x →
    (family 1)ᶜ.Adj v y → x ≠ y → col15 v x = col15 v y → (family 1)ᶜ.Adj x y := by
  decide +kernel

/-- Every value of `λ_Ḡ` on the 15-vertex graph. -/
theorem indepNeighborsCard_compl_counterexample (v : Fin 3 × Fin (1 + 4)) :
    indepNeighborsCard (family 1)ᶜ v = lam15 v :=
  le_antisymm (indepNeighborsCard_le v _ (col15 v) (col15_lt v) (col15_spec v))
    ((wit15_spec v).1.trans
      (card_le_indepNeighborsCard v _ (wit15_spec v).2.1 (wit15_spec v).2.2))

end Counterexample

section Graph12

/-- The edges of a counterexample on 12 vertices: the triangles `{8, 9, 11}` and `{4, 5, 10}`,
the path `11 - 3 - 10` between them, the leaf `0` at `11`, and the paths `8 - 6 - 1` and
`9 - 7 - 2`. -/
def edges12 : List (ℕ × ℕ) :=
  [(4, 5), (1, 6), (2, 7), (6, 8), (7, 9), (8, 9), (3, 10), (4, 10), (5, 10), (0, 11), (3, 11),
    (8, 11), (9, 11)]

/-- The graph with the edges `edges12` (graph6 `K??I@?A?WwQE`). -/
def graph12 : SimpleGraph (Fin 12) where
  Adj v w := (v.val, w.val) ∈ edges12 ∨ (w.val, v.val) ∈ edges12
  symm _ _ h := h.symm
  loopless := ⟨by decide⟩

instance : DecidableRel graph12.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem graph12_connected : graph12.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨11, fun v => ?_⟩
  have e : ∀ {a b : Fin 12}, graph12.Adj a b → graph12.Reachable 11 a →
      graph12.Reachable 11 b := fun h ha => ha.trans h.reachable
  have r11 : graph12.Reachable 11 11 := Reachable.refl _
  have r0 := e (by decide : graph12.Adj 11 0) r11
  have r3 := e (by decide : graph12.Adj 11 3) r11
  have r8 := e (by decide : graph12.Adj 11 8) r11
  have r9 := e (by decide : graph12.Adj 11 9) r11
  have r10 := e (by decide : graph12.Adj 3 10) r3
  have r6 := e (by decide : graph12.Adj 8 6) r8
  have r7 := e (by decide : graph12.Adj 9 7) r9
  have r4 := e (by decide : graph12.Adj 10 4) r10
  have r5 := e (by decide : graph12.Adj 10 5) r10
  have r1 := e (by decide : graph12.Adj 6 1) r6
  have r2 := e (by decide : graph12.Adj 7 2) r7
  fin_cases v <;> assumption

theorem card_graph12 : Fintype.card (Fin 12) = 12 := Fintype.card_fin 12

/-- A total dominating set of `graph12` with 7 vertices. -/
def tds12 : Finset (Fin 12) := {4, 6, 7, 8, 9, 10, 11}

theorem isTotalDominating_tds12 : IsTotalDominating graph12 (tds12 : Set (Fin 12)) := by
  have h : ∀ v : Fin 12, ∃ w ∈ tds12, graph12.Adj v w := by decide +kernel
  intro v
  obtain ⟨w, hw, hvw⟩ := h v
  exact ⟨w, Finset.mem_coe.mpr hw, hvw⟩

/-- A total dominating set contains the neighbours `11`, `6`, `7` of the leaves `0`, `1`, `2`, a
neighbour of `6` (`1` or `8`), a neighbour of `7` (`2` or `9`), a neighbour `w` of `5` (`4` or
`10`) and a neighbour of `w` (in `{3, 4, 5, 10}`); these seven vertices are distinct. -/
theorem le_card_of_isTotalDominating_graph12 {D : Finset (Fin 12)}
    (hD : IsTotalDominating graph12 (D : Set (Fin 12))) : 7 ≤ D.card := by
  have leaf : ∀ u w : Fin 12, u.val < 3 → graph12.Adj u w → w = [11, 6, 7].getD u.val 0 := by
    decide +kernel
  have key : ∀ d e f g : Fin 12, graph12.Adj 6 d → graph12.Adj 7 e → graph12.Adj 5 f →
      graph12.Adj f g → ({11, 6, 7, d, e, f, g} : Finset (Fin 12)).card = 7 := by
    decide +kernel
  obtain ⟨a, ha, h0⟩ := hD 0
  obtain ⟨b, hb, h1⟩ := hD 1
  obtain ⟨c, hc, h2⟩ := hD 2
  obtain ⟨d, hd, h6⟩ := hD 6
  obtain ⟨e, he, h7⟩ := hD 7
  obtain ⟨f, hf, h5⟩ := hD 5
  obtain ⟨g, hg, hfg⟩ := hD f
  obtain rfl := leaf 0 a (by decide) h0
  obtain rfl := leaf 1 b (by decide) h1
  obtain rfl := leaf 2 c (by decide) h2
  rw [← key d e f g h6 h7 h5 hfg]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem totalDominationNumber_graph12 : totalDominationNumber graph12 = 7 := by
  have hmem : 7 ∈ {n | ∃ D : Finset (Fin 12), IsTotalNDominatingSet (G := graph12) n D} :=
    ⟨tds12, isTotalDominating_tds12, by decide⟩
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ ?_)
  rintro n ⟨D, hD, rfl⟩
  exact le_card_of_isTotalDominating_graph12 hD

/-- The values of `λ_Ḡ` on `graph12`: `2` at the vertex `3`, whose closed neighbourhood
`{3, 10, 11}` meets both triangles, and `3` elsewhere. -/
def lam12 (v : Fin 12) : ℕ := if v = 3 then 2 else 3

/-- Lower-bound certificates: the edge `{8, 9}` outside `N_G[3]`, and otherwise a triangle
outside `N_G[v]`. -/
def wit12 (v : Fin 12) : Finset (Fin 12) :=
  if v = 3 then {8, 9}
  else if v ∈ ({0, 6, 7, 8, 9, 11} : Finset (Fin 12)) then {4, 5, 10} else {8, 9, 11}

/-- Upper-bound certificates: a 2-colouring of `G - N_G[3]` (a forest), and a proper
3-colouring of `G`. -/
def col12 (v x : Fin 12) : ℕ :=
  if v = 3 then [0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0].getD x.val 0
  else [1, 1, 1, 1, 1, 2, 0, 0, 1, 2, 0, 0].getD x.val 0

theorem wit12_spec : ∀ v : Fin 12, lam12 v ≤ (wit12 v).card ∧
    (∀ x ∈ wit12 v, graph12ᶜ.Adj v x) ∧
    (∀ x ∈ wit12 v, ∀ y ∈ wit12 v, x ≠ y → ¬ graph12ᶜ.Adj x y) := by
  decide +kernel

theorem col12_lt : ∀ v x : Fin 12, graph12ᶜ.Adj v x → col12 v x < lam12 v := by
  decide +kernel

theorem col12_spec : ∀ v x y : Fin 12, graph12ᶜ.Adj v x → graph12ᶜ.Adj v y → x ≠ y →
    col12 v x = col12 v y → graph12ᶜ.Adj x y := by
  decide +kernel

/-- Every value of `λ_Ḡ` on `graph12`. -/
theorem indepNeighborsCard_compl_graph12 (v : Fin 12) :
    indepNeighborsCard graph12ᶜ v = lam12 v :=
  le_antisymm (indepNeighborsCard_le v _ (col12 v) (col12_lt v) (col12_spec v))
    ((wit12_spec v).1.trans
      (card_le_indepNeighborsCard v _ (wit12_spec v).2.1 (wit12_spec v).2.2))

theorem localIndependenceMin_compl_graph12 : localIndependenceMin graph12ᶜ = 2 := by
  unfold localIndependenceMin
  rw [show indepNeighborsCard graph12ᶜ = lam12 from funext indepNeighborsCard_compl_graph12]
  decide +kernel

theorem localIndependenceMinFreq_compl_graph12 : localIndependenceMinFreq graph12ᶜ = 1 := by
  unfold localIndependenceMinFreq
  rw [localIndependenceMin_compl_graph12,
    show indepNeighborsCard graph12ᶜ = lam12 from funext indepNeighborsCard_compl_graph12]
  decide +kernel

/-- `graph12` violates the bound of Conjecture 300: `γ_t = 7 > (12 + 1) / 2`. By the
computation in the README no graph on at most 11 vertices does. -/
theorem graph12_violates :
    (1 / 2 : ℝ) * ((Fintype.card (Fin 12) : ℝ) + (localIndependenceMinFreq graph12ᶜ : ℝ)) <
      (totalDominationNumber graph12 : ℝ) := by
  rw [totalDominationNumber_graph12, card_graph12, localIndependenceMinFreq_compl_graph12]
  norm_num

end Graph12

/-- WOWII Conjecture 300 is false: the 15-vertex graph `family 1` has `γ_t = 10`, while
`(n + f) / 2 = (15 + 4) / 2 = 19/2`. -/
theorem not_statement : ¬ statement := fun h =>
  (family_violates le_rfl).not_ge
    (h (Fin 3 × Fin (1 + 4)) (family 1) (family_connected 1) (by rw [card_family]; norm_num))

/-- The same conclusion from the 12-vertex graph `graph12`: `γ_t = 7`, while
`(n + f) / 2 = (12 + 1) / 2 = 13/2`. -/
theorem not_statement_graph12 : ¬ statement := fun h =>
  graph12_violates.not_ge (h (Fin 12) graph12 graph12_connected (by rw [card_graph12]; norm_num))

end AgenticConjectures.WowiiGraphConjecture300
