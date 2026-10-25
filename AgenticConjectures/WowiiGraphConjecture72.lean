import Mathlib

/-!
# Written on the Wall II, Conjecture 72: the Formal Conjectures reading is false

Conjecture 72 of E. DeLaViña's *Written on the Wall II* (Graffiti.pc, dated April 4, 2004,
listed with status `O`) reads:

> If G is a simple connected graph, then tree(G) ≥ CEIL[average of ecc(v) + maximum of λ(v) /3]

Here `tree(G)` is the number of vertices of a largest induced tree, `ecc(v)` is the
eccentricity of `v`, and `λ(v)` is the independence number of the subgraph induced by the
neighbourhood of `v`. The row leaves open whether `/3` divides only the maximum of `λ(v)` or
the whole sum. The formal statement `WrittenOnTheWallII.GraphConjecture72.conjecture72` of
google-deepmind/formal-conjectures at commit `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
(snapshot `problems/wowii-graph-conjecture-72/upstream/GraphConjecture72.lean`) takes the
first reading, `⌈averageEccentricity G + (maxL : ℝ) / 3⌉ ≤ (largestInducedTreeSize G : ℝ)`.

This file shows that this formal statement is false. `refuted : ¬ statement` uses a connected
graph on 28 vertices with average eccentricity `75/14`, maximum `λ` equal to `5`, and largest
induced tree of order `7`, while `⌈75/14 + 5/3⌉ = 8`. The other reading,
`⌈(average of ecc(v) + maximum of λ(v)) / 3⌉ ≤ tree(G)`, is not addressed here.

## Upstream correspondence

* `averageEccentricity`, `largestInducedTreeSize` and `indepNeighborsCard` are copied term for
  term, under the section variables `{α : Type*} [Fintype α] [DecidableEq α]` of their upstream
  files `Eccentricity.lean`, `LargestInducedTree.lean` and `Independence.lean` in
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/`. Upstream they are in namespace
  `SimpleGraph`; here they are in this file's namespace, so that they cannot clash with other
  modules of the library.
* `statement` quantifies the upstream theorem over every vertex type `α : Type u`. Its
  hypotheses `[Fintype α] [DecidableEq α] [Nontrivial α]` and `G.Connected` and its conclusion
  are the upstream text verbatim. Upstream's `α : Type*` is universe polymorphic, and
  `refuted` holds in every universe `u` (the counterexample lives on `ULift (Fin 28)`).
* `problems/wowii-graph-conjecture-72/upstream_statement_check.lean` restates the upstream
  statement over the upstream, `SimpleGraph`-namespaced definitions and refutes it with
  `refuted`.

## Proof

The counterexample (`graph`) lives on any type `V ≃ Fin 28`; the labels are those of
`problems/wowii-graph-conjecture-72/g28.txt`. Each vertex `i` gets a level `lvl i`: the ten
vertices `8, …, 17` have level 0, vertex `0` level 1, vertex `1` level 2, the four vertices
`2, …, 5` level 3, vertex `6` level 4, vertex `7` level 5, and the ten vertices `18, …, 27`
level 6. Two distinct vertices are adjacent when their levels are consecutive, or both are 0,
or both are 6. So levels 0–1 and levels 5–6 are two cliques `K_11`, joined by the path
`0 - 1 - m - 6 - 7`, where `m` runs over the independent set `{2, 3, 4, 5}`.

* `graph_connected`: every vertex other than `1` has a neighbour one level closer to level 2.
* `averageEccentricity_ge`: levels change by at most one along an edge (`lvl_walk`). So a
  vertex `v` is at distance at least `lvl v` from a vertex of level 0 and at least `6 - lvl v`
  from a vertex of level 6 (`ecc_ge`). These bounds sum to 150 (`sum_lvl`), so the average
  eccentricity is at least `150/28 = 75/14`.
* `five_le_indepNeighborsCard`: the neighbours `0, 2, 3, 4, 5` of vertex `1` are pairwise
  non-adjacent, so `λ(1) ≥ 5`.
* `card_le_seven`: an induced tree meets each clique in at most two vertices, because a
  triangle gives two different paths (`not_isAcyclic_of_triangle`). If it contains `1` and
  `6`, it has at most one vertex of level 3, since two would close a 4-cycle
  (`not_isAcyclic_of_square`). If it contains `1` but not `6`, it has no vertex of level at
  least 5; symmetrically, if it contains `6` but not `1`, it has no vertex of level at most 1.
  If it contains neither and has a vertex of level 3, that vertex is all of it. The last three
  facts follow from the connectivity of the tree (`of_preserved`). Each case leaves at most
  seven vertices.
* `tree_lt_ceil`: `tree ≤ 7 < 8 ≤ ⌈75/14 + 5/3⌉ ≤ ⌈averageEccentricity + maxL / 3⌉`.

The bounds are the exact values: the average eccentricity is `75/14`, `max λ = 5`, and the
largest induced tree has 7 vertices. `problems/wowii-graph-conjecture-72/verify_wowii72.py`
recomputes them independently.
-/

namespace AgenticConjectures.WowiiGraphConjecture72

open SimpleGraph

section Definitions

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Upstream definition, verbatim (modulo namespace).

The average eccentricity of a graph `G`: the mean of `G.eccent v` over all vertices,
converted to a real number. Returns 0 if the graph has no vertices. -/
noncomputable def averageEccentricity (G : SimpleGraph α) : ℝ :=
  (∑ v : α, (G.eccent v).toNat) / (Fintype.card α : ℝ)

/-- Upstream definition, verbatim (modulo namespace).

`largestInducedTreeSize G` is the number of vertices in a largest induced subtree of `G`.
A tree is a connected acyclic graph; an induced tree is an induced subgraph that is a tree. -/
noncomputable def largestInducedTreeSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, s.card = n ∧ (G.induce (s : Set α)).IsTree }

/-- Upstream definition, verbatim (modulo namespace).

Independence number of the neighbourhood of `v`. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

end Definitions

section Induce

variable {W : Type*} {G : SimpleGraph W} {s : Set W}

/-- Three pairwise adjacent vertices of `s` give two different paths in `G.induce s`, so the
induced graph is not acyclic. -/
theorem not_isAcyclic_of_triangle {a b c : W} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) : ¬ (G.induce s).IsAcyclic := by
  intro h
  have hAB : (G.induce s).Adj ⟨a, ha⟩ ⟨b, hb⟩ := hab
  have hAC : (G.induce s).Adj ⟨a, ha⟩ ⟨c, hc⟩ := hac
  have hCB : (G.induce s).Adj ⟨c, hc⟩ ⟨b, hb⟩ := hbc.symm
  have hp : (Walk.cons hAC (Walk.cons hCB Walk.nil)).IsPath :=
    (Walk.IsPath.nil.cons (by simp [hbc.ne'])).cons (by simp [hab.ne, hac.ne])
  have h1 := congrArg (fun p : (G.induce s).Path ⟨a, ha⟩ ⟨b, hb⟩ => p.1.length)
    (h.path_unique (Path.singleton hAB) ⟨_, hp⟩)
  simp [Path.singleton] at h1

/-- A 4-cycle `a - b - c - d - a` in `s` gives two different paths from `a` to `c` in
`G.induce s`, so the induced graph is not acyclic. -/
theorem not_isAcyclic_of_square {a b c d : W} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hd : d ∈ s) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : ¬ (G.induce s).IsAcyclic := by
  intro h
  have hAB : (G.induce s).Adj ⟨a, ha⟩ ⟨b, hb⟩ := hab
  have hBC : (G.induce s).Adj ⟨b, hb⟩ ⟨c, hc⟩ := hbc
  have hAD : (G.induce s).Adj ⟨a, ha⟩ ⟨d, hd⟩ := hda.symm
  have hDC : (G.induce s).Adj ⟨d, hd⟩ ⟨c, hc⟩ := hcd.symm
  have hp : (Walk.cons hAB (Walk.cons hBC Walk.nil)).IsPath :=
    (Walk.IsPath.nil.cons (by simp [hbc.ne])).cons (by simp [hab.ne, hac])
  have hq : (Walk.cons hAD (Walk.cons hDC Walk.nil)).IsPath :=
    (Walk.IsPath.nil.cons (by simp [hcd.ne'])).cons (by simp [hda.ne', hac])
  have h1 := congrArg (fun p : (G.induce s).Path ⟨a, ha⟩ ⟨c, hc⟩ => p.1.support)
    (h.path_unique ⟨_, hp⟩ ⟨_, hq⟩)
  simp [hbd] at h1

/-- In a connected induced subgraph, a property that passes along every edge inside `s`
holds at every vertex of `s` once it holds at one of them. -/
theorem of_preserved (hconn : (G.induce s).Connected) (P : W → Prop)
    (hP : ∀ u v, u ∈ s → v ∈ s → G.Adj u v → P u → P v) {a b : W} (ha : a ∈ s)
    (hb : b ∈ s) (hPa : P a) : P b := by
  obtain ⟨p⟩ := hconn.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  suffices ∀ (x y : s) (q : (G.induce s).Walk x y), P x → P y from this _ _ p hPa
  intro x y q
  induction q with
  | nil => exact id
  | cons h q ih => exact fun hx => ih (hP _ _ (Subtype.prop _) (Subtype.prop _) h hx)

end Induce

section Local

variable {α : Type*} [Fintype α] {G : SimpleGraph α}

/-- An independent set of neighbours of `u` has at most `indepNeighborsCard G u`
elements. -/
theorem card_le_indepNeighborsCard (u : α) (S : Finset α) (hS : ∀ x ∈ S, G.Adj u x)
    (hind : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ G.Adj x y) :
    S.card ≤ indepNeighborsCard G u := by
  classical
  let T : Finset (G.neighborSet u) := S.subtype (fun x => x ∈ G.neighborSet u)
  have hT : T.card = S.card := by
    simp only [T, Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem (fun x hx => hS x hx)
  rw [← hT]
  unfold indepNeighborsCard
  apply SimpleGraph.IsIndepSet.card_le_indepNum
  intro a ha b hb hab
  simp only [T, Finset.mem_coe, Finset.mem_subtype] at ha hb
  simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
  exact hind a ha b hb (fun h => hab (Subtype.ext h))

end Local

section Counterexample

/-- The level of each vertex of the counterexample, with the vertex labels of
`problems/wowii-graph-conjecture-72/g28.txt`: the clique vertices `q_i = 8, …, 17` have
level `0`, `p0 = 0` has level `1`, `p1 = 1` level `2`, `m_i = 2, …, 5` level `3`,
`p3 = 6` level `4`, `p4 = 7` level `5`, and the clique vertices `r_i = 18, …, 27`
level `6`. -/
def lvl (i : Fin 28) : ℕ :=
  if i.val = 0 then 1 else if i.val = 1 then 2 else if i.val ≤ 5 then 3 else
  if i.val = 6 then 4 else if i.val = 7 then 5 else if i.val ≤ 17 then 0 else 6

theorem lvl_le_six : ∀ i : Fin 28, lvl i ≤ 6 := by decide

theorem lvl_eq_one : ∀ i : Fin 28, lvl i = 1 → i = 0 := by decide

theorem lvl_eq_two : ∀ i : Fin 28, lvl i = 2 → i = 1 := by decide

theorem lvl_eq_three : ∀ i : Fin 28, lvl i = 3 → i ∈ ({2, 3, 4, 5} : Finset (Fin 28)) := by
  decide

theorem lvl_eq_four : ∀ i : Fin 28, lvl i = 4 → i = 6 := by decide

theorem lvl_eq_five : ∀ i : Fin 28, lvl i = 5 → i = 7 := by decide

/-- A neighbour of `i` one level closer to level `2` (used for `i ≠ 1`). -/
def par (i : Fin 28) : Fin 28 :=
  if lvl i = 0 then 0 else if lvl i = 4 then 2 else if lvl i = 5 then 6 else
  if lvl i = 6 then 7 else 1

/-- The distance from `p1 = 1`, read off the level. -/
def depth (i : Fin 28) : ℕ := if lvl i ≤ 2 then 2 - lvl i else lvl i - 2

theorem par_spec : ∀ i : Fin 28, i ≠ 1 → par i ≠ i ∧ depth (par i) + 1 = depth i ∧
    (lvl (par i) + 1 = lvl i ∨ lvl i + 1 = lvl (par i)) := by decide

theorem depth_eq_zero : ∀ i : Fin 28, depth i = 0 → i = 1 := by decide

theorem sum_lvl : ∑ i : Fin 28, max (lvl i) (6 - lvl i) = 150 := by decide

/-- The counterexample graph on a vertex type `V ≃ Fin 28`: two distinct vertices are
adjacent when their levels are consecutive, or both are `0`, or both are `6`. -/
def graph {V : Type*} (e : V ≃ Fin 28) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (lvl (e u) + 1 = lvl (e v) ∨ lvl (e v) + 1 = lvl (e u) ∨
    (lvl (e u) = 0 ∧ lvl (e v) = 0) ∨ (lvl (e u) = 6 ∧ lvl (e v) = 6))
  symm _ _ h := ⟨h.1.symm, by have := h.2; omega⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {V : Type*} (e : V ≃ Fin 28)

theorem lvl_adj {u v : V} (h : (graph e).Adj u v) :
    lvl (e u) ≤ lvl (e v) + 1 ∧ lvl (e v) ≤ lvl (e u) + 1 := by
  have := h.2
  omega

theorem adj_of_succ {u v : V} (h : lvl (e u) + 1 = lvl (e v)) : (graph e).Adj u v :=
  ⟨fun huv => by subst huv; omega, Or.inl h⟩

theorem lvl_symm (i : Fin 28) : lvl (e (e.symm i)) = lvl i := by
  rw [Equiv.apply_symm_apply]

/-- Levels change by at most one along an edge, hence by at most the length of a walk. -/
theorem lvl_walk {u v : V} (p : (graph e).Walk u v) :
    lvl (e u) ≤ lvl (e v) + p.length ∧ lvl (e v) ≤ lvl (e u) + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have := lvl_adj e h
    rw [Walk.length_cons]
    omega

theorem graph_connected : (graph e).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨e.symm 1, fun v => ?_⟩
  suffices ∀ n, ∀ v : V, depth (e v) = n → (graph e).Reachable (e.symm 1) v from
    this _ v rfl
  intro n
  induction n with
  | zero =>
    intro v hv
    obtain rfl : v = e.symm 1 := e.eq_symm_apply.mpr (depth_eq_zero _ hv)
    exact Reachable.refl _
  | succ n ih =>
    intro v hv
    have hv1 : e v ≠ 1 := by
      intro h
      rw [h] at hv
      have : depth (1 : Fin 28) = 0 := by decide
      omega
    obtain ⟨hne, hd, hl⟩ := par_spec (e v) hv1
    refine (ih (e.symm (par (e v))) (by rw [Equiv.apply_symm_apply]; omega)).trans
      (Adj.reachable ⟨fun h => hne ?_, ?_⟩)
    · have := congrArg e h
      rwa [Equiv.apply_symm_apply] at this
    · rw [Equiv.apply_symm_apply]
      omega

theorem lvl_le_dist (u v : V) :
    lvl (e u) ≤ lvl (e v) + (graph e).dist u v ∧ lvl (e v) ≤ lvl (e u) + (graph e).dist u v := by
  obtain ⟨p, -, hp⟩ := (graph_connected e).exists_path_of_dist u v
  rw [← hp]
  exact lvl_walk e p

theorem ecc_ge (u : V) : max (lvl (e u)) (6 - lvl (e u)) ≤ ((graph e).eccent u).toNat := by
  haveI : Nonempty V := ⟨e.symm 0⟩
  haveI : Finite V := Finite.of_equiv _ e.symm
  have hne : (graph e).eccent u ≠ ⊤ :=
    ne_top_of_le_ne_top (connected_iff_ediam_ne_top.mp (graph_connected e)) eccent_le_ediam
  have key : ∀ w : V, (graph e).dist u w ≤ ((graph e).eccent u).toNat := fun w => by
    rw [← ENat.toNat_coe ((graph e).dist u w),
      ((graph_connected e).preconnected u w).coe_dist_eq_edist]
    exact ENat.toNat_le_toNat edist_le_eccent hne
  have h18 := lvl_symm e 18
  have h8 := lvl_symm e 8
  have l18 : lvl (18 : Fin 28) = 6 := by decide
  have l8 : lvl (8 : Fin 28) = 0 := by decide
  have hu := lvl_le_six (e u)
  have d18 := lvl_le_dist e u (e.symm 18)
  have d8 := lvl_le_dist e u (e.symm 8)
  have k18 := key (e.symm 18)
  have k8 := key (e.symm 8)
  refine max_le ?_ ?_ <;> omega

theorem sum_ecc_ge [Fintype V] : 150 ≤ ∑ v : V, ((graph e).eccent v).toNat := by
  rw [← sum_lvl, ← e.sum_comp (fun i => max (lvl i) (6 - lvl i))]
  exact Finset.sum_le_sum fun v _ => ecc_ge e v

theorem averageEccentricity_ge [Fintype V] [DecidableEq V] :
    (150 / 28 : ℝ) ≤ averageEccentricity (graph e) := by
  have h : (150 : ℝ) ≤ ((∑ v : V, ((graph e).eccent v).toNat : ℕ) : ℝ) := by
    exact_mod_cast sum_ecc_ge e
  rw [averageEccentricity, Fintype.card_congr e, Fintype.card_fin]
  push_cast at h ⊢
  gcongr

theorem five_le_indepNeighborsCard [Fintype V] :
    5 ≤ indepNeighborsCard (graph e) (e.symm 1) := by
  classical
  have hS : ∀ i ∈ ({0, 2, 3, 4, 5} : Finset (Fin 28)), lvl i = 1 ∨ lvl i = 3 := by decide
  have l1 : lvl (e (e.symm 1)) = 2 := by rw [Equiv.apply_symm_apply]; decide
  have h := card_le_indepNeighborsCard (G := graph e) (e.symm 1)
    (({0, 2, 3, 4, 5} : Finset (Fin 28)).map e.symm.toEmbedding) ?_ ?_
  · rwa [Finset.card_map] at h
  · intro x hx
    rw [Finset.mem_map_equiv, Equiv.symm_symm] at hx
    have hx' := hS _ hx
    refine ⟨fun h => ?_, ?_⟩
    · rw [← h] at hx'
      omega
    · omega
  · intro x hx y hy _ hxy
    rw [Finset.mem_map_equiv, Equiv.symm_symm] at hx hy
    have hx' := hS _ hx
    have hy' := hS _ hy
    have := hxy.2
    omega

theorem adj_of_le_one {u v : V} (huv : u ≠ v) (hu : lvl (e u) ≤ 1) (hv : lvl (e v) ≤ 1) :
    (graph e).Adj u v := by
  refine ⟨huv, ?_⟩
  by_cases h : lvl (e u) = 1 ∧ lvl (e v) = 1
  · exact absurd (e.injective ((lvl_eq_one _ h.1).trans (lvl_eq_one _ h.2).symm)) huv
  · omega

theorem adj_of_five_le {u v : V} (huv : u ≠ v) (hu : 5 ≤ lvl (e u)) (hv : 5 ≤ lvl (e v)) :
    (graph e).Adj u v := by
  refine ⟨huv, ?_⟩
  have := lvl_le_six (e u)
  have := lvl_le_six (e v)
  by_cases h : lvl (e u) = 5 ∧ lvl (e v) = 5
  · exact absurd (e.injective ((lvl_eq_five _ h.1).trans (lvl_eq_five _ h.2).symm)) huv
  · omega

/-- Every induced tree of the counterexample has at most seven vertices. -/
theorem card_le_seven {s : Finset V} (hT : ((graph e).induce (s : Set V)).IsTree) :
    s.card ≤ 7 := by
  classical
  have hacyc := hT.isAcyclic
  have hconn := hT.connected
  have l1 : lvl (e (e.symm 1)) = 2 := by rw [Equiv.apply_symm_apply]; decide
  have l6 : lvl (e (e.symm 6)) = 4 := by rw [Equiv.apply_symm_apply]; decide
  set sQ := s.filter (fun v => lvl (e v) ≤ 1) with hsQ
  set s1 := s.filter (fun v => lvl (e v) = 2) with hs1
  set sM := s.filter (fun v => lvl (e v) = 3) with hsM
  set s6 := s.filter (fun v => lvl (e v) = 4) with hs6
  set sR := s.filter (fun v => 5 ≤ lvl (e v)) with hsR
  have htot : s.card ≤ sQ.card + s1.card + sM.card + s6.card + sR.card := by
    have hsub : s ⊆ sQ ∪ s1 ∪ sM ∪ s6 ∪ sR := by
      intro v hv
      have := lvl_le_six (e v)
      simp only [hsQ, hs1, hsM, hs6, hsR, Finset.mem_union, Finset.mem_filter, hv, true_and]
      omega
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (sQ ∪ s1 ∪ sM ∪ s6) sR
    have h3 := Finset.card_union_le (sQ ∪ s1 ∪ sM) s6
    have h4 := Finset.card_union_le (sQ ∪ s1) sM
    have h5 := Finset.card_union_le sQ s1
    omega
  -- A clique meets an induced tree in at most two vertices.
  have hQ : sQ.card ≤ 2 := by
    by_contra hlt
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := (Finset.two_lt_card (s := sQ)).mp (by omega)
    simp only [hsQ, Finset.mem_filter] at ha hb hc
    exact not_isAcyclic_of_triangle (G := graph e) (s := (s : Set V)) ha.1 hb.1 hc.1
      (adj_of_le_one e hab ha.2 hb.2) (adj_of_le_one e hbc hb.2 hc.2)
      (adj_of_le_one e hac ha.2 hc.2) hacyc
  have hR : sR.card ≤ 2 := by
    by_contra hlt
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := (Finset.two_lt_card (s := sR)).mp (by omega)
    simp only [hsR, Finset.mem_filter] at ha hb hc
    exact not_isAcyclic_of_triangle (G := graph e) (s := (s : Set V)) ha.1 hb.1 hc.1
      (adj_of_five_le e hab ha.2 hb.2) (adj_of_five_le e hbc hb.2 hc.2)
      (adj_of_five_le e hac ha.2 hc.2) hacyc
  have hM : sM.card ≤ 4 := by
    have hsub : sM ⊆ ({2, 3, 4, 5} : Finset (Fin 28)).map e.symm.toEmbedding := by
      intro v hv
      simp only [hsM, Finset.mem_filter] at hv
      rw [Finset.mem_map_equiv, Equiv.symm_symm]
      exact lvl_eq_three _ hv.2
    exact (Finset.card_le_card hsub).trans (by rw [Finset.card_map]; decide)
  -- The levels `2` and `4` hold one vertex each, `p1 = e.symm 1` and `p3 = e.symm 6`.
  have h1 : s1.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [hs1, Finset.mem_filter] at ha hb
    exact e.injective ((lvl_eq_two _ ha.2).trans (lvl_eq_two _ hb.2).symm)
  have h6 : s6.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [hs6, Finset.mem_filter] at ha hb
    exact e.injective ((lvl_eq_four _ ha.2).trans (lvl_eq_four _ hb.2).symm)
  have h1' : e.symm 1 ∉ s → s1.card = 0 := by
    intro hn
    rw [Finset.card_eq_zero, hs1, Finset.filter_eq_empty_iff]
    intro v hv hlv
    rw [← e.eq_symm_apply.mpr (lvl_eq_two _ hlv)] at hn
    exact hn hv
  have h6' : e.symm 6 ∉ s → s6.card = 0 := by
    intro hn
    rw [Finset.card_eq_zero, hs6, Finset.filter_eq_empty_iff]
    intro v hv hlv
    rw [← e.eq_symm_apply.mpr (lvl_eq_four _ hlv)] at hn
    exact hn hv
  -- Two vertices of level `3` together with `p1` and `p3` form a 4-cycle.
  have hsq : 2 ≤ sM.card → ¬ (e.symm 1 ∈ s ∧ e.symm 6 ∈ s) := by
    rintro h2 ⟨h1s, h6s⟩
    obtain ⟨a, ha, b, hb, hab⟩ := (Finset.one_lt_card (s := sM)).mp (by omega)
    simp only [hsM, Finset.mem_filter] at ha hb
    exact not_isAcyclic_of_square (G := graph e) (s := (s : Set V)) h1s ha.1 h6s hb.1
      (adj_of_succ e (by omega)) (adj_of_succ e (by omega)) (adj_of_succ e (by omega)).symm
      (adj_of_succ e (by omega)).symm (e.symm.injective.ne (by decide)) hab hacyc
  -- Without `p1` and `p3`, a vertex of level `3` is isolated.
  have hiso : e.symm 1 ∉ s → e.symm 6 ∉ s → 1 ≤ sM.card → s.card ≤ 1 := by
    intro h1s h6s hM1
    obtain ⟨m, hm⟩ := Finset.card_pos.mp (by omega : 0 < sM.card)
    simp only [hsM, Finset.mem_filter] at hm
    have hP : ∀ u v, u ∈ (s : Set V) → v ∈ (s : Set V) → (graph e).Adj u v → u = m → v = m := by
      rintro u v - hv huv rfl
      have := huv.2
      rcases (show lvl (e v) = 2 ∨ lvl (e v) = 4 by omega) with h | h
      · rw [← e.eq_symm_apply.mpr (lvl_eq_two _ h)] at h1s
        exact absurd hv h1s
      · rw [← e.eq_symm_apply.mpr (lvl_eq_four _ h)] at h6s
        exact absurd hv h6s
    have hall : ∀ x ∈ s, x = m := fun x hx => of_preserved hconn _ hP hm.1 hx rfl
    exact Finset.card_le_one.mpr fun a ha b hb => (hall a ha).trans (hall b hb).symm
  -- Without `p3`, nothing of level `≥ 5` is connected to `p1`.
  have hsepR : e.symm 1 ∈ s → e.symm 6 ∉ s → sR.card = 0 := by
    intro h1s h6s
    have hP : ∀ u v, u ∈ (s : Set V) → v ∈ (s : Set V) → (graph e).Adj u v →
        lvl (e u) ≤ 4 → lvl (e v) ≤ 4 := by
      intro u v hu _ huv hlu
      have := lvl_adj e huv
      by_contra hlv
      have hu4 : lvl (e u) = 4 := by omega
      rw [← e.eq_symm_apply.mpr (lvl_eq_four _ hu4)] at h6s
      exact h6s hu
    rw [Finset.card_eq_zero, hsR, Finset.filter_eq_empty_iff]
    intro x hx hlx
    have : lvl (e x) ≤ 4 := of_preserved hconn (fun y => lvl (e y) ≤ 4) hP h1s hx (by omega)
    omega
  -- Without `p1`, nothing of level `≤ 1` is connected to `p3`.
  have hsepQ : e.symm 6 ∈ s → e.symm 1 ∉ s → sQ.card = 0 := by
    intro h6s h1s
    have hP : ∀ u v, u ∈ (s : Set V) → v ∈ (s : Set V) → (graph e).Adj u v →
        2 ≤ lvl (e u) → 2 ≤ lvl (e v) := by
      intro u v hu _ huv hlu
      have := lvl_adj e huv
      by_contra hlv
      have hu2 : lvl (e u) = 2 := by omega
      rw [← e.eq_symm_apply.mpr (lvl_eq_two _ hu2)] at h1s
      exact h1s hu
    rw [Finset.card_eq_zero, hsQ, Finset.filter_eq_empty_iff]
    intro x hx hlx
    have : 2 ≤ lvl (e x) := of_preserved hconn (fun y => 2 ≤ lvl (e y)) hP h6s hx (by omega)
    omega
  by_cases h1s : e.symm 1 ∈ s <;> by_cases h6s : e.symm 6 ∈ s
  · have : sM.card < 2 := by
      by_contra h
      exact hsq (by omega) ⟨h1s, h6s⟩
    omega
  · have := hsepR h1s h6s
    have := h6' h6s
    omega
  · have := hsepQ h6s h1s
    have := h1' h1s
    omega
  · have := h1' h1s
    have := h6' h6s
    by_cases hm : 1 ≤ sM.card
    · have := hiso h1s h6s hm
      omega
    · omega

theorem largestInducedTreeSize_le [Fintype V] [DecidableEq V] :
    largestInducedTreeSize (graph e) ≤ 7 := by
  unfold largestInducedTreeSize
  apply csSup_le'
  rintro n ⟨s, rfl, hs⟩
  exact card_le_seven e hs

/-- The counterexample violates the upstream inequality: its largest induced tree has seven
vertices, while `⌈averageEccentricity + maxL / 3⌉ ≥ ⌈75/14 + 5/3⌉ = 8`. -/
theorem tree_lt_ceil [Fintype V] [DecidableEq V]
    (hne : (Finset.univ.image fun v => indepNeighborsCard (graph e) v).Nonempty) :
    (largestInducedTreeSize (graph e) : ℝ) <
      ⌈averageEccentricity (graph e) +
        ((Finset.univ.image fun v => indepNeighborsCard (graph e) v).max' hne : ℝ) / 3⌉ := by
  have hA := averageEccentricity_ge e
  have hL : (5 : ℝ) ≤
      ((Finset.univ.image fun v => indepNeighborsCard (graph e) v).max' hne : ℝ) := by
    exact_mod_cast (five_le_indepNeighborsCard e).trans
      (Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hT : (largestInducedTreeSize (graph e) : ℝ) ≤ 7 := by
    exact_mod_cast largestInducedTreeSize_le e
  have h7 : (7 : ℤ) < ⌈averageEccentricity (graph e) +
      ((Finset.univ.image fun v => indepNeighborsCard (graph e) v).max' hne : ℝ) / 3⌉ := by
    rw [Int.lt_ceil]
    push_cast
    linarith
  have h8 : (8 : ℝ) ≤ (⌈averageEccentricity (graph e) +
      ((Finset.univ.image fun v => indepNeighborsCard (graph e) v).max' hne : ℝ) / 3⌉ : ℝ) := by
    exact_mod_cast h7
  linarith

end Counterexample

universe u

/-- The upstream statement, quantified over every finite vertex type with at least two
elements. -/
def statement : Prop :=
  ∀ (α : Type u) [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α),
    G.Connected →
      let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
      ⌈averageEccentricity G + (maxL : ℝ) / 3⌉ ≤ (largestInducedTreeSize G : ℝ)

/-- The Formal Conjectures statement of WOWII Conjecture 72 is false in every universe. -/
theorem refuted : ¬ statement.{u} := by
  intro h
  exact not_le.mpr (tree_lt_ceil Equiv.ulift _)
    (h (ULift.{u} (Fin 28)) (graph Equiv.ulift) (graph_connected Equiv.ulift))

end AgenticConjectures.WowiiGraphConjecture72
