import Mathlib

/-!
# Written on the Wall II, Conjecture 96

Conjecture 96 of E. DeLaViña's *Written on the Wall II* (Graffiti.pc, dated April 21, 2004,
listed with status `O`) reads:

> If G is a simple connected graph, then α(G) ≤ 1 + minimum dist_even(v)*(maximum of λ(v) -1)

Here `α(G)` is the independence number, `dist_even(v)` is the number of vertices at even
distance from `v` (distance zero counts, so `v` itself is included), and `λ(v)` is the
independence number of the subgraph induced by the neighbourhood of `v`.

This file proves the formal statement `WrittenOnTheWallII.GraphConjecture96.conjecture96` of
google-deepmind/formal-conjectures at commit `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
(snapshot `problems/wowii-graph-conjecture-96/upstream/GraphConjecture96.lean`). The theorem
`conjecture96` below has the upstream hypotheses `[Fintype α] [DecidableEq α] [Nontrivial α]`
and `G.Connected`; `statement` quantifies it over all finite vertex types and
`statement_holds` proves it. The proof also gives a per-root form, `indepNum_le_perRoot`.

## Upstream correspondence

* `distEven` and `indepNeighborsCard` are copied term for term, under the section variables
  `{α : Type*} [Fintype α] [DecidableEq α]` of their upstream files
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean` and
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Independence.lean`. Upstream they
  are in namespace `SimpleGraph`; here they are in this file's namespace, so that they
  cannot clash with other modules of the library.
* The statement of `conjecture96` is the upstream text verbatim. Only what is needed
  outside the formal-conjectures project changes: `import Mathlib` replaces
  `FormalConjecturesUtil`, and the `module`/`public`/`@[expose]` keywords and the
  `@[category research open, AMS 5]` attribute are dropped.
* This repository builds against Lean and mathlib `v4.30.0`; formal-conjectures at
  `c094b97` pins `v4.33.1`. The graph definitions the statement uses are textually the same
  in both, except that the `symm` field of `SimpleGraph` changed from `Symmetric` to the
  equivalent `Std.Symm`; the proof has not been compiled against `v4.33.1`.
* `[Nontrivial α]` is upstream's hypothesis. The literal WOWII row is false for the
  one-vertex graph: there `α = 1`, `min dist_even = 1` and `max λ = 0`, so the right-hand
  side is `1 + 1 * (0 - 1) = 0`. The inequality is stated in `ℝ`, so `maxL - 1` is a signed
  subtraction, as in the source.
* `problems/wowii-graph-conjecture-96/upstream_statement_check.lean` restates the upstream
  theorem over the upstream, `SimpleGraph`-namespaced definitions and closes it with
  `conjecture96`.

## Proof

Write `λ(u) = indepNeighborsCard G u`, `Λ = max_u λ(u)` and `E(v) = distEven G v`.

* `one_le_indepNeighborsCard`: on at least two vertices every vertex has a neighbour, so
  `Λ ≥ 1` and the real number `Λ - 1` equals the natural number `Λ - 1`.
* `indepNum_le_one` (case `Λ ≤ 1`): two non-adjacent vertices would give, by
  `exists_dist_two` and `exists_parent`, a path `x - y - w` with `x`, `w` distinct and
  non-adjacent, so `λ(y) ≥ 2` (`two_le_indepNeighborsCard`). Hence `α ≤ 1 = 1 + E · 0`.
* `indepNum_le_perRoot` (counting, for any root `v`): fix a maximum independent set `I`.
  Send each `x ∈ I` at even distance from `v` to itself, and each `x` at odd distance to a
  BFS parent (`exists_parent`); the image consists of even-distance vertices. The fibre over
  a vertex of `I` is that vertex alone. The fibre over `u ∉ I` is an independent set of
  neighbours of `u` (`card_le_indepNeighborsCard`); if also `u ≠ v`, it stays independent
  after adding a parent of `u`, which lies two levels closer to `v` than the fibre. So
  `α ≤ max(1, λ(v)) + ∑_{u ≠ v, d(v,u) even} max(1, λ(u) - 1)`.
* `indepNum_le_of_two_le` (case `Λ ≥ 2`): bounding every term gives
  `α ≤ Λ + (E(v) - 1)(Λ - 1) = 1 + E(v)(Λ - 1)`; `conjecture96` takes `v` minimising `E`.

The star `K_{1,m}` (`m ≥ 1`) attains equality: at its centre `E = 1`, and `Λ = α = m`.
-/

namespace AgenticConjectures.WowiiGraphConjecture96

open SimpleGraph

section Definitions

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Upstream definition, verbatim (modulo namespace).

`distEven G v` counts the vertices at even distance from `v` in `G`. This is
DeLaVina's `dist_even(v)` invariant appearing in several WOWII conjectures.
Distance zero is even, so `v` itself is always counted. -/
noncomputable def distEven (G : SimpleGraph α) (v : α) : ℕ :=
  (Finset.univ.filter fun w => Even (G.dist v w)).card

/-- Upstream definition, verbatim (modulo namespace).

Independence number of the neighbourhood of `v`. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

end Definitions

section Graph

variable {V : Type*} {G : SimpleGraph V}

/-- BFS parent: in a connected graph, every vertex `x ≠ v` has a neighbour one step
closer to `v`. -/
theorem exists_parent (hG : G.Connected) {v x : V} (hx : x ≠ v) :
    ∃ y, G.Adj y x ∧ G.dist v y + 1 = G.dist v x := by
  obtain ⟨p, -, hp⟩ := hG.exists_path_of_dist v x
  have hpos : 0 < G.dist v x := hG.pos_dist_of_ne hx.symm
  have key : ∀ q : G.Walk x v, q.length = G.dist v x →
      ∃ y, G.Adj y x ∧ G.dist v y + 1 = G.dist v x := by
    intro q hq
    cases q with
    | nil => exact absurd rfl hx
    | cons h q' =>
      rename_i y
      refine ⟨y, h.symm, ?_⟩
      have hlen : q'.length + 1 = G.dist v x := by simpa using hq
      have h1 : G.dist y v ≤ q'.length := SimpleGraph.dist_le q'
      rw [SimpleGraph.dist_comm] at h1
      rcases h.symm.diff_dist_adj (u := v) with h2 | h2 | h2 <;> omega
  exact key p.reverse (by simp [hp])

/-- If `x` and `z` are at distance at least two, some vertex is at distance exactly two
from `x`. -/
theorem exists_dist_two (hG : G.Connected) {x z : V} (h : 2 ≤ G.dist x z) :
    ∃ w, G.dist x w = 2 := by
  obtain ⟨n, hn⟩ : ∃ n, G.dist x z = n + 2 := ⟨G.dist x z - 2, by omega⟩
  induction n generalizing z with
  | zero => exact ⟨z, hn⟩
  | succ n ih =>
    have hzx : z ≠ x := by
      rintro rfl
      simp at hn
    obtain ⟨y, -, hy⟩ := exists_parent hG hzx
    exact ih (z := y) (by omega) (by omega)

end Graph

section Local

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α}

omit [DecidableEq α] in
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

omit [DecidableEq α] in
/-- A path `x - y - z` with `x ≠ z` and `x`, `z` non-adjacent gives an independent pair
in the neighbourhood of `y`. -/
theorem two_le_indepNeighborsCard {x y z : α} (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hxz : x ≠ z) (hn : ¬ G.Adj x z) : 2 ≤ indepNeighborsCard G y := by
  classical
  have h := card_le_indepNeighborsCard (G := G) y {x, z}
    (by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hxy.symm
      · exact hyz)
    (by
      intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hn
      · exact fun h => hn h.symm
      · exact absurd rfl hab)
  rwa [Finset.card_pair hxz] at h

omit [DecidableEq α] in
/-- In a connected graph on at least two vertices, every vertex has a neighbour, so
every local independence number is at least one. -/
theorem one_le_indepNeighborsCard [Nontrivial α] (hG : G.Connected) (u : α) :
    1 ≤ indepNeighborsCard G u := by
  classical
  obtain ⟨x, hx⟩ := exists_ne u
  obtain ⟨y, hyu, -⟩ := exists_parent hG (v := x) hx.symm
  have h := card_le_indepNeighborsCard (G := G) u {y}
    (by
      intro w hw
      rw [Finset.mem_singleton.mp hw]
      exact hyu.symm)
    (by
      intro a ha b hb hab
      rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb] at hab
      exact absurd rfl hab)
  simpa using h

omit [DecidableEq α] in
/-- **Case `max λ ≤ 1`.** If every neighbourhood has independence number at most one,
then a connected graph has independence number at most one. -/
theorem indepNum_le_one (hG : G.Connected) (hl : ∀ u, indepNeighborsCard G u ≤ 1) :
    G.indepNum ≤ 1 := by
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  rw [← hI.card_eq]
  by_contra hlt
  have hlt' : 1 < I.card := by omega
  obtain ⟨x, hx, z, hz, hxz⟩ := Finset.one_lt_card.mp hlt'
  have hnadj : ¬ G.Adj x z := hI.isIndepSet hx hz hxz
  have h2 : 2 ≤ G.dist x z := by
    have h0 : G.dist x z ≠ 0 := fun h0 => hxz (hG.dist_eq_zero_iff.mp h0)
    have h1 : G.dist x z ≠ 1 := fun h1 => hnadj (dist_eq_one_iff_adj.mp h1)
    omega
  obtain ⟨w, hw⟩ := exists_dist_two hG h2
  have hwx : w ≠ x := by
    rintro rfl
    simp at hw
  obtain ⟨y, hyw, hy⟩ := exists_parent hG hwx
  have hxy : G.Adj x y := dist_eq_one_iff_adj.mp (by omega)
  have hnxw : ¬ G.Adj x w := fun h => by
    rw [dist_eq_one_iff_adj.mpr h] at hw
    omega
  have := two_le_indepNeighborsCard hxy hyw hwx.symm hnxw
  have := hl y
  omega

/-- **Per-root form.** For every root `v` of a connected graph,
`α(G) ≤ max(1, λ(v)) + ∑_{u ≠ v, d(v,u) even} max(1, λ(u) - 1)`. -/
theorem indepNum_le_perRoot (hG : G.Connected) (v : α) :
    G.indepNum ≤ max 1 (indepNeighborsCard G v) +
      ∑ u ∈ (Finset.univ.filter fun w => Even (G.dist v w)).erase v,
        max 1 (indepNeighborsCard G u - 1) := by
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  have hind : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y :=
    fun x hx y hy hxy => hI.isIndepSet hx hy hxy
  -- BFS parents towards the root `v`.
  have hpar : ∀ x, ∃ y, x ≠ v → G.Adj y x ∧ G.dist v y + 1 = G.dist v x := by
    intro x
    by_cases hx : x = v
    · exact ⟨x, fun h => absurd hx h⟩
    · obtain ⟨y, hy⟩ := exists_parent hG hx
      exact ⟨y, fun _ => hy⟩
  choose par hpar using hpar
  -- `φ` keeps even-distance vertices and sends odd-distance ones to their parent.
  let φ : α → α := fun x => if Even (G.dist v x) then x else par x
  have hφ : ∀ x u, φ x = u → x ≠ u → G.Adj u x ∧ G.dist v u + 1 = G.dist v x := by
    intro x u hxu hne
    by_cases he : Even (G.dist v x)
    · simp only [φ, he, if_true] at hxu
      exact absurd hxu hne
    · have hxv : x ≠ v := by
        rintro rfl
        simp at he
      simp only [φ, he, if_false] at hxu
      subst hxu
      exact hpar x hxv
  have hmaps : Set.MapsTo φ I (Finset.univ.filter fun w => Even (G.dist v w)) := by
    intro x _
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    by_cases he : Even (G.dist v x)
    · simp only [φ, he, if_true]
    · have hxv : x ≠ v := by
        rintro rfl
        simp at he
      simp only [φ, he, if_false]
      rw [← (hpar x hxv).2, Nat.even_add_one] at he
      exact not_not.mp he
  -- Fibre over a vertex of `I`: only the vertex itself.
  have hF1 : ∀ u ∈ I, (I.filter fun x => φ x = u).card ≤ 1 := by
    intro u hu
    have hsub : (I.filter fun x => φ x = u) ⊆ {u} := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_singleton]
      by_contra hne
      exact hind u hu x hx.1 (Ne.symm hne) (hφ x u hx.2 hne).1
    calc (I.filter fun x => φ x = u).card ≤ ({u} : Finset α).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton u
  -- Fibre over a vertex outside `I`: every member is a neighbour of `u`.
  have hfib : ∀ u ∉ I, ∀ x ∈ I.filter (fun x => φ x = u),
      G.Adj u x ∧ G.dist v u + 1 = G.dist v x := by
    intro u hu x hx
    rw [Finset.mem_filter] at hx
    exact hφ x u hx.2 (fun h => hu (h ▸ hx.1))
  have hF2 : ∀ u ∉ I, (I.filter fun x => φ x = u).card ≤ indepNeighborsCard G u := by
    intro u hu
    apply card_le_indepNeighborsCard u
    · exact fun x hx => (hfib u hu x hx).1
    · intro x hx y hy hxy
      exact hind x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  -- Fibre over a non-root vertex outside `I`: the parent of `u` can be added.
  have hF3 : ∀ u ∉ I, u ≠ v →
      (I.filter fun x => φ x = u).card + 1 ≤ indepNeighborsCard G u := by
    intro u hu huv
    obtain ⟨hwu, hwd⟩ := hpar u huv
    have hwnot : par u ∉ I.filter (fun x => φ x = u) := by
      intro hw
      have := (hfib u hu (par u) hw).2
      omega
    have hnadj : ∀ x ∈ I.filter (fun x => φ x = u), ¬ G.Adj (par u) x := by
      intro x hx hadj
      have h1 := (hfib u hu x hx).2
      rcases hadj.diff_dist_adj (u := v) with h | h | h <;> omega
    rw [← Finset.card_insert_of_notMem hwnot]
    apply card_le_indepNeighborsCard u
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hwu.symm
      · exact (hfib u hu x hx).1
    · intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx <;>
        rcases Finset.mem_insert.mp hy with rfl | hy
      · exact absurd rfl hxy
      · exact hnadj y hy
      · exact fun h => hnadj x hx h.symm
      · exact hind x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  -- Sum the fibre sizes over the even-distance vertices.
  have hv : v ∈ Finset.univ.filter fun w => Even (G.dist v w) := by simp
  rw [← hI.card_eq, Finset.card_eq_sum_card_fiberwise hmaps, ← Finset.add_sum_erase _ _ hv]
  apply add_le_add
  · by_cases hvI : v ∈ I
    · exact (hF1 v hvI).trans (le_max_left _ _)
    · exact (hF2 v hvI).trans (le_max_right _ _)
  · apply Finset.sum_le_sum
    intro u hu
    have huv : u ≠ v := Finset.ne_of_mem_erase hu
    by_cases huI : u ∈ I
    · exact (hF1 u huI).trans (le_max_left _ _)
    · have := hF3 u huI huv
      exact le_trans (by omega) (le_max_right _ _)

/-- **Case `max λ ≥ 2`.** If every local independence number is at most `L` and
`L ≥ 2`, then `α(G) ≤ 1 + distEven(v) · (L - 1)` for every root `v`. -/
theorem indepNum_le_of_two_le (hG : G.Connected) (v : α) {L : ℕ} (hL : 2 ≤ L)
    (hl : ∀ u, indepNeighborsCard G u ≤ L) :
    G.indepNum ≤ 1 + distEven G v * (L - 1) := by
  have hv : v ∈ Finset.univ.filter fun w => Even (G.dist v w) := by simp
  have hsum : ∑ u ∈ (Finset.univ.filter fun w => Even (G.dist v w)).erase v,
      max 1 (indepNeighborsCard G u - 1) ≤ (distEven G v - 1) * (L - 1) := by
    have h := Finset.sum_le_card_nsmul
      ((Finset.univ.filter fun w => Even (G.dist v w)).erase v)
      (fun u => max 1 (indepNeighborsCard G u - 1)) (L - 1)
      (fun u _ => max_le (by omega) (Nat.sub_le_sub_right (hl u) 1))
    rwa [Finset.card_erase_of_mem hv, smul_eq_mul] at h
  have hroot : max 1 (indepNeighborsCard G v) ≤ L := max_le (by omega) (hl v)
  have hE : 0 < distEven G v := Finset.card_pos.mpr ⟨v, hv⟩
  have h := indepNum_le_perRoot hG v
  obtain ⟨e, he⟩ : ∃ e, distEven G v = e + 1 := ⟨distEven G v - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  rw [he] at hsum ⊢
  simp only [Nat.add_sub_cancel] at hsum ⊢
  have hring : (e + 1) * m = e * m + m := by ring
  omega

end Local

section Conjecture

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- WOWII Conjecture 96, exactly as stated upstream (formal-conjectures `c094b97`):
for a connected graph `G` on at least two vertices,
`α(G) ≤ 1 + min_v distEven(v) · (max_v λ(v) - 1)`. -/
theorem conjecture96 (G : SimpleGraph α) (h : G.Connected) :
    let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    (G.indepNum : ℝ) ≤ 1 + (minDistEven : ℝ) * ((maxL : ℝ) - 1) := by
  intro minDistEven maxL
  have hl : ∀ u, indepNeighborsCard G u ≤ maxL := fun u =>
    Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))
  obtain ⟨v, -, hv⟩ : ∃ v ∈ Finset.univ, distEven G v = minDistEven :=
    Finset.mem_image.mp (Finset.min'_mem _ _)
  have hL1 : 1 ≤ maxL := (one_le_indepNeighborsCard h v).trans (hl v)
  have key : G.indepNum ≤ 1 + minDistEven * (maxL - 1) := by
    rcases Nat.lt_or_ge maxL 2 with hlt | hge
    · have := indepNum_le_one h (fun u => by have := hl u; omega)
      omega
    · rw [← hv]
      exact indepNum_le_of_two_le h v hge hl
  have hcast : ((maxL - 1 : ℕ) : ℝ) = (maxL : ℝ) - 1 := by
    rw [Nat.cast_sub hL1, Nat.cast_one]
  calc (G.indepNum : ℝ) ≤ ((1 + minDistEven * (maxL - 1) : ℕ) : ℝ) := by exact_mod_cast key
    _ = 1 + (minDistEven : ℝ) * ((maxL : ℝ) - 1) := by
      rw [Nat.cast_add, Nat.cast_mul, hcast, Nat.cast_one]

end Conjecture

universe u

/-- The upstream open statement, quantified over every finite vertex type with at least
two elements. -/
def statement : Prop :=
  ∀ (α : Type u) [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α),
    G.Connected →
      let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
      let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
      (G.indepNum : ℝ) ≤ 1 + (minDistEven : ℝ) * ((maxL : ℝ) - 1)

/-- WOWII Conjecture 96 holds. -/
theorem statement_holds : statement.{u} := fun _ _ _ _ G h => conjecture96 G h

end AgenticConjectures.WowiiGraphConjecture96

