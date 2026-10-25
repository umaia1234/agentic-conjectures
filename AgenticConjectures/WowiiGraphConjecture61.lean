import Mathlib

/-!
# WOWII Graph Conjecture 61 — the bound `f(G) ≥ α(G) + 1`

Written on the Wall II, Conjecture 61 (E. DeLaVina, Graffiti.pc) states that every finite
simple connected graph `G` satisfies `f(G) ≥ r(G) + ⌈D(G) / 3⌉`, where `f(G)` is the number
of vertices of a largest induced forest, `r(G)` the Havel–Hakimi residue and `D(G)` the
diameter.  The conjecture is open.  `problems/wowii-graph-conjecture-61/PROOF.md` proves
partial results informally; this module formalizes its inequality (5) (first part of
Theorem 2): every connected graph with at least two vertices satisfies `f(G) ≥ α(G) + 1`.
The proof is the one of `PROOF.md`: a maximum independent set `I` together with one vertex
`x ∉ I` induces a star plus isolated vertices, hence a forest.

Correspondence with the upstream statement (`problems/wowii-graph-conjecture-61/upstream/`,
FormalConjectures commit `9118d083ffca1536f521f9a7d103201f537ea670`):

* `largestInducedForestSize` below has the same body as the upstream helper
  `SimpleGraph.largestInducedForestSize` of
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Induced.lean` (the `sSup` of the
  cardinalities of the finsets of vertices that induce an acyclic subgraph).  It is copied,
  not imported, because the upstream helper library is not a dependency of this repository.
* `α(G)` is mathlib's `SimpleGraph.indepNum`.
* The hypotheses `[Fintype α] [DecidableEq α] [Nontrivial α]` and `G.Connected` are those
  of the upstream `conjecture61`.  `Nontrivial α` (at least two vertices) is needed: the
  one-vertex graph has `f = α = 1`.  The residue and the diameter do not occur here, so the
  theorem is a partial result towards the conjecture, not a proof of it.
-/

namespace AgenticConjectures.WowiiGraphConjecture61

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The number of vertices of a largest induced forest of `G` (same body as the upstream
`SimpleGraph.largestInducedForestSize`). -/
noncomputable def largestInducedForestSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsAcyclic ∧ s.card = n }

omit [DecidableEq α] in
/-- Every vertex set inducing a forest gives a lower bound for `largestInducedForestSize`. -/
theorem card_le_largestInducedForestSize (G : SimpleGraph α) {s : Finset α}
    (hs : (G.induce (s : Set α)).IsAcyclic) : s.card ≤ largestInducedForestSize G := by
  apply le_csSup
  · refine ⟨Fintype.card α, ?_⟩
    rintro n ⟨t, -, rfl⟩
    exact Finset.card_le_univ t
  · exact ⟨s, hs, rfl⟩

omit [Fintype α] in
/-- An independent set `I` together with any vertex `x` induces a forest: every edge of
`G[I ∪ {x}]` contains `x`, so a cycle through a vertex `u ≠ x` would have to leave and
re-enter `u` through the same edge `ux`. -/
theorem isAcyclic_induce_insert (G : SimpleGraph α) {I : Finset α}
    (hI : G.IsIndepSet (I : Set α)) (x : α) :
    (G.induce ((insert x I : Finset α) : Set α)).IsAcyclic := by
  set H := G.induce ((insert x I : Finset α) : Set α)
  have mem : ∀ a : ((insert x I : Finset α) : Set α), a.1 ≠ x → a.1 ∈ I := by
    intro a hax
    have ha := a.2
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha
    exact ha.resolve_left hax
  -- every neighbour of a vertex `a ≠ x` is `x`
  have key : ∀ a b, H.Adj a b → a.1 ≠ x → b.1 = x := by
    intro a b hab hax
    by_contra hbx
    have hab' : G.Adj a.1 b.1 := hab
    exact hI (Finset.mem_coe.2 (mem a hax)) (Finset.mem_coe.2 (mem b hbx)) hab'.ne hab'
  -- no cycle is based at a vertex other than `x`
  have base : ∀ (u) (c : H.Walk u u), u.1 ≠ x → ¬ c.IsCycle := by
    intro u c hux hc
    apply hc.snd_ne_penultimate
    apply Subtype.ext
    rw [key _ _ (c.adj_snd hc.not_nil) hux, key _ _ (c.adj_penultimate hc.not_nil).symm hux]
  intro v c hc
  by_cases hvx : v.1 = x
  · have hsnd : c.snd.1 ≠ x := by
      intro h
      exact (c.adj_snd hc.not_nil).ne (Subtype.ext (hvx.trans h.symm))
    have hmem : c.snd ∈ c.support := c.getVert_mem_support 1
    exact base _ (c.rotate c.snd hmem) hsnd ((Walk.isCycle_rotate hmem).2 hc)
  · exact base v c hvx hc

/-- Inequality (5) of `PROOF.md`: a connected graph with at least two vertices satisfies
`f(G) ≥ α(G) + 1`. -/
theorem indepNum_add_one_le_largestInducedForestSize [Nontrivial α] (G : SimpleGraph α)
    (h : G.Connected) : G.indepNum + 1 ≤ largestInducedForestSize G := by
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  obtain ⟨x, hx⟩ : ∃ x, x ∉ I := by
    by_contra hall
    push Not at hall
    obtain ⟨v, -⟩ := exists_pair_ne α
    obtain ⟨u, hvu⟩ := h.preconnected.exists_adj_of_nontrivial v
    exact hI.isIndepSet (Finset.mem_coe.2 (hall v)) (Finset.mem_coe.2 (hall u)) hvu.ne hvu
  have hcard := card_le_largestInducedForestSize G (isAcyclic_induce_insert G hI.isIndepSet x)
  rwa [Finset.card_insert_of_notMem hx, hI.card_eq] at hcard

end AgenticConjectures.WowiiGraphConjecture61
