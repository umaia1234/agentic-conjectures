/-
Faithfulness check: the negation of the upstream statement, over the upstream definitions,
follows from `AgenticConjectures.TxGraffitiConjecture3.not_statement` given `G48LowerBound`.

The six definitions below are copied verbatim from formal-conjectures (Apache-2.0) at commit
`c094b979118b89adb77cf5f8d923ac9dd2e51b1d`, in their upstream namespace `SimpleGraph` and under
the section variables of their source files
(`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Matching.lean`,
`.../Domination.lean` and `.../Saturation.lean`). The binders and conclusion of
`Arxiv.«2507.17780».tx_graffiti_conjecture_3` are copied from `upstream/3.lean`; since the
statement is false, the check proves its negation. The two bridge lemmas have to unfold the
upstream constants to ours, so a mismatch in any definition or binder makes this file fail.

This file is not part of the library (it is not imported from `AgenticConjectures.lean`). Run it
from the repository root after `lake build`:

    lake env lean problems/txgraffiti-conjecture-3/upstream_statement_check.lean

The expected output is two lines listing the axioms `propext`, `Classical.choice` and
`Quot.sound`.
-/
import AgenticConjectures.TxGraffitiConjecture3

namespace SimpleGraph

section Matching
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A finite set of edges `M` is a *matching* of `G` if every element of `M` is
an edge of `G` and any two edges of `M` are equal or share no vertex (no vertex
is covered twice). -/
def IsEdgeMatching (G : SimpleGraph α) (M : Finset (Sym2 α)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
    ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ = e₂ ∨ ∀ v : α, ¬ (v ∈ e₁ ∧ v ∈ e₂)

/-- A matching `M` of `G` is *maximal* if no further edge of `G` can be added to
`M` while keeping the matching property. -/
def IsMaximalEdgeMatching (G : SimpleGraph α) (M : Finset (Sym2 α)) : Prop :=
  G.IsEdgeMatching M ∧
    ∀ e ∈ G.edgeSet, e ∉ M → ¬ G.IsEdgeMatching (insert e M)
end Matching

section Domination
variable {α : Type*} {G : SimpleGraph α} [Fintype α] [DecidableEq α]

/-- A set `D` is a dominating set for `G` if every vertex of `G` is either in
`D` or adjacent to a vertex of `D`. -/
def IsDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

@[mk_iff]
structure IsNIndepDominatingSet (n : ℕ) (D : Finset α) : Prop where
  isIndep : G.IsIndepSet D
  isDominating : G.IsDominating D
  card_eq : D.card = n

noncomputable def indepDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsNIndepDominatingSet n D}
end Domination

section Saturation
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The *saturation number* `μ*(G)` (also called the lower matching number): the
minimum number of edges in a maximal matching of `G`.

Every finite graph has a maximal matching (extend the empty matching greedily),
so this set is nonempty and the infimum is a genuine minimum. -/
noncomputable def saturationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ M : Finset (Sym2 α), G.IsMaximalEdgeMatching M ∧ M.card = n}
end Saturation

end SimpleGraph

open SimpleGraph

namespace Arxiv.«2507.17780»

theorem indepDominationNumber_eq {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    AgenticConjectures.TxGraffitiConjecture3.indepDominationNumber G =
      G.indepDominationNumber := by
  unfold AgenticConjectures.TxGraffitiConjecture3.indepDominationNumber
    SimpleGraph.indepDominationNumber
  congr 1
  ext n
  constructor
  · rintro ⟨D, h1, h2, h3⟩
    exact ⟨D, h1, h2, h3⟩
  · rintro ⟨D, h1, h2, h3⟩
    exact ⟨D, h1, h2, h3⟩

theorem saturationNumber_eq {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    AgenticConjectures.TxGraffitiConjecture3.saturationNumber G = G.saturationNumber := rfl

/-- The upstream binders and conclusion, verbatim, under a negation. -/
theorem not_tx_graffiti_conjecture_3
    (h : AgenticConjectures.TxGraffitiConjecture3.G48LowerBound) :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (r : ℕ) (_hReg : ∀ v, G.degree v = r) (_hr : 1 ≤ r),
      G.indepDominationNumber ≤ G.saturationNumber := by
  intro hFC
  apply AgenticConjectures.TxGraffitiConjecture3.not_statement h
  intro V _ _ G _ r hReg hr
  rw [indepDominationNumber_eq, saturationNumber_eq]
  exact hFC V G r hReg hr

/-- The same with `1 ≤ r` replaced by `4 ≤ r` (our restriction, not an upstream declaration). -/
theorem not_tx_graffiti_conjecture_3_ge4
    (h : AgenticConjectures.TxGraffitiConjecture3.G48LowerBound) :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (r : ℕ) (_hReg : ∀ v, G.degree v = r) (_hr : 4 ≤ r),
      G.indepDominationNumber ≤ G.saturationNumber := by
  intro hFC
  apply AgenticConjectures.TxGraffitiConjecture3.not_statementGeFour h
  intro V _ _ G _ r hReg hr
  rw [indepDominationNumber_eq, saturationNumber_eq]
  exact hFC V G r hReg hr

end Arxiv.«2507.17780»

#print axioms Arxiv.«2507.17780».not_tx_graffiti_conjecture_3
#print axioms Arxiv.«2507.17780».not_tx_graffiti_conjecture_3_ge4
