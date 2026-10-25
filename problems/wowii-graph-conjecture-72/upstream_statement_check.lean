/-
Faithfulness check: the upstream statement, over the upstream definitions, is refuted by
`AgenticConjectures.WowiiGraphConjecture72.refuted`.

The three definitions below are copied from formal-conjectures at commit
`c094b979118b89adb77cf5f8d923ac9dd2e51b1d`, in their upstream namespace `SimpleGraph` and
under the section variables of their source files (`Eccentricity.lean`,
`LargestInducedTree.lean` and `Independence.lean` in
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/`). `Conjecture72` is the upstream
theorem `conjecture72` from `upstream/GraphConjecture72.lean` as a proposition about all vertex
types in a universe `u`: its section variables, its binders and its conclusion are copied
verbatim. `not_conjecture72` proves its negation with our theorem. Elaboration has to unfold
the upstream constants to ours, so a mismatch in any definition or in the statement would make
this file fail.

This file is deliberately not part of the library (it is not imported from
`AgenticConjectures.lean`). Run it from the repository root after `lake build`:

    lake env lean problems/wowii-graph-conjecture-72/upstream_statement_check.lean

The expected output is a single line listing the axioms `propext`, `Classical.choice` and
`Quot.sound`.
-/
import AgenticConjectures.WowiiGraphConjecture72

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The average eccentricity of a graph `G`: the mean of `G.eccent v` over all vertices,
converted to a real number. Returns 0 if the graph has no vertices. -/
noncomputable def averageEccentricity (G : SimpleGraph α) : ℝ :=
  (∑ v : α, (G.eccent v).toNat) / (Fintype.card α : ℝ)

/-- `largestInducedTreeSize G` is the number of vertices in a largest induced subtree of `G`.
A tree is a connected acyclic graph; an induced tree is an induced subgraph that is a tree. -/
noncomputable def largestInducedTreeSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, s.card = n ∧ (G.induce (s : Set α)).IsTree }

/-- Independence number of the neighbourhood of `v`. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture72

open SimpleGraph

universe u

/-- The upstream theorem `conjecture72`, for vertex types `α : Type u`. -/
def Conjecture72 : Prop :=
  ∀ {α : Type u} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α)
    (h : G.Connected),
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    ⌈averageEccentricity G + (maxL : ℝ) / 3⌉ ≤ (largestInducedTreeSize G : ℝ)

theorem not_conjecture72 : ¬ Conjecture72.{u} := fun h =>
  AgenticConjectures.WowiiGraphConjecture72.refuted.{u} fun _ _ _ _ G hG => h G hG

end WrittenOnTheWallII.GraphConjecture72

#print axioms WrittenOnTheWallII.GraphConjecture72.not_conjecture72
