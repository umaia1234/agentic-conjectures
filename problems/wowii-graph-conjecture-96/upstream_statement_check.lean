/-
Faithfulness check: the upstream statement, over the upstream definitions, is closed by
`AgenticConjectures.WowiiGraphConjecture96.conjecture96`.

The two definitions below are copied from formal-conjectures at commit
`c094b979118b89adb77cf5f8d923ac9dd2e51b1d`, in their upstream namespace `SimpleGraph` and
under the section variables of their source files
(`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/VertexDistance.lean` and
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Independence.lean`). The theorem block
is copied from `upstream/GraphConjecture96.lean`, without the `@[category research open,
AMS 5]` attribute, and its `sorry` is replaced by a call to our theorem. Elaboration has to
unfold the upstream constants to ours, so a mismatch in any definition or in the statement
would make this file fail.

This file is deliberately not part of the library (it is not imported from
`AgenticConjectures.lean`). Run it from the repository root after `lake build`:

    lake env lean problems/wowii-graph-conjecture-96/upstream_statement_check.lean

The expected output is a single line listing the axioms `propext`, `Classical.choice` and
`Quot.sound`.
-/
import AgenticConjectures.WowiiGraphConjecture96

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `distEven G v` counts the vertices at even distance from `v` in `G`. This is
DeLaVina's `dist_even(v)` invariant appearing in several WOWII conjectures.
Distance zero is even, so `v` itself is always counted. -/
noncomputable def distEven (G : SimpleGraph α) (v : α) : ℕ :=
  (Finset.univ.filter fun w => Even (G.dist v w)).card

/-- Independence number of the neighbourhood of `v`. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture96

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

theorem conjecture96 (G : SimpleGraph α) (h : G.Connected) :
    let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    (G.indepNum : ℝ) ≤ 1 + (minDistEven : ℝ) * ((maxL : ℝ) - 1) := by
  exact AgenticConjectures.WowiiGraphConjecture96.conjecture96 G h

end WrittenOnTheWallII.GraphConjecture96

#print axioms WrittenOnTheWallII.GraphConjecture96.conjecture96
