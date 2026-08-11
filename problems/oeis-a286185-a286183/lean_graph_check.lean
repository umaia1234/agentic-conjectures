/-
Faithfulness check: print the edge sets of the Lean definitions `prism`,
`moebius` and `antiprism` from `AgenticConjectures/OeisA286185A286183.lean`, so
they can be diffed against the graphs the certificate brute-forces.

This file is deliberately *not* part of the library (it is not imported from
`AgenticConjectures.lean`); it is a reproduction aid.  Run from the repository
root:

    lake env lean problems/oeis-a286185-a286183/lean_graph_check.lean

and compare the output with

    python3 problems/oeis-a286185-a286183/certificate.py --print-edges

Vertex `(i, r)` is printed with index `2*i + r`, matching the certificate's
indexing.  `decide` is used only to evaluate the adjacency predicate on concrete
finite arguments; nothing here is a proof and nothing is exported.
-/
import AgenticConjectures.OeisA286185A286183

open AgenticConjectures.OeisA286185A286183

instance decPrism (n : ℕ) : DecidableRel (prism n).Adj := by
  intro u v; unfold prism; simp only; infer_instance

instance decMoebius (n : ℕ) : DecidableRel (moebius n).Adj := by
  intro u v; unfold moebius; simp only; infer_instance

instance decAntiprism (n : ℕ) : DecidableRel (antiprism n).Adj := by
  intro u v; unfold antiprism; simp only; infer_instance

/-- Edges of `Γ` on `ZMod n × Bool`, as index pairs `2*i + r < 2*j + s`. -/
def edgeList (n : ℕ) (Γ : SimpleGraph (ZMod n × Bool)) [DecidableRel Γ.Adj]
    [NeZero n] : List (Nat × Nat) :=
  let verts := (List.range n).flatMap fun i => [((i : ZMod n), false), ((i : ZMod n), true)]
  let idx : ZMod n × Bool → Nat := fun u => 2 * u.1.val + (if u.2 then 1 else 0)
  (verts.flatMap fun u => verts.map fun v => (u, v)).filterMap fun (u, v) =>
    if Γ.Adj u v ∧ idx u < idx v then some (idx u, idx v) else none

def report (n : ℕ) [NeZero n] : String :=
  let p := (edgeList n (prism n)).mergeSort (fun a b => a ≤ b)
  let m := (edgeList n (moebius n)).mergeSort (fun a b => a ≤ b)
  let a := (edgeList n (antiprism n)).mergeSort (fun a b => a ≤ b)
  s!"n={n}\n  prism     {p}\n  moebius   {m}\n  antiprism {a}"

#eval IO.println <| String.intercalate "\n"
  [report 1, report 2, report 3, report 4, report 5, report 6]
