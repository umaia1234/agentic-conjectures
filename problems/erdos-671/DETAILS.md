**English** | [한국어](DETAILS.ko.md)

# Mathematical details for Erdős #671

The Lean module constructs a single interpolation array in stages. This file
is an orientation guide to the kernel-checked argument, not a replacement for
it.

## Stage geometry

A `Cell` is a nondegenerate closed interval inside `[-1,1]`. A `Level k` is a
finite family of pairwise-disjoint cells whose interiors lie in a protected
subinterval. Each parent cell has many children at the next level.

For every stage, three kinds of exact-cardinality rows are installed:

1. filler rows, used to occupy every row size not reserved below;
2. collision-pair rows, one for each child cell; and
3. an exterior row, used away from all child cells.

The cells are shrunk so that every row except the one assigned to a selected
child has Lebesgue value at most `2` throughout that child. The assigned
collision row has Lebesgue value at least `k+1` there. Outside all children,
the exterior row has value at least `k+1`. Consequently every point sees a
row exceeding `k+1` in every sufficiently late stage. This proves cofinal
unboundedness everywhere.

## Collision rows

The key local device starts with two interpolation nodes approaching a common
centre at different slopes. Their Lagrange coefficients become large with
opposite signs, while the remaining background coefficients stay controlled.
The formalization proves the required limits from the product formula for the
Lagrange basis and chooses a sufficiently small collision parameter by
neighbourhood arguments. No numerical approximation or external oracle is
used.

## Selecting a convergence point

Fix a continuous function `f`. At stage `k`, the proof samples `f` at
`k^3+1` protected points. A pigeonhole lemma finds two samples whose values
differ by at most `2*‖f‖/k^3`. The child corresponding to this pair is selected.
The selected children form nested compact intervals, so their intersection
contains a point `selectedPoint f`.

At that point, every nonselected row has Lebesgue value at most `2`. Standard
polynomial approximation and the Lebesgue error bound therefore give
convergence along those rows. On the single selected row in each stage, the
opposite large coefficients multiply the close sample values; the resulting
error is `O(1/k^2)`, the coefficient residual is `O(1/k)`, and the selected
target converges to `selectedPoint f`. Hence those exceptional rows converge
as well, proving convergence of the full sequence.

## Trust boundary

All limit, compactness, approximation, interpolation, and cardinality claims
are proved in Lean. `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`. The construction is noncomputable, as
expected for its choice and compactness steps, but introduces no mathematical
axiom beyond those standard Lean dependencies.
