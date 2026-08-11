# Eight-element attempt: inconclusive

No run below produced a counterexample, and no run proved that one cannot
exist.  In particular, these experiments do not extend the certified
seven-element bound in the literature.

## Unsplit MILP

The reduced integer formulation used binary variables for `D` and `Y`, an
integer largest-star variable, exact down-closure implications, the Berge
half-family inequality, and the standard rank/ground-set reductions.

Observed after a 300-second HiGHS 1.12.0 run:

```text
status:            time limit reached
variables:         513
input rows:        9,595
incumbent:         |Y| - z = 0 (|Y| = 63, z = 63)
dual bound:        13 for the maximization form
branch-and-bound:  7,002 nodes
LP iterations:     913,279
```

The zero incumbent is not evidence of infeasibility while the dual bound is
positive.

## Symmetry split

The variables for the eight sets of size seven were fixed into the nine
isomorphism types indexed by how many of them belong to `D`.  Each feasibility
model explicitly required `|Y| - z >= 1`.

All nine processes reached their 240-second limits.  None found a feasible
counterexample, but none returned UNSAT.  The runs were deliberately stopped
instead of consuming more shared compute.

## Additional reductions tried

The saturation lemma from `README.md`, equality `D = down(Y)`, and a
largest-star symmetry order substantially reduced early MILP search, but the
run was interrupted before a terminal result.  A BDD-based SAT encoding of
the seven-element benchmark was also stopped after approximately 154 seconds
to reduce machine load.  It returned no terminal status.

## Bottom line

The computationally meaningful next target is not another unlogged heuristic
run.  It is a proof-producing SAT or exact-rational IP solve whose certificate
is checked independently.  Until such a certificate exists, `n = 8` must be
reported as unresolved by this directory.

