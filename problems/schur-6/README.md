# Independent Schur-6 attempt

Status on 2026-08-11: the published partition of `[1,536]` is reproduced and
independently verified.  No valid partition of `[1,537]` was found.  The best
saved 537-coloring has exactly two monochromatic Schur triples; this is a near
coloring, **not** a new lower bound.

## Published 536 certificate

The source is Fredricksen and Sweet, *Symmetric Sum-Free Partitions and Lower
Bounds for Schur Numbers*, Electronic Journal of Combinatorics 7 (2000), R32:

<https://www.combinatorics.org/ojs/index.php/eljc/article/download/v7i1r32/pdf/>

`published_536_half.txt` transcribes the six sets in Section 4.  The paper's
partition is symmetric under `x -> 537-x`, apart from its documented exceptional
pair: 179 has color 4 and 358 has color 1.  `reconstruct_published.py` performs
only that reconstruction.  The separate `verify.py` checks coverage, uniqueness,
ranges, and every `x <= y`, `x+y=z` triple directly.

Reproduce the certificate check from the repository root:

```bash
python3 problems/schur-6/reconstruct_published.py \
  problems/schur-6/published_536_half.txt \
  > /tmp/reconstructed_536.col
cmp /tmp/reconstructed_536.col \
  problems/schur-6/published_536.col
python3 problems/schur-6/verify.py \
  problems/schur-6/published_536.col --maximum 536
```

Observed result:

```text
valid=true
assigned_distinct=536
color_sizes=[129,86,110,77,64,70]
violations=[]
```

Thus this work independently verifies `S(6) >= 536` under the usual convention
that `S(k)` is the greatest colorable interval endpoint.

## The 537 searches

Merely adding 537 to a color of the symmetric published certificate creates,
for colors 1 through 6 respectively, 64, 43, 55, 38, 32, and 35 violations of
the form `x+(537-x)=537`.  Consequently, extending this certificate requires a
large symmetry-breaking rearrangement rather than a single insertion.

### Weighted local search

`local_search.cpp` is a focused, weighted min-conflicts search with breakout
penalties, tabu tenure, noise, and deterministic seeding.  It explicitly treats
`x=x` triples as two-variable constraints.  Build and reproduce the main run:

```bash
g++ -O3 -std=c++20 problems/schur-6/local_search.cpp \
  -o /tmp/schur6_local
/tmp/schur6_local --maximum 537 --colors 6 \
  --seed-file problems/schur-6/published_536.col \
  --seconds 180 --seed 20260811 --perturb 6 --noise 0.02 \
  --output /tmp/schur537_best.col
python3 problems/schur-6/verify.py \
  /tmp/schur537_best.col --maximum 537
```

The main run executed 2,736,128 moves in 180.153 seconds and improved from 64
violations to 2.  A second deterministic capture run reached the same state at
move 574,532.  It is saved as `near_537_two_violations.col`; independent checking
finds exactly:

```text
color 4: 12+12=24
color 4: 12+24=36
```

The near coloring differs from the published 536 coloring on 459 of the first
536 integers, so it is not a superficial one-point extension.

`repair_search.py` exhaustively branches on a vertex of a current violation and
uses an exact packed representation for memoization.  The following run excludes
every repair of the saved near coloring using at most five recolorings:

```bash
python3 problems/schur-6/repair_search.py \
  problems/schur-6/near_537_two_violations.col \
  --maximum 537 --colors 6 --depth 5 --seconds 60
```

It exhausts 232,887 search nodes (212,143 at depth 5) without finding a repair.
This is only a radius-5 result around one coloring, not a global impossibility
proof.

### Complete SAT encoding

`encode_cnf.py` emits an exact one-hot encoding.  It contains an exactly-one
constraint per integer, one forbidden monochromatic clause per color and Schur
triple, and sound first-occurrence color-symmetry breaking.  For `[1,537]` it
emits 3,222 variables and 443,829 clauses: 8,592 exactly-one clauses, 432,552
triple clauses for 72,092 triples, and 2,685 symmetry-breaking clauses.

```bash
python3 problems/schur-6/encode_cnf.py \
  --maximum 537 --colors 6 > /tmp/schur537.cnf
timeout 300s cadical /tmp/schur537.cnf > /tmp/schur537.model
# Run these only if the solver reports SATISFIABLE:
python3 problems/schur-6/decode_sat.py \
  /tmp/schur537.model --maximum 537 --colors 6 > /tmp/schur537.col
python3 problems/schur-6/verify.py \
  /tmp/schur537.col --maximum 537
```

CaDiCaL 1.7.3 did not decide the formula before the external timeout.  It
reported 1,852,345 conflicts, 3,638,375 decisions, 1,803,443 learned clauses,
224.05 CPU seconds, 336.12 elapsed seconds under concurrent load, and 162.98 MB
maximum resident memory.  Its 19 internal random-walk phases also reached a
minimum of two unsatisfied clauses, matching the independent local-search
minimum, but this is not evidence of unsatisfiability.

`flip_phase.py` can flip Boolean polarities so an all-true solver phase matches a
given coloring; `decode_sat.py --phase-seed ...` reverses that transformation.
This optional route was unit-tested but was not substituted for the timed full
SAT run reported above.

## Cross-checks and limitations

The encoder/decoder were checked on the known boundary `S(2)=4`: the generated
`[1,4]` instance was decoded and accepted by `verify.py`, while `[1,5]` was
reported UNSAT by CaDiCaL.  The polarity-flipped decode path passed the same
test.  Python files pass `py_compile`, and the C++ search builds cleanly with
`-Wall -Wextra -pedantic`.

No file here certifies `[1,537]`, and no run proves that it is impossible.  The
concrete bottleneck is a persistent two-violation basin reached independently by
the focused search and CaDiCaL's random walk; the full CDCL instance remains
undecided after roughly 1.85 million conflicts.
