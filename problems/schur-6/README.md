# Independent Schur-6 attempt

Status on 2026-10-24: `S(6) >= 537` is now published.  Chen, Zhu and Long,
arXiv:2610.31362 (22 October 2026), give an explicit sum-free 6-partition of
`[1,537]`; this directory re-verifies it with two independent checkers.  Our own
SAT encoding of their search frame finds a further 537-partition, which only
reproduces their method and bound.  No partition of `[1,538]` was found; DRAT
certificates exclude specific template classes at 538 (section *Update
2026-10-24* below).  Nothing here is a new lower bound.

Status on 2026-08-11 (kept for the record; superseded by the paragraph above):
the published partition of `[1,536]` is reproduced and independently verified.
No valid partition of `[1,537]` was found.  The best saved 537-coloring has
exactly two monochromatic Schur triples; this is a near coloring, **not** a new
lower bound.

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

(2026-10-24: the first sentence is superseded.  `[1,537]` is now certified by
the published partition `published_537.col` and by `frame_537_kissat.col`, both
described below.)

## Update 2026-10-24

### Literature: `S(6) >= 537` is published

A literature check on 2026-10-24 found Zhiyang Chen, Ligeng Zhu and Fan Long,
*A new lower bound for the sixth Schur number: S(6) >= 537*, arXiv:2610.31362v1
(22 October 2026), <https://arxiv.org/abs/2610.31362>.  Their Theorem 1 lists a
partition of `[1,537]` into six sum-free sets.  It is palindromic
(`c(x) = c(538-x)`), every class is even sum-free modulo 538, and it was found
by SAT solving inside a "frame g" (their Definition 3, parameters `Q = 151`,
`d = 38`); their ancillary files list 131 pairwise inequivalent partitions.  The
537 bound is therefore their result, not ours, and the goal of the earlier
searches in this directory has been reached in the literature.

`published_537.col` is a transcription of their Theorem 1 listing.  It was
compared with their ancillary `anc/certificate.col` (SHA-256
`5f950ad88a5437108a0c6ab4b9d40cc2832a43dd474b5c4b269e02ac81258315`) and the two
agree exactly.  Two independent checkers accept it: the existing `verify.py`
(scans the members of each class) and the new `check_partition.cpp` (a C++
label-array checker that scans all 72,092 pairs `x <= y`, `x+y <= 537`, and also
reports palindromy and sum-freeness modulo `n+1`):

```bash
cd problems/schur-6
python3 verify.py published_537.col --maximum 537
g++ -O2 -std=c++17 check_partition.cpp -o /tmp/schur6_check
/tmp/schur6_check published_537.col 537
```

```text
valid=true  color_sizes=[76,76,88,70,76,151]  violations=[]  (verify.py JSON, condensed)
pairs_checked=72092 monochromatic_triples=0 structural_problems=0
palindromic=yes modular_triples_mod_538=0
valid=true                                                        (check_partition)
```

Both checkers also accept all 131 partitions of the ancillary
`solutions537.txt` (SHA-256 `fcae1cd5...4631b6`, not stored here); 125 of them
are palindromic.  That check is local-only because it needs the download.

### Template SAT encodings

`template_sat.py` writes DIMACS for structured classes of 6-colorings of
`[1,n]`: `--palindromic` folds `x` and `n+1-x` into one block of six variables
(269 blocks for `n = 537` and `n = 538`); `--frame Q D` adds the frame g of
Chen-Zhu-Long restated with `N = n+1` on `f(x) = min(x, N-x)` (`f < j => c != j`
for `j <= 4`; color 5 is forbidden for `f < D` and `Q-D < f < Q` and forced at
`f in {D, N-2Q}`; color 6 is forbidden for `f < Q` and forced at `f = Q` and,
unless `--no-middle`, for `f > N-2Q`).  For `n = 537`, `Q = 151`, `D = 38` this
is exactly their Definition 3; the paper defines the frame only for `n = 537`,
so the `n = 538` version (with `N = 539`) and the other `(Q, D)` values are our
own extrapolation of it.  `--frame6 Q` keeps only the color-6
conditions; `--fix FILE K` fixes the colors of `1..K` to those of a stored
partition; `--order [M]` numbers colors `1..M` by least elements.  Only
at-least-one clauses are emitted per block (sound for UNSAT claims; a decoded
model is re-verified anyway).  For palindromic colorings, sum-free on `[1,n]`
implies sum-free modulo `n+1` (a modular triple `x+y = z+N` maps to the
ordinary triple `(N-x)+(N-y) = N-z`), so at `n = 537` these classes are exactly
the paper's palindromic frame families.

`audit_template_cnf.py` is a separately written soundness audit: it re-derives
the class from its definition and accepts a CNF only if every clause is an
at-least-one clause, an at-most-one clause, the clause of an actual (folded)
Schur triple, a unit implied by the frame or by `--fix`, or a justified
color-order clause; `--sha256` pins the exact file.  An UNSAT certificate
therefore implies that the class is empty.  Negative tests (wrong `n`, wrong
frame, missing frame, wrong reference file) are rejected.

Sanity checks of the encoder against known values (kissat, under a second
each except 2 s for the last UNSAT): 3 colors, `[1,13]` SAT and `[1,14]` UNSAT
(`S(3) = 13`); 4 colors with `--order`, `[1,44]` SAT and `[1,45]` UNSAT
(`S(4) = 44`); palindromic 3-coloring of `[1,13]` and palindromic 4-coloring of
`[1,43]` SAT.  Every SAT model was decoded and accepted by `verify.py`.  When
`3 | n+1` no palindromic coloring exists, because `(n+1)/3` and `2(n+1)/3` would
share a class; this is why the Fredricksen-Sweet 536 partition needs its
exceptional pair `{179, 358}`.  It does not affect `n = 537, 538`.

### Results

Solver: kissat 4.0.4 (default options unless noted) on a shared, heavily loaded
machine; times are kissat CPU seconds.  Classes were first solved without proof
output, with a cap of 12M conflicts or a wall-clock limit ("unknown" = stopped
there).  "Certified" means that the CNF passed `audit_template_cnf.py` (pinned
by SHA-256) and that a DRAT proof written by a kissat run was checked by
`drat-trim` (`s VERIFIED`).  Every UNSAT result reported below for `n = 538`
is certified in this sense.

**n = 537.**  Palindromic, frame g(151, 38): SAT in 106 s (3.2M conflicts).
The decoded partition is `frame_537_kissat.col`, accepted by both checkers.
`compare_published_537.py` shows that it is not among the 131 published
partitions, even after `x -> r*x mod 538` and color renaming; the nearest
published one differs in 16 positions.  It reproduces the published method
and bound and is not a new result.  The palindromic class with `--order` only
(no frame) was stopped by hand, undecided, after 128 s (2.07M conflicts).

**Frame grid at n = 538.**  Each cell is the class of palindromic 6-colorings
of `[1,538]` in our `N = 539` frame g(Q, D).  Within frame g(Q, D), `Q` is the
least element of color 6 and `D` the least element of color 5, so different
cells are disjoint classes.  With default options kissat stopped every `D = 37`
class undecided at 12M conflicts (450-490 s each); these classes were then
decided with `--sat`, kissat's configuration for satisfiable instances, which
also wrote the checked proofs.  Times are CPU seconds of the deciding run.

| Q | D = 37 | D = 38 | D = 39 |
|---|---|---|---|
| 148 | UNSAT (`--sat`), 617 s, 13.18M, **certified** | UNSAT, 168 s, 5.48M, **certified** | UNSAT, 89 s, 3.28M, **certified** |
| 149 | UNSAT (`--sat`), 527 s, 12.33M, **certified** | UNSAT, 197 s, 6.02M, **certified** | UNSAT, 105 s, 3.53M, **certified** |
| 150 | UNSAT (`--sat`), 587 s, 13.37M, **certified** | UNSAT, 206 s, 5.96M, **certified** | UNSAT, 107 s, 3.68M, **certified** |
| 151 | UNSAT (`--sat`), 631 s, 14.88M, **certified** | UNSAT, 209 s, 6.06M, **certified** | UNSAT, 114 s, 3.76M, **certified** |
| 152 | UNSAT (`--sat`), 930 s, 17.50M, **certified** | UNSAT, 208 s, 6.18M, **certified** | UNSAT, 115 s, 3.79M, **certified** |
| 153 | UNSAT (`--sat`), 1045 s, 19.46M, **certified** | UNSAT, 266 s, 7.35M, **certified** | UNSAT, 134 s, 4.30M, **certified** |
| 154 | UNSAT (`--sat`), 844 s, 16.16M, **certified** | UNSAT, 255 s, 7.15M, **certified** | UNSAT, 137 s, 4.29M, **certified** |

Certified cells: CNF hash prefix, conflicts of the proof-producing run,
proof size, and drat-trim wall time.  Proofs were deleted after checking and
are regenerated by `certify_templates.sh`.

| class | CNF SHA-256 | kissat conflicts | proof size | drat-trim wall |
|---|---|---|---|---|
| g(148, 37) | `30f8862da0b42ce3...` | 13.18M | 1391 MB | 1040 s |
| g(149, 37) | `68754c62d18e1734...` | 12.33M | 1241 MB | 665 s |
| g(150, 37) | `3b6b04609be5878d...` | 13.37M | 1425 MB | 532 s |
| g(151, 37) | `702e7d3c33628cd9...` | 14.88M | 1673 MB | 1410 s |
| g(152, 37) | `6a0655e499c5ae49...` | 17.50M | 2047 MB | 1230 s |
| g(153, 37) | `54f22cd411ce96a7...` | 19.46M | 2272 MB | 1266 s |
| g(154, 37) | `0021968ebc1d353d...` | 16.16M | 1830 MB | 976 s |
| g(148, 38) | `b1e24788b7009bd0...` | 5.48M | 495 MB | 335 s |
| g(149, 38) | `ad9ee92eb97c11e1...` | 6.02M | 559 MB | 239 s |
| g(150, 38) | `9dcfec4ae5f73759...` | 5.96M | 541 MB | 408 s |
| g(151, 38) | `3be571b5b80901eb...` | 6.06M | 565 MB | 378 s |
| g(152, 38) | `68ba61b0908840d7...` | 6.18M | 592 MB | 243 s |
| g(153, 38) | `39b4f540f80bc9fd...` | 7.35M | 726 MB | 440 s |
| g(154, 38) | `aaa28f3830f42976...` | 7.15M | 690 MB | 297 s |
| g(148, 39) | `189fef22cdb642fd...` | 3.28M | 267 MB | 294 s |
| g(149, 39) | `39929b63e17f637c...` | 3.53M | 292 MB | 147 s |
| g(150, 39) | `65e5c529ca66b61e...` | 3.68M | 297 MB | 142 s |
| g(151, 39) | `bf639be3cb11962a...` | 3.76M | 315 MB | 202 s |
| g(152, 39) | `ed8b1023ff44b1d0...` | 3.79M | 317 MB | 221 s |
| g(153, 39) | `661c9a293998c42b...` | 4.30M | 382 MB | 251 s |
| g(154, 39) | `e3ea6c4ceadeab80...` | 4.29M | 380 MB | 177 s |

**Other classes at n = 538.**

| class | result | cost | status |
|---|---|---|---|
| palindromic, frame g(151, 38) without the solid middle (`--no-middle`) | UNSAT | 215 s, 6.05M conflicts | certified (CNF `d21429f362c72dec...`, 571 MB proof, drat-trim 219 s) |
| palindromic, color-6 frame only (`--frame6 151 --order 5`) | unknown | 803 s, stopped at the 1,500 s wall limit | — |
| any 6-coloring that agrees with `published_537.col` on `[1,150]` | UNSAT | 1.7 s, 13k conflicts | certified; proof stored, checked in CI |
| any 6-coloring that agrees with `published_537.col` on `[1,120]` | UNSAT | 54 s, 0.95M conflicts | certified (CNF `ef261df813a4f9d6...`, 66 MB proof, drat-trim 62 s) |
| any 6-coloring that agrees with `published_537.col` on `[1,100]` or `[1,80]` | unknown | 153 s and 144 s, stopped at the 300 s wall limit | — |

All 21 grid cells are certified: no palindromic sum-free 6-partition of
`[1,538]` lies in our `N = 539` frame g(Q, D) for any `148 <= Q <= 154` and
`37 <= D <= 39`.  This grid contains the paper's own parameters `(151, 38)`
moved to `N = 539`, but the frame is only one family of palindromic colorings,
so the grid says nothing about palindromic colorings outside it.  The
`--no-middle` class contains g(151, 38) and is also empty.  The `[1,120]` row
says: no sum-free 6-partition of `[1,538]`, palindromic or not, induces on
`[1,120]` the same set partition as `published_537.col` (whose restriction to
`[1,120]` uses five classes, since `min C6 = 151`); this implies the `[1,150]`
row, which is kept because its proof is small enough to store and check in CI.
The CNF fixes colors as numbered in the file, but no other clause
distinguishes colors in this class, so the result covers every renaming of
colors.  The two classes above are re-certified by `certify_templates.sh`
together with the grid.

Reproduction (from `problems/schur-6`):

```bash
# CI-checked certificate (about 2 s + 1 s + 53 s CPU for drat-trim):
python3 template_sat.py cnf --maximum 538 --fix published_537.col 150 \
  > /tmp/schur6_prefix150.cnf
python3 audit_template_cnf.py /tmp/schur6_prefix150.cnf --maximum 538 \
  --fix published_537.col 150 \
  --sha256 11747b52a391cacffa8235ccdec8d8e61574ec4b22e39b05887f44d686e1bca5
drat-trim /tmp/schur6_prefix150.cnf prefix150_538_unsat.drat
# The 21 grid cells, the --no-middle class and the [1,120] class (local only;
# per class 1-17 min kissat CPU, 1-24 min of drat-trim and a 0.07-2.3 GB
# temporary proof; about 5 h for all 23 in sequence):
bash certify_templates.sh          # or --audit-only for the fast audit part
# Rediscover a 537 partition in the published frame (about 2 min):
python3 template_sat.py cnf --maximum 537 --palindromic --frame 151 38 > /tmp/f.cnf
kissat /tmp/f.cnf > /tmp/f.out
python3 template_sat.py decode --maximum 537 --palindromic /tmp/f.out > /tmp/f.col
python3 verify.py /tmp/f.col --maximum 537
```

`prefix150_538_unsat.drat` (1.9 MB, text DRAT, 38,906 lemma lines) is the
core-trimmed form (`drat-trim -l`) of kissat's 4.8 MB binary proof.  Both
versions verify; on the trimmed one drat-trim reports 37,624 core lemmas,
14,424 of them RAT, and 19,851 of the 434,854 input clauses in the core.  A
truncated copy of the proof is rejected (`s NOT VERIFIED`).  Kissat runs with other seeds or versions need not
reproduce the same proof or conflict counts.

### Local search toward 538

`tabu_search.cpp` (C++17, standard library only) recolors one position at a
time to minimise the number of violated Schur "cells" (the position set of a
triple `x+y = z`; folded positions with `--palindromic`).  A recolored position
may not return to its old color for a randomised tabu tenure, with aspiration
on new bests.  With `--breakout` the objective is a weighted count: at every
local minimum the weight of each violated cell grows by one (Morris' breakout
method), and all weights are halved every 1,000 such bumps.  Frame options
match `template_sat.py`.

Calibration on a class known to be satisfiable (palindromic `[1,537]` in frame
g(151, 38), which kissat solves in 106 s) shows that this local search is much
weaker than CDCL here: plain tabu stopped at 8 violated cells after 120 s, and
breakout at 2 violated cells after 600 s (46.3M moves).  Neither found a
solution, so local-search failure at 538 is weak evidence.

Runs at 538 (two threads, 8 breakout starts of 300 s each per thread, on a
heavily loaded machine):

| class | starts | moves | best in every start |
|---|---|---|---|
| palindromic, frame g(151, 37), random starts (this class was later certified empty, see the grid) | 8 | 173.0M | 2 violated cells (5 triples on `[1,538]`) |
| unrestricted `[1,538]`, started from published F1.001, F1.034, F2.001, F3.001, F4.001, F5.001 and from `frame_537_kissat.col`, `near_537_two_violations.col` | 8 | 114.7M | 2 violated triples |

All 17 best colorings (these 16 and the calibration run) have the same shape.
One class contains `a`, `2a` and `3a`, and the only violations are `a+a = 2a`
and `a+2a = 3a`; the observed values are `a` = 1, 2, 3, 5, 6, 12, 16, 27 and
38.  The 2026-08-11 near coloring of `[1,537]` (`12, 24, 36`) has the same
shape.  This is an observation about the search, not a theorem.
`near_538_two_violations.col` stores one such coloring of `[1,538]`
(`12+12 = 24`, `12+24 = 36`) as data for future searches; it certifies nothing.

```bash
g++ -O3 -std=c++17 tabu_search.cpp -o /tmp/schur6_tabu
/tmp/schur6_tabu --maximum 538 --palindromic --frame 151 37 --breakout \
  --seed 1 --seconds 300 --output /tmp/near538.col
/tmp/schur6_check /tmp/near538.col 538
/tmp/schur6_check near_538_two_violations.col 538   # monochromatic_triples=2
```

Runs stop on wall time, so the move counts and final colorings depend on the
machine load and are not bit-reproducible.

### What is not claimed

- No sum-free 6-partition of `[1,538]` was found; `S(6) >= 538` is not
  established.  `S(6) >= 537` is the result of Chen, Zhu and Long, re-verified
  here.
- The 538 exclusions cover only the stated classes: palindromic colorings in
  the listed frames (and the `--no-middle` relaxation of g(151, 38)), and
  colorings that agree with `published_537.col` on `[1,120]`.  They say
  nothing about general partitions of `[1,538]`, and the frame classes depend
  on our extrapolation of the paper's frame to `N = 539`.
- The frame classes are certified only by local runs of
  `certify_templates.sh` (proofs of up to 2.3 GB are not stored); CI
  re-checks their CNF audits and SHA-256 pins, and the stored `[1,150]` proof.
- No novelty is claimed for any 538 exclusion; the paper does not report
  whether its authors tried 538.
