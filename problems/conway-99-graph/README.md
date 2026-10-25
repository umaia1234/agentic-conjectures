**English** | [한국어](README.ko.md)

# Conway 99-graph

Status checked as of: 2026-08-11.

## Problem

The question is whether a strongly regular graph

```text
srg(99,14,1,2)
```

exists. That is, it is the existence problem of a graph with 99 vertices in
which every vertex has degree 14, any two adjacent vertices have 1 common
neighbor, and any two non-adjacent vertices have 2 common neighbors.
Equivalently, every edge lies in exactly one triangle and every non-edge
lies in exactly one 4-cycle.

## Current status and known partial results

A 2025 peer-reviewed paper also explicitly states this existence problem as
unresolved. Writing `G` for the automorphism group of a putative graph, that
paper proved the following without computer assistance.

- If `2 | |G|`, then `|G| | 6`.
- If `7 | |G|`, then `G` is the cyclic group `Z_7`.

It contains no new computational result deciding existence or nonexistence.
This document records the statement as a candidate for future computational
search and the restrictions already known.

## Computational perspective

Fixing one vertex, the remaining vertices decompose by distance layers as
`1 + 14 + 84`. Regularity, the common-neighbor equations, and canonical
augmentation can be fed directly into SAT, integer programming, or
exhaustive search. However, since the actual graph may have almost no
symmetry, ruling out subspaces that assume a large automorphism group cannot
by itself resolve the whole problem.

## Symmetric subcases: SAT/DRAT exclusions (2026-10-24)

**Result (computer-checked, partial).** Let `Γ` be an srg(99,14,1,2) and `t`
an automorphism of order 2. Then `t` fixes exactly 1, 3, 5, 7 or 9 vertices.
In detail: for each of the ten local involution types with `F >= 11` fixed
vertices in the table below, the CNF "some srg(99,14,1,2) on the rooted frame
is invariant under this involution" is unsatisfiable, and CaDiCaL's DRAT
proof is verified by `drat-trim`. CI re-checks these ten proofs. Eight of the
ten types (`F >= 19`) are also excluded by the elementary interlacing bound
`F <= 18` derived below, so for them the SAT runs are only consistency
checks. The two types with `F = 11` and `F = 13` are the part not covered by
that bound.

In addition, the type `(d, e) = (0, 2)` with `F = 9` is unsatisfiable. In
this type the involution fixes two edges of the matching `Γ1(x)` pointwise
and flips the other five. CaDiCaL took 1061 s, and drat-trim verified the
549 MB proof locally. Its core proof (105 MB) is too large to commit, so CI
does not re-check this type. `certify_case.py` regenerates it (see
"Reproduction"). The only other type with `F = 9` is `(3, 1)`, so an
involution fixing 9 vertices has type `(3, 1)` at every fixed vertex `x`. It
swaps three pairs of edges of the matching `Γ1(x)` and fixes the seventh
edge pointwise.

We did not find these statements in the sources listed under "Literature",
but we did not consult the full texts of Behbahani–Lam (2011),
Makhnev–Minakova (2004) or Wilbrink (1984), so no novelty is claimed. The
same pipeline reproduces known exclusions as consistency checks (labelled
"reproduction" below). Nothing here decides existence. The other eight
involution types (`F <= 9`) and the fixed-point-free automorphisms of order 3
are still open. The runs listed below return UNKNOWN for them.

### Which symmetry types have to be considered

Write `A` for the adjacency matrix. Then `A^2 + A - 12I = 2J`, so the
eigenvalues are 14 (once), 3 and -4. Their multiplicities `f, g` satisfy
`f + g = 98` and `14 + 3f - 4g = tr A = 0`, so they are 54 and 44.

*Trace conditions.* Let an automorphism `g` have permutation matrix `P`, with
`F = tr P` fixed vertices and `α1 = tr(PA) = #{x : x^g ~ x}`. `P` commutes
with `A`, so it preserves the eigenspaces. Let `χ1, χ2` be its traces on the
eigenspaces for 3 and -4. Then `F = 1 + χ1 + χ2` and
`α1 = 14 + 3χ1 - 4χ2`, so

```text
χ1 = (4F + α1 - 18)/7,    χ2 = (3F - α1 + 11)/7
```

are integers. If `g` has prime order `p`, then on an eigenspace of dimension
`d` it has eigenvalue 1 with some multiplicity `a`, and every primitive
`p`-th root of unity with a common multiplicity `b`. Hence `χ = a - b`,
`χ ≡ d (mod p)` and `-d/(p-1) <= χ <= d`. In particular `χ1 ≡ 54` and
`χ2 ≡ 44 (mod p)`. For `p = 2` these conditions say only that
`α1 ≡ 18 - 4F (mod 14)` (and `F` is odd because 99 is odd), so they do not
bound `F`.

*Fixed-point bound.* Let `g ≠ 1` fix the set `Φ`, with `|Φ| = F >= 1`, and
let `N` be the other `99 - F` vertices. A fixed neighbour of `x ∈ N` is a
common neighbour of `x` and `x^g ≠ x`, so `x` has at most `max(λ, μ) = 2`
fixed neighbours. Let `c <= 2` be the average number of fixed neighbours of a
vertex of `N`, and `a` the average degree inside `Φ`. The quotient matrix of
the partition `{Φ, N}` has eigenvalues 14 and `a - c`. By interlacing,
`a - c <= 3`, the second eigenvalue of `A`. Counting the edges between `Φ`
and `N` gives `F(14 - a) = (99 - F)c`. Hence `F(11 - c) <= (99 - F)c`, that
is `11F <= 99c <= 198`, and so `F <= 18`.

*Root-fixing automorphisms.* Fix a vertex `x`. Because `λ = 1`, `Γ1(x)` is a
perfect matching of 7 edges. Each vertex of `Γ2(x)` has exactly two
neighbours in `Γ1(x)`, and they are non-adjacent (`λ = 1`). Different
vertices give different pairs (`μ = 2`). There are 84 of each, so this is a
bijection. The encoder therefore fixes this *rooted frame*: root 0,
`Γ1 = {1..14}` with matching `{2i-1, 2i}`, and `Γ2` labelled by the
non-adjacent pairs in lexicographic order. An automorphism fixing `x` is
determined by its action `σ` on `Γ1(x)`, which is an element of the
hyperoctahedral group `Z2 ≀ S7` (order `2^11·3^2·5·7`) preserving the
matching. Conjugate `σ` give relabelled, equisatisfiable CNFs. This gives
the following cases for prime order `p`:

- `p >= 11`: `p` does not divide `|Z2 ≀ S7|`, so an automorphism of order
  `p` that fixes a vertex acts trivially on `Γ1` and `Γ2`, which is
  impossible. Hence it fixes no vertex, `p | 99` and `p = 11`, with cycle
  type `11^9` (case `p11-free`).
- `p = 7`: `F ≡ 1 (mod 7)`, so a vertex is fixed, and `σ` is a positive
  7-cycle on the matching edges (`F = 1`, case `p7-root`).
- `p = 5`: `F ≡ 4 (mod 5)`, so a vertex is fixed, and `σ` is a positive
  5-cycle fixing the other two edges pointwise (`F = 9`, case `p5-root`).
- `p = 3`: `σ` is one or two positive 3-cycles with the remaining edges
  fixed pointwise (`F = 33` or `F = 3`, cases `p3-root-a`, `p3-root-b`), or
  `g` is fixed-point-free with cycle type `3^33` (case `p3-free`).
- `p = 2`: since 99 is odd, every involution fixes a vertex. Up to
  conjugacy, `σ` swaps `d` pairs of matching edges, fixes `e` edges
  pointwise and flips the remaining `7 - 2d - e`. It fixes
  `F = 1 + 2e^2 + 2d` vertices. There are 19 non-identity types `(d, e)`
  (cases `p2-d<d>-e<e>`). By the bound above only the 11 types with
  `F <= 18` can occur.

### Encoding specification

`symmetric/srg_sym_encode.py` (standard library only) writes, for a group
`G` given by generators, the CNF "there is an srg(v,k,λ,μ) on `{0..v-1}`
invariant under `G`" (plus the rooted frame for rooted cases):

1. Variables `1..m` are the `G`-orbits on unordered vertex pairs, numbered
   by increasing least pair index `x·v + y` (`x < y`). Variables `m+1..` are AND
   gates `t = e_A ∧ e_B` for the needed sorted pairs `(A, B)`, `A < B`, in
   increasing order.
2. Constraint blocks: for each vertex-orbit representative `x` (ascending),
   `Σ_{y≠x} e(x,y) = k`. Then, for each pair-orbit representative `(x, y)`
   (ascending), the literals `e(x,z) ∧ e(y,z)` for `z ∉ {x, y}` ascending
   (the variable itself when both pairs lie in one orbit, else the AND
   gate), followed by `μ - λ` copies of `e(x,y)` (or `λ - μ` copies of
   `¬e(x,y)`), with sum exactly `max(λ, μ)`. This one equation states
   `λ = 1` for edges and `μ = 2` for non-edges.
3. Each block of `N` literals and bound `K` uses a full sequential counter.
   The variables `s(i,j)` mean "at least `j` of the first `i` literals are
   true" (`j <= min(i, K+1)`, numbered by `i` then `j`). The clauses per
   cell are `s(i-1,j) → s(i,j)`, `s(i-1,j-1) ∧ l_i → s(i,j)`,
   `s(i,j) → s(i-1,j) ∨ l_i` and `s(i,j) → s(i-1,j-1)`. Here `s(i-1,0)` is
   read as true and a missing `s(i-1,j)` as false, and clauses that mention
   only such constants are simplified. The block ends with the units
   `s(N,K)` and `¬s(N,K+1)` (the latter only if `K+1 <= N`).
4. Clause order: frame units (by variable), AND triples
   `[¬t,a] [¬t,b] [t,¬a,¬b]`, then the counter clauses block by block
   (cells by `i` then `j`, the four clause kinds in the order listed).
   DIMACS output: header `p cnf V C`, one clause per line ending in ` 0`.

All auxiliary variables are functionally defined, so a `G`-invariant
srg(99,14,1,2) on the frame gives a model. An UNSAT answer therefore
excludes the type. `symmetric/srg_sym_audit.py` does not import the encoder.
It rebuilds the group by closure, recomputes the generator invariants
(order, fixed points, cycle type, signed action on the matching, frame
invariance), derives the DIMACS bytes again and compares their SHA-256 with
`cases.json`.

### Results

All runs are from 2026-10-24 and used `certify_case.py` with CaDiCaL 3.0.1
(default options, binary DRAT) and drat-trim. `F` is the number of fixed
vertices. Times are wall-clock times on an Apple M5 Max shared with other
jobs. `> L s` means that CaDiCaL stopped at its time limit `L` without an
answer (UNKNOWN). The UNSAT rows other than `(0, 2)` have their core proofs
and clause cores in `symmetric/certs/`. `symmetric/results/<case>.json` and
`symmetric/logs/<case>.log` hold the solver and drat-trim output (with the
local build directory written as `BUILD/`).

Involutions fixing the root (`σ` swaps `d` pairs of matching edges and fixes
`e` edges pointwise):

| `(d, e)` | `F` | pair orbits | clauses | result | CaDiCaL | drat-trim (full / core proof) | core proof, xz |
|---|---|---|---|---|---|---|---|
| `(0, 6)` | 73 | 3746 | 5,417,579 | UNSAT, DRAT verified | 1.3 s | 4.6 s / 3.3 s | 2.6 kB |
| `(1, 5)` | 53 | 3126 | 4,505,079 | UNSAT, DRAT verified | 1.6 s | 5.9 s / 3.9 s | 12.9 kB |
| `(0, 5)` | 51 | 3075 | 4,431,622 | UNSAT, DRAT verified | 1.5 s | 5.9 s / 4.3 s | 27.4 kB |
| `(1, 4)` | 35 | 2739 | 3,956,262 | UNSAT, DRAT verified | 10.0 s | 17.8 s / 13.7 s | 107.7 kB |
| `(0, 4)` | 33 | 2706 | 3,910,617 | UNSAT, DRAT verified | 4.8 s | 7.6 s / 5.7 s | 69.9 kB |
| `(2, 3)` | 23 | 2571 | 3,727,018 | UNSAT, DRAT verified | 10.8 s | 38.1 s / 35.9 s | 319.2 kB |
| `(1, 3)` | 21 | 2550 | 3,699,105 | UNSAT, DRAT verified | 10.5 s | 33.3 s / 29.1 s | 255.5 kB |
| `(0, 3)` | 19 | 2531 | 3,674,084 | UNSAT, DRAT verified | 3.5 s | 5.4 s / 4.2 s | 41.0 kB |
| `(2, 2)` | 13 | 2486 | 3,616,187 | UNSAT, DRAT verified | 3.0 s | 6.3 s / 5.0 s | 71.7 kB |
| `(1, 2)` | 11 | 2475 | 3,602,556 | UNSAT, DRAT verified | 2.5 s | 6.1 s / 4.7 s | 50.6 kB |
| `(0, 2)` | 9 | 2466 | 3,591,727 | UNSAT, DRAT verified locally | 1061.3 s | 1465.1 s / 1263.0 s | not committed (28.44 MB) |
| `(3, 1)` | 9 | 2466 | 3,591,723 | UNKNOWN | > 1800 s | - | - |
| `(2, 1)` | 7 | 2459 | 3,583,680 | UNKNOWN | > 600 s | - | - |
| `(3, 0)` | 7 | 2459 | 3,583,676 | UNKNOWN | > 600 s | - | - |
| `(1, 1)` | 5 | 2454 | 3,578,403 | UNKNOWN | > 600 s | - | - |
| `(2, 0)` | 5 | 2454 | 3,578,401 | UNKNOWN | > 600 s | - | - |
| `(0, 1)` | 3 | 2451 | 3,575,874 | UNKNOWN | > 600 s | - | - |
| `(1, 0)` | 3 | 2451 | 3,575,874 | UNKNOWN | > 600 s | - | - |
| `(0, 0)` | 1 | 2450 | 3,576,077 | UNKNOWN | > 600 s | - | - |

Other prime orders. `p3-root-a` (`F = 33`) is also excluded by the
interlacing bound.

| case | action on `Γ1` or cycle type | `F` | literature | pair orbits | clauses | result | CaDiCaL | core proof, xz |
|---|---|---|---|---|---|---|---|---|
| `p11-free` | cycle type `11^9` | 0 | reproduction | 441 | 627,372 | UNKNOWN | > 1800 s | - |
| `p7-root` | positive 7-cycle on the 7 matching edges | 1 | reproduction | 693 | 1,000,545 | UNKNOWN | > 1800 s | - |
| `p5-root` | positive 5-cycle, 2 edges fixed pointwise | 9 | reproduction | 999 | 1,459,080 | UNKNOWN | > 1800 s | - |
| `p3-root-a` | one positive 3-cycle, 4 edges fixed pointwise | 33 | reproduction | 1969 | 2,838,689 | UNSAT, DRAT verified | 2.1 s | 28.6 kB |
| `p3-root-b` | two positive 3-cycles, 1 edge fixed pointwise | 3 | reproduction | 1619 | 2,359,468 | UNKNOWN | > 1800 s | - |
| `p3-free` | cycle type `3^33` | 0 | open | 1617 | 2,354,814 | UNKNOWN | > 1800 s | - |

### Validation of the encoder

`symmetric/validate_encoder.py` was run on 2026-10-24. It took 900 s in
total, about 14 minutes of which is the srg(243,22,1,2) solve.

- Part A (no solver, `--semantic-only`, under 1 s). For known graphs, the
  assignment read off the graph satisfies every clause (auxiliary variables
  are computed by unit propagation). The graphs are: Paley(9) on its rooted
  frame under each of five root-fixing permutations that is an
  automorphism; the Berlekamp–van Lint–Seidel srg(243,22,1,2) on its rooted
  frame under a group of order 110 fixing the root; and 40 automorphisms
  each of the Petersen, Clebsch and Shrikhande graphs. This is the soundness
  direction that the UNSAT claims rely on. It also exhibits an explicit
  model of the srg(243,22,1,2) frame CNF.
- Part B (CaDiCaL). For every cycle type of `S_n`, the CNF for one
  permutation of that type must be SAT exactly when a listed graph has an
  automorphism of that type. Checked: Paley(9), 30 cycle types (6 SAT);
  Petersen, 42 (7 SAT); Paley(13), 101 (5 SAT); Clebsch, 231 (12 SAT);
  srg(16,6,2,2) (rook graph and Shrikhande), 231 (13 SAT). Rooted frames
  with the trivial group: srg(9,4,1,2) is SAT, while srg(19,6,1,2) and
  srg(33,8,1,2) are UNSAT (these parameter sets are infeasible). BvLS under
  the order-110 group is SAT. Every SAT model was decoded and checked as an
  invariant srg.

### Reproduction

From `problems/conway-99-graph/symmetric` (standard-library Python 3;
measured on an Apple M5 Max, 2026-10-24):

```sh
python3 srg_sym_audit.py               # group data + CNF hashes, all 25 cases (about 25 s)
python3 verify_certificates.py         # drat-trim on the 11 clause cores (about 15 s)
python3 verify_certificates.py --full  # the same proofs against the full CNFs (about 95 s)
python3 validate_encoder.py --semantic-only   # Part A (under 1 s)
python3 validate_encoder.py            # Parts A and B, needs cadical (900 s)
python3 srg_sym_encode.py cnf p2-d1-e2 -o /tmp/p2-d1-e2.cnf   # one CNF (about 5 s)
python3 certify_case.py p2-d1-e2 --build /tmp/c99 --out /tmp/c99 --limit 5400   # whole pipeline, about 25 s
python3 certify_case.py p2-d0-e2 --build /tmp/c99 --out /tmp/c99 --limit 5400   # type (0, 2), about 65 min
```

`certify_case.py` writes the CNF and audits it byte for byte. It then runs
`cadical -t LIMIT CNF PROOF` (CaDiCaL 3.0.1, binary DRAT). On UNSAT it runs
`drat-trim CNF PROOF -i -l CORE -C` and then `drat-trim CNF CORE -i -c
CLAUSES`, and writes `<case>.core.drat.xz` and `<case>.clause-core.txt.xz`
to the build directory. The committed copies are in `certs/`. It exits with
status 0 only if both drat-trim runs print `s VERIFIED`. Without `--out` it
overwrites `results/<case>.json` and `logs/<case>.log`. Running it a second
time on the eleven fast UNSAT cases reproduced byte-identical core proofs.
For `(0, 2)`, `cases.json` records the SHA-256 of the full proof, the core
proof and the clause core, so a regenerated proof can be compared. `drat-trim`
prints its usual warnings about ignored unit deletions in backward mode;
every core lemma is RUP (0 RAT lemmas). CNFs (11–109 MB) and full proofs
(22–71 MB, and 549 MB for `(0, 2)`) are not committed.

### Literature and labels

- Wilbrink (1984), as cited by Cesarz–Woldar: `Γ` is not vertex-transitive.
- Makhnev–Minakova (2004), as cited by Cesarz–Woldar: `|Aut Γ|` divides
  `2·3^3·7·11`.
- Behbahani–Lam (2011), as stated in Crnković–Maksimović (2020, Theorem
  7.1): the only possible prime divisors of `|Aut Γ|` are 2 and 3, and an
  automorphism of order 3 has no fixed points. This covers our cases
  `p11-free`, `p7-root`, `p5-root`, `p3-root-a` and `p3-root-b`.
- Crnković–Maksimović (2020): no automorphism group of order 6 or 9 (`Z6`,
  `S3`, `Z9`, `E9`).
- Cesarz–Woldar (2025): computer-free proofs that `2 | |G|` implies
  `|G| | 6` and that `7 | |G|` implies `G ≅ Z7`.
- Thakkar–Severini (arXiv:2608.11211, 2026): with CP-SAT, the
  single-fixed-point `Z7` model was still UNKNOWN after 48 h on 14 cores,
  and the fixed-point-free `Z3` model was UNKNOWN within 1800 s.
- arXiv:2610.16266 (unrefereed, 2026) claims nonexistence via a
  sum-of-squares triangle bound. It is not checked or used here.

We found no exclusion of involutions by fixed-point count in these sources.
Involutions themselves are not excluded in the literature we read. In the
tables, "reproduction" marks cases that the cited results already exclude,
and "open" marks cases that we did not find excluded.

### What is not claimed

- Existence or nonexistence of srg(99,14,1,2), or of one with an involution.
  Eight involution types (`F ∈ {1,3,5,7}`, and `(3, 1)` with `F = 9`) and
  fixed-point-free order 3 remain open here.
- A CI-checked exclusion of type `(0, 2)`. Its proof was verified locally,
  but it is not committed.
- Any novelty. The interlacing bound is elementary, and the excluded types
  may be covered by literature we did not read.
- Composite groups beyond the cited results were not encoded.
- UNKNOWN entries are timeouts, not evidence either way.

## FormalConjectures upstream

The [local upstream snapshot](upstream/README.md) preserves the exact Lean
statement for 99 vertices and the pinned commit information. That file is a
problem statement containing `sorry`, and the status survey here likewise
does not decide existence or nonexistence.

## Evidence

- H. A. Wilbrink, On the (99,14,1,2) strongly regular graph, in *Papers
  dedicated to J. J. Seidel*, Eindhoven Univ. Tech. Report 84-WSK-03 (1984),
  342--355 (not consulted).
- A. A. Makhnev and I. M. Minakova, On automorphisms of strongly regular
  graphs with parameters λ = 1, μ = 2, *Diskret. Mat.* 16 (2004), no. 1,
  95--104 (not consulted).
- M. Behbahani and C. Lam,
  [Strongly regular graphs with non-trivial automorphisms](https://doi.org/10.1016/j.disc.2010.10.005),
  *Discrete Math.* 311 (2011), 132--144 (not consulted; cited via
  Crnković–Maksimović).
- D. Crnković and M. Maksimović, Construction of strongly regular graphs
  having an automorphism group of composite order, *Contrib. Discrete Math.*
  15 (2020), no. 1, 22--41.
- A. Thakkar and S. Severini,
  [A forced-structure reduction and verifiable bounds for Conway's 99-graph](https://arxiv.org/abs/2608.11211),
  arXiv:2608.11211 (2026).
- M. Cesarz and A. Woldar,
  [On the automorphism group of a putative Conway 99-graph](https://alco.centre-mersenne.org/articles/10.5802/alco.418/),
  *Algebraic Combinatorics* 8 (2025), 379--398.
