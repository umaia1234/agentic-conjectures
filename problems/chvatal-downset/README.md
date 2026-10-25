# Chvatal downset conjecture: SAT reductions with DRAT certificates

**English** | [한국어](README.ko.md)

This directory records a bounded computational attack on Chvatal's
conjecture for intersecting subfamilies of downsets.  It does **not** claim a
new case of the conjecture: the certified exclusions for ground sets with at
most seven elements reproduce a published theorem, and the eight-element case
is not settled here.

## Statement

For a finite downset `D` (if `A in D` and `B subseteq A`, then `B in D`), let

- `alpha(D)` be the largest size of a pairwise-intersecting subfamily of `D`;
- `Delta(D) = max_i |{A in D : i in A}|` be the size of its largest star.

Chvatal's conjecture is

```text
alpha(D) <= Delta(D) for every finite downset D.
```

The general conjecture remains open.  A certificate-producing integer
programming computation proves it when the ground set has at most seven
elements.  The same paper reports only a floating-point solve for eight
elements:

- L. Eifler, A. Gleixner, J. Pulaj, *A Safe Computational Framework for
  Integer Programming Applied to Chvatal's Conjecture*, ACM TOMS 48 (2022),
  <https://doi.org/10.1145/3485630> (below: EGP).
- Preprint and public computational description:
  <https://optimization-online.org/2018/09/6802/>.

## Results

| Ground set | CNF | Outcome | Assumptions beyond the proofs below |
|---|---|---|---|
| 6 elements | `generate_cnf.py --n 6 --reduced --encoding cardnet` | UNSAT, DRAT proof accepted by drat-trim | Kleitman-Magnanti, Sterboul, conjecture for 5 elements, PySAT's cardinality network |
| 3 to 7 elements | `generate_rank_cnf.py`, every rank `3 <= r <= n` (15 CNFs) | all UNSAT, DRAT proofs accepted by drat-trim | Kleitman-Magnanti |
| 8 elements | `generate_rank_cnf.py`, ranks 3, 7, 8 | UNSAT, DRAT proofs accepted by drat-trim | Kleitman-Magnanti |
| 8 elements | `generate_rank_cnf.py`, ranks 4, 5, 6 | undecided: bounded runs stopped without a result | |

Together with the reduction proved below, the rank-split certificates show:
**Chvatal's conjecture holds for every downset on a ground set with at most
seven elements**, assuming the Kleitman-Magnanti theorem.  This is a
certified reproduction, by SAT and DRAT instead of exact MILP, of the
`n <= 7` theorem of EGP; it is not new.  For eight elements it shows only
that a counterexample with the fewest sets would have rank (largest member
size) 4, 5 or 6.

The mathematical reductions below are informal proofs (not Lean).  The CNF
generators are trusted code: `generate_rank_cnf.py` uses only the Python
standard library and its `--self-test` checks the encoding against brute
force; `generate_cnf.py` builds its cardinality constraints with PySAT.

## Saturation lemma

The following reduction is elementary, but it is useful in a SAT search.

**Lemma.** If Chvatal's conjecture has a counterexample, then it has a
counterexample `(D, Y)` such that

1. `D = down(Y) := {S : S subseteq T for some T in Y}`;
2. `Y` is a maximum-cardinality intersecting subfamily of `D`;
3. for every `T in D \ Y`, some `S in Y` is disjoint from `T`.

**Proof.** Start with a counterexample `D0` and choose a maximum-cardinality
intersecting subfamily `Y` of `D0`.  Put `D = down(Y)`.  Because `D0` is a
downset and `Y subseteq D0`, we have `Y subseteq D subseteq D0`.  Passing from
`D0` to `D` cannot increase any star, while it leaves `|Y|` unchanged.
Consequently `|Y| > Delta(D0) >= Delta(D)`, so `(D, Y)` is still a
counterexample.  Any intersecting subfamily of `D` is also one of `D0`, hence
`Y` remains maximum in `D`.  Finally, if `T in D \ Y` met every member of
`Y`, then `Y union {T}` would be an intersecting subfamily of `D` larger than
`Y`, a contradiction.  This proves all three assertions.  QED.

## The original reduced encoding (`generate_cnf.py`)

In Boolean variables `x_T = [T in D]` and `y_T = [T in Y]`, assertion 3 of
the lemma is the clause

```text
not x_T or y_T or (or_{S intersect T = empty, S nonempty} y_S).
```

Assertion 1 is encoded in both directions:

```text
y_T -> x_S                         for every S subseteq T,
x_S -> or_{T superseteq S} y_T.
```

For each ground element `i`, the strict counterexample inequality
`|Y| >= |star_i(D)| + 1` is encoded as the cardinality constraint

```text
sum_{S nonempty} y_S + sum_{S contains i} (not x_S) >= 2^(n-1) + 1.
```

### Why each reduction is sound for `n = 6`

Assume the conjecture for ground sets with at most five elements (EGP,
Proposition 3, or the rank-split chain below) and let `D0` be a counterexample
on `{0, ..., 5}`.  Choose a maximum intersecting `Y subseteq D0` and put
`D = down(Y)`.  Every clause holds for `(D, Y)`:

1. `Y` pairwise intersecting, `D = down(Y)`, saturation: the lemma.
2. `y_{} = 0` and `x_{} = 1`: the empty set meets nothing, and `Y` is
   nonempty because `|Y| > Delta(D) >= 0`.
3. `y_S = 0` for `1 <= |S| <= 2` (EGP, Corollary 3): if `S in Y` and
   `S subseteq {a, b}`, every member of `Y` meets `S`, so `Y` lies in the union
   of the stars of `a` and `b`.  By the Kleitman-Magnanti theorem (EGP,
   Theorem 5: "Any intersecting family that is contained in the union of two
   stars generates a downset that satisfies Conjecture 1") the downset
   `D = down(Y)` satisfies the conjecture, contradicting `|Y| > Delta(D)`.
4. `x_{i} = 1` for every element (EGP, Proposition 4): if `{i}` is not in
   `D`, no member of `D` contains `i`, and `D` is a counterexample on five
   elements.
5. `x_{0,1,2,3} = 1` (EGP, Proposition 5): by Sterboul's theorem the
   conjecture holds for downsets whose members have at most three elements,
   so `D` has a member with at least four elements.  A 4-subset of it is in
   `D`; relabel the ground set so that it is `{0, 1, 2, 3}`.  Every other
   constraint is invariant under relabelling.
6. Cardinality: for element `i` there are 63 literals `y_S` and 32 literals
   `not x_S`; exactly `|Y| + 32 - |star_i(D)|` of them are true, and this is
   at least 33 exactly when `|Y| >= |star_i(D)| + 1`.

So every six-element counterexample yields values of the primary variables
satisfying all clauses written by the script.  The only auxiliary variables
come from PySAT's `CardEnc.atleast(..., encoding=cardnetwrk)`; that every
such assignment extends to them (completeness of the cardinality network) is
trusted from PySAT and is **not** tested here.  This is why the rank-split
encoding below writes its own counters.

### DRAT certificate for `n = 6`

`generate_cnf.py --solve --proof PATH` now writes the DRAT trace of PySAT's
solver.  The CNF has 16,238 variables and 25,356 clauses, SHA256
`f8d119eac17820ae405c590c13aa4fae93b8cf787faa21092f90a1384858f2eb`
(python-sat 1.9.dev17).  Measured on a shared 18-core machine:

- PySAT CaDiCaL 1.9.5: UNSAT after 156,925 conflicts; building the CNF,
  solving and writing the 41.3 MB text DRAT took 14.4 s, and drat-trim
  printed `s VERIFIED` after 12.5 s.
- standalone CaDiCaL 3.0.1: UNSAT after 161,702 conflicts (3.3 s), 13.6 MB
  binary DRAT; drat-trim `s VERIFIED` in 3.3 s.

The proofs are too large to commit;
`certify_drat.py repo-n6` regenerates the CNF, compares its SHA256 with
[`drat_manifest.json`](drat_manifest.json), obtains the PySAT proof and runs
drat-trim.  `n6_solver_result.json` is the earlier run without a proof and is
kept as a record.

The same encoding for `n = 7` was stopped after 1015.6 s of CaDiCaL 3.0.1 CPU
time and 11,613,975 conflicts without a result; the rank-split encoding
replaces it.

## The rank-split encoding (`generate_rank_cnf.py`)

For a ground set `{0, ..., n-1}` and a rank `r` with `3 <= r <= n`, the CNF
is satisfiable exactly when some `(D, Y)` satisfies

1. `Y` is intersecting and every member of `Y` has at least three elements;
2. `D = down(Y)`;
3. saturation: every `T in D \ Y` is disjoint from some member of `Y`;
4. every singleton is in `D`;
5. `|Y| >= |star_i(D)| + 1` for every element `i`;
6. minimality: `Tight := {i : |star_i(D)| = |Y| - 1}` is not in `D`;
7. rank: `{0, ..., r-1}` is in `D` and no `(r+1)`-set is in `D`;
8. symmetry: inside each block `{0, ..., r-1}` and `{r, ..., n-1}`, for
   consecutive `j, j+1`: `|star_j(D)| >= |star_{j+1}(D)|`, and if they are
   equal, the vector `(x_S)` listed by increasing bitmask `S` is
   lexicographically at least the vector of the family with `j` and `j+1`
   swapped;

plus the derived unit clause "`r` is in `Tight`" when `r < n` (step (f)
below).

**Proposition.** Let `n >= 3` and assume the conjecture for every downset on
a ground set with at most `n - 1` elements.  If it fails for a downset on
`{0, ..., n-1}`, then conditions 1-8 and the unit clause hold for some
`(D, Y)` and some `r in {3, ..., n}`.

**Proof.** Among the counterexample downsets on `{0, ..., n-1}` choose `D`
with `|D|` minimal, and a maximum intersecting `Y subseteq D`, so
`|Y| = alpha(D) > Delta(D)`.

(a) Let `M` be a maximal member of `D` and `D' = D \ {M}`.  Then `D'` is a
downset, `alpha(D') >= alpha(D) - 1` (drop `M` from `Y`), and
`|star_i(D')| = |star_i(D)| - [i in M]`.  By minimality `D'` is not a
counterexample.  Condition 5 restates `|Y| > Delta(D)`.  If
`alpha(D) >= Delta(D) + 2`, then `alpha(D') >= Delta(D) + 1 > Delta(D')`, a
contradiction; hence `|Y| = Delta(D) + 1`, and `Tight` is the nonempty set
of elements with a largest star.  If `Tight subseteq M`, then
`Delta(D') = Delta(D) - 1 < Delta(D) <= alpha(D')`, again a contradiction.
So `Tight` lies in no maximal member of `D`, i.e. `Tight` is not in `D`
(condition 6).

(b) `down(Y) subseteq D` is a counterexample as well
(`|Y| > Delta(D) >= Delta(down(Y))`), so `D = down(Y)` by minimality
(condition 2).  If `T in D \ Y` met every member of `Y`, then `Y union {T}`
would be a larger intersecting family (condition 3).

(c) If some `S in Y` (nonempty, as `Y` is intersecting) had at most two
elements, `Y` would lie in the union of two stars, and by Kleitman-Magnanti
`D = down(Y)` would satisfy the conjecture (condition 1).

(d) If `{i}` were not in `D`, then `D` would be a counterexample on `n - 1`
elements (condition 4).

(e) Let `r` be the largest size of a member of `D`; `r >= 3` by (c).
Conditions 1-6 are invariant under relabelling the ground set.  Among all
relabellings `pi` with `{0, ..., r-1} in pi(D)`, take one for which the key
`(|star_0|, ..., |star_{n-1}|, x_0, x_1, ..., x_{2^n - 1})` is
lexicographically largest (`x_S` in bitmask order, true above false).
Condition 7 holds.  Swapping two elements of the same block keeps
`{0, ..., r-1}` in `D` and cannot increase the key; for consecutive `j, j+1`
this is condition 8.

(f) If `r < n`: `Tight` is not in `D` but `{0, ..., r-1}` is, so some
`i >= r` has `|star_i(D)| = Delta(D)`; by condition 8,
`|star_r(D)| >= |star_i(D)|`, so `r in Tight`.  QED.

**Corollary.** On ground sets with at most two elements every nonempty
intersecting family contains a set of size at most two, so the conjecture
holds there by Kleitman-Magnanti.  By induction, UNSAT of the rank-split CNF
for all `3 <= r <= n <= 7` proves the conjecture for ground sets with at most
seven elements.  Sterboul's theorem is not needed (rank 3 is one of the
CNFs), and neither is PySAT.

**Encoding details.**  Counting uses totalizers with clauses in both
directions, so each counter output is equivalent to "at least `t` inputs are
true".  For condition 6, auxiliary `tight_i` satisfy
`tight_i -> |star_i(D)| >= |Y| - 1`, and each `S` gets the clause
`not x_S or (or_{i not in S} tight_i)`; since `D` is a downset, this says
that the set of true `tight_i` is not in `D`, which is satisfiable exactly
when `Tight` is not in `D`.  For condition 8, unary counters give
`|star_j| >= |star_{j+1}|` clause by clause, and equality switches on a
lexicographic chain over the pairs `(S, S xor {j, j+1})` with `j in S`,
`j+1 not in S`, in increasing bitmask order.

**Faithfulness test.**  UNSAT needs every `(D, Y)` with conditions 1-8 to
extend to a model.  `generate_rank_cnf.py --self-test` (about 40 s)
builds that extension explicitly, with exact auxiliary values, and checks it
clause by clause: for every family of sets of size at least three when
`n = 4, 5`; for random saturated families brought to the canonical form of
step (e) when `n = 6, 7, 8`; and for cyclically symmetric families and the
Fano plane, which satisfy condition 6.  The counting bound is relaxed to
`|Y| - Delta(D)` so that real families can be tested; the test also checks
the canonical form against conditions 7-8 and that totalizers with up to nine
inputs are exact.

## Certificates

[`drat_manifest.json`](drat_manifest.json) lists, for every `(n, r)`, the
size and SHA256 of the CNF, the certificate kind and the measured solver
effort.  Committed proofs live in [`drat/`](drat/): CaDiCaL 3.0.1 proofs
reduced to their core lemmas with `drat-trim -l` (text DRAT, 1.5 MB in
total).

| `n` | ranks | CaDiCaL 3.0.1 conflicts | certificate |
|---|---|---|---|
| 3, 4, 5 | all | at most 7 | committed |
| 6 | 3, 4, 5, 6 | 334; 4,474; 381; 0 | committed |
| 7 | 3, 6, 7 | 297; 9,849; 0 | committed |
| 7 | 4 | 2,125,950 | regenerated by `--solve` |
| 7 | 5 | 841,502 | regenerated by `--solve` |
| 8 | 3, 8 | 550; 0 | committed |
| 8 | 7 | 308,332 | regenerated by `--solve` |

Rank `r = n` is refuted by unit propagation: condition 7 puts
`{0, ..., n-1}` into `D`, so every set, `Tight` included, is in `D`,
contradicting condition 6.  The regenerated binary DRAT proofs
measure 145 MB (`n7_r4`; solve 184 s, drat-trim 208 s), 64 MB (`n7_r5`;
59 s, 80 s) and 22 MB (`n8_r7`; 14 s, 19 s); the whole `--solve` run took
564 s of wall-clock time (287 s CPU) on the shared machine.

### Reproduction

```bash
cd problems/chvatal-downset
# Committed proofs (CI): 15 cases, about 2 s; drat-trim on PATH.
python3 certify_drat.py rank
# Proofs too large to commit: n7_r4, n7_r5, n8_r7; cadical and drat-trim
# on PATH, about 10 minutes on the machine above.
python3 certify_drat.py rank --solve
# Original encoding, n = 6 (PySAT proof, about 30 s plus pip).
python3 -m venv /tmp/chvatal-drat-venv
/tmp/chvatal-drat-venv/bin/pip install "python-sat[pblib]==1.9.dev17"
/tmp/chvatal-drat-venv/bin/python certify_drat.py repo-n6
# Encoding self-test, about 40 s.
python3 generate_rank_cnf.py --self-test
```

A single case by hand:

```bash
python3 generate_rank_cnf.py --n 7 --rank 4 --output /tmp/n7_r4.cnf
cadical /tmp/n7_r4.cnf /tmp/n7_r4.drat
drat-trim /tmp/n7_r4.cnf /tmp/n7_r4.drat
```

The earlier uncertified commands still work:

```bash
python -m venv /tmp/chvatal-sat-venv
/tmp/chvatal-sat-venv/bin/pip install "python-sat[pblib]"
/tmp/chvatal-sat-venv/bin/python generate_cnf.py \
  --n 6 --reduced --encoding cardnet --solve
/tmp/chvatal-sat-venv/bin/python generate_cnf.py --self-test
```

## Eight elements

Ranks 3, 7 and 8 are certified (table above).  Ranks 4, 5 and 6 were run with
`cadical -t 5400` (CaDiCaL 3.0.1, no proof output) on the CNFs written by
`generate_rank_cnf.py` (SHA256 in the manifest).  All three ran concurrently
on the shared machine and were stopped by the 90-minute wall-clock limit
with no result:

| rank | CPU seconds | conflicts | result |
|---|---|---|---|
| 4 | 3,690.8 | 35,463,210 | unknown |
| 5 | 3,691.0 | 31,695,931 | unknown |
| 6 | 4,068.9 | 44,748,818 | unknown |

The hardest rank grows fast: rank 4 needs 4,474 conflicts for `n = 6` and
2,125,950 for `n = 7`.  The same factor (about 475) would put `n = 8`,
rank 4, near `10^9` conflicts (an extrapolation, not a measurement), with
proofs of tens of gigabytes.  Two exploratory variants (scratch scripts,
not committed) did not change this picture, measured on `n = 7`, rank 4:

- cube-and-conquer on the value of `|Y|`: adding the units for "`|Y| = k`"
  gives 99 cubes, all UNSAT; the hardest needed 485,978 conflicts, but the
  total was 3,901,795, 1.8 times the single run;
- stronger symmetry breaking: lexicographic constraints for all
  transpositions inside the blocks, and for each cross-block transposition
  `(j, k)` guarded by "`{0, ..., r-1} - {j} + {k}` is in `D`" (then the
  swap keeps `{0, ..., r-1}` in `D`), reduced the conflicts only from
  2,125,950 to 1,508,117.

The MILP and feasibility runs in
[`n8_attempt_summary.md`](n8_attempt_summary.md) are unchanged.  The
eight-element case is therefore **unresolved by this attempt**.

## Trust boundary

- No novelty: `n <= 7` is EGP's theorem, reproduced here by SAT.
- The Kleitman-Magnanti theorem is cited, not re-proved; the reductions and
  the faithfulness argument are written proofs plus a randomized and
  exhaustive self-test, not a formal proof.
- The `n = 6` certificate of `generate_cnf.py` additionally relies on
  Sterboul's theorem, on the five-element case and on PySAT's cardinality
  network; the rank-split chain does not.
- drat-trim and the two generators are trusted code.

## FormalConjectures source

The exact upstream Lean statement is preserved in the local
[FormalConjectures snapshot](upstream/README.md).  It states the full conjecture
with `sorry`; the bounded searches here do not prove that declaration.
Informally, the `n <= 7` result above is `Chvatal.exists_maximal_star`
restricted to types `α` with `Fintype.card α <= 7` (`Decreasing` is the
downset property; `Intersecting` also excludes the empty set, as here); it is
not formalized in Lean.
