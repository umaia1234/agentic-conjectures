**English** | [한국어](README.ko.md)

# TxGraffiti Conjecture 3: independent domination versus saturation in regular graphs

## Statement

Source: R. Davila, B. Brimkov and R. Pepper, *In Reverie Together: Ten Years of Mathematical
Discovery with a Machine Collaborator*, [arXiv:2507.17780](https://arxiv.org/abs/2507.17780),
Conjecture 3. For every `r`-regular graph `G` with `r > 0` the paper conjectures
"i(G) ≤ µ∗(G), and this bound is sharp".

Here `i(G)` is the independent domination number (the least size of a maximal independent set) and
`µ*(G)` is the saturation number (the least size of a maximal matching), which equals the edge
domination number `γ_e(G)`. Formal Conjectures states the inequality as
`Arxiv.«2507.17780».tx_graffiti_conjecture_3` ([upstream snapshot](upstream/README.md)).

## Result

**Claimed status: refuted.** The upstream statement is false, and so is its restriction to
degrees `r ≥ 4`.

1. **The cubic counterexample is not ours.** `G48` is the 48-vertex cubic graph `counterexample.g6`
   of the public repository
   [ipitchford/txgraffiti-order48-successor](https://github.com/ipitchford/txgraffiti-order48-successor),
   with the same vertex labels (`python3 certificates/g48_cnf.py --same-as FILE` compares a graph6
   file with the Lean graph). It has `i = 16 > 15 = µ*`. Earlier and related public
   counterexamples are listed under [Prior work](#prior-work-and-scope).
2. **Every degree divisible by 3 fails.** Replace each vertex of a graph `G` by `t` pairwise
   non-adjacent twins (the lexicographic product `G[K̄_t]`). If `G` is `r`-regular, `G[K̄_t]` is
   `tr`-regular with `i(G[K̄_t]) = t·i(G)` and `µ*(G[K̄_t]) ≤ t·µ*(G)`. Hence `G48[K̄_t]` is
   `3t`-regular on `48t` vertices with `i = 16t > 15t ≥ µ*`. With `t = 2` this gives a 6-regular
   counterexample on 96 vertices, which refutes the restriction to `r ≥ 4`. We did not find the
   blow-up observation in the sources we checked; this is not a novelty claim.
3. **The other degrees stay open.** The conjecture remains open for every degree `r ≥ 4` that is
   not divisible by 3, including 4 and 5. No connected 4-regular graph with at most 17 vertices
   and no connected 5-regular graph with at most 14 vertices is a counterexample, and several
   structured families gave nothing either ([Searches](#searches)). This part is
   computer-assisted and not formalized.
4. **Pen and paper, not machine-checked.** [DETAILS.md](DETAILS.md) records a few class results.
   - For `r ≥ 7`, every `r`-regular graph with an efficient edge dominating set satisfies
     `i ≤ µ*`. This is a direct corollary of the lopsided Local Lemma argument of Gupta
     (arXiv:2608.22498, Theorem 1). In particular, Iwane's Problem 17 has a negative answer for
     `k ≥ 7`.
   - No minimally unsatisfiable `k`-CNF of deficiency 1 has every literal occurring at most
     `k − 1` times.

## What is checked, and by what

| Claim | Checked by |
|---|---|
| `G48` is cubic; `µ*(G48) = 15`; `D48` is an independent dominating set of size 16 | Lean (`decide`, kernel) |
| `\|E\| ≤ (2r − 1)·µ*(G)` for every graph of maximum degree `≤ r` | Lean |
| blow-up lemma: degree, `i(G[K̄_t]) = t·i(G)`, `µ*(G[K̄_t]) ≤ t·µ*(G)` | Lean |
| `G48LowerBound` (no independent dominating set of `G48` with at most 15 vertices) ⇒ the conjecture fails for every `r` divisible by 3, in particular `¬ statement` and `¬ statementGeFour` | Lean |
| `G48LowerBound` itself | DRAT proof checked by `drat-trim` in CI, for a CNF that CI regenerates from the Lean source and hash-checks |
| the CNF encodes `G48LowerBound` | pen and paper: the soundness argument in [g48_cnf.py](certificates/g48_cnf.py) and [DETAILS.md](DETAILS.md); `--check` also runs the soundness construction on `D48` |
| `i(G48) = 16`, `µ*(G48) = 15`, independently of SAT | C branch and bound [search/tx3check.c](search/tx3check.c), in CI |
| searches for degrees 4, 5 and 6 | C branch and bound plus nauty `geng`, local only |
| class results for `r ≥ 7` and the MU(1) remark | pen and paper only |

The refutation uses exactly one fact outside Lean, `G48LowerBound`. Lean takes it as a hypothesis,
and CI checks its DRAT certificate. The independent C check gives a second implementation of that
same fact.

### Lean theorems

Module `AgenticConjectures.TxGraffitiConjecture3`. Its docstring records the correspondence with
the upstream definitions.

- `statement`: the universal closure of the upstream theorem. `statementGeFour` replaces
  `1 ≤ r` by `4 ≤ r`, and `statementDeg r` fixes the degree.
- `card_edgeFinset_le_mul_saturationNumber`: `|E| ≤ (2r − 1)·µ*` when all degrees are at most `r`.
- `degree_blowup`, `indepDominationNumber_blowup`, `saturationNumber_blowup_le`: the blow-up lemma.
- `G48_degree`, `card_edgeFinset_G48`, `isMaximalEdgeMatching_M48`, `saturationNumber_G48`,
  `isNIndepDominatingSet_D48`.
- `indepDominationNumber_G48 (h : G48LowerBound) : indepDominationNumber G48 = 16`.
- `not_statementDeg (h : G48LowerBound) (hr : 3 ∣ r) (hr0 : 0 < r) : ¬ statementDeg r`.
- `not_statement (h : G48LowerBound) : ¬ statement` and
  `not_statementGeFour (h : G48LowerBound) : ¬ statementGeFour`.

No `sorry`, no extra axioms and no `native_decide` are used. `#print axioms` shows only
`propext`, `Classical.choice` and `Quot.sound`.

### The certificate

[certificates/g48_cnf.py](certificates/g48_cnf.py) reads the neighbour lists `nbrs48` from the Lean
module and builds a CNF that is satisfiable if and only if `G48` has an independent dominating set
with at most 15 vertices. The CNF has these parts:

- one domination clause per vertex;
- one independence clause per edge;
- a totalizer bounding the number of chosen vertices by 15. To shrink it, the 30 vertices covered
  by the matching `{0,1}, …, {28,29}` enter it through 15 pair indicators, which is sound because
  each pair is an edge.

The script docstring documents the variables, the clause order and the soundness argument. The
result, [g48_ids_le15.cnf](certificates/g48_ids_le15.cnf), has 212 variables and 692 clauses, with
sha256 `f916d6b4…bbbf2`.

The proof [g48_ids_le15.drat](certificates/g48_ids_le15.drat) is 1.0 MB. CaDiCaL 3.0.1 produced it
in text DRAT format, and two passes of `drat-trim -l` shortened it. `drat-trim` verifies it in
about 0.1 s, with 534 of the 692 clauses in the core. A fresh `cadical --no-binary` run gives a
different proof (1.8 MB) that also verifies; proofs need not be byte-identical.

## Searches

All searches use the exact solver [search/tx3check.c](search/tx3check.c).

- **The checker.** For each graph6 graph it computes `i` by branch and bound. It computes `µ*`
  exactly only when `i ≥ ⌈|E|/(2r − 1)⌉`, because otherwise `i < µ*` follows from the lower bound.
- **Cross-checks.** It agrees with the pysat solvers of [search/tx3lib.py](search/tx3lib.py) on
  all 18,058 connected `r`-regular graphs with `r = 3, …, 6` and `6 ≤ n ≤ 12`. On 2,000 random
  regular graphs, [search/crosscheck.py](search/crosscheck.py) compares pysat, CP-SAT and
  enumeration of maximal independent sets for `i`, and pysat, CP-SAT and (on small graphs) brute
  force for `µ*`.
- **Generation.** The graphs come from nauty `geng -c -dR -DR`. Counts match OEIS
  A006820 (4-regular), A006821 (5-regular) and A006822 (6-regular).

| family | range | graphs | counterexamples |
|---|---|---|---|
| connected 4-regular | `n ≤ 16` | 8,943,749 | 0 |
| connected 4-regular | `n = 17` | 86,221,634 | 0 |
| connected 5-regular | `n ≤ 14` | 3,467,295 | 0 |
| connected 6-regular | `n ≤ 14` | 21,985,302 | 0 |
| line graphs, prisms `G□K_2` and products `G□K_3` of connected cubic graphs `G` | `\|G\| ≤ 20` | 556,471 each | 0 |
| weighted blow-ups `B[t]` of degree 4, 5, 6 (vertex `v` of a cubic or quartic base `B` replaced by `t(v)` twins) | `\|B\| ≤ 18`, at most 62 vertices | 104,109 | 0 |

The products `G48□K_2` (4-regular, 96 vertices) and `G48□K_3` (5-regular, 144 vertices) have
independent dominating sets no larger than the lower bound `⌈|E|/(2r − 1)⌉` (28 and 40), so both
satisfy `i ≤ µ*`.

A 4-regular counterexample with an efficient edge dominating set would give an unsatisfiable
4-CNF in which every literal occurs exactly 3 times ([DETAILS.md](DETAILS.md), section 5).
Simulated annealing over such formulas ([search/sa_balanced_cnf.c](search/sa_balanced_cnf.c))
finds an unsatisfiable 3-CNF with 15 variables and 20 clauses, every literal occurring exactly
twice, in under 20 seconds. For `k = 4` and at most 20 variables, the fewest satisfying
assignments it reaches stays in the hundreds or more.

Per-run counts, timings and the exact commands are in
[search/search_summary.txt](search/search_summary.txt). `sh search/reproduce.sh` reruns the
searches; the `n = 17` stage runs only on request.

## Reproduction

From the problem directory:

```bash
python3 certificates/g48_cnf.py --check                                    # < 1 s, stdlib only
drat-trim certificates/g48_ids_le15.cnf certificates/g48_ids_le15.drat     # about 0.1 s
cc -O2 -o /tmp/txgraffiti3_tx3check search/tx3check.c && python3 certificates/g48_cnf.py --g6 | /tmp/txgraffiti3_tx3check   # prints COUNTEREXAMPLE i=16 mu*=15
(cd ../.. && lake env lean problems/txgraffiti-conjecture-3/upstream_statement_check.lean)  # after lake build; prints the 3 standard axioms
sh search/reproduce.sh              # default stages: about 2.5 hours on one core
sh search/reproduce.sh quartic17    # n = 17: about 2 CPU-hours in JOBS=3 parallel slices
```

`reproduce.sh` needs `cc`, nauty's `geng`, and a `python3` with networkx, python-sat and ortools
(set `PY` to choose it). The Lean module builds with `lake build` from the repository root.

## Statement faithfulness

- `statement` is the universal closure of the upstream theorem: the same binders `V : Type`,
  `[Fintype V] [DecidableEq V]`, `G` with `[DecidableRel G.Adj]` and `r : ℕ`, the same hypotheses
  `∀ v, G.degree v = r` and `1 ≤ r`, and the same conclusion. The helper definitions are copied
  term for term from formal-conjectures c094b97. The module docstring lists the cosmetic
  adaptations, such as namespacing and the explicit `G` argument of `IsNIndepDominatingSet`.
- Both invariants are infima over `ℕ`, and `sInf ∅ = 0`. Lean proves the relevant sets nonempty
  for every finite graph, so this convention plays no role.
- The paper's sharpness clause ("and this bound is sharp") is not part of the upstream formal
  statement, and we do not address it. The refutation concerns the inequality.
- The paper quantifies over `r`-regular graphs with `r > 0`, which matches `1 ≤ r`. The
  counterexamples are finite, simple and connected.
- `statementGeFour` is our own restriction to degrees `r ≥ 4`, the part of the conjecture that was
  still open once cubic counterexamples were public. It is not an upstream declaration.
- **Mechanical check.** [`upstream_statement_check.lean`](upstream_statement_check.lean) declares
  the six upstream definitions again, verbatim, in their upstream namespace `SimpleGraph`. It then
  restates the binders and conclusion of `Arxiv.«2507.17780».tx_graffiti_conjecture_3` under a
  negation, in the upstream namespace, and derives that negation from `not_statement` given
  `G48LowerBound` (and the `4 ≤ r` variant from `not_statementGeFour`). Its two bridge lemmas have
  to unfold the upstream constants to ours, so any mismatch in a definition or binder makes the
  file fail. It prints the three standard axioms. The file is not imported by the library, so CI
  does not run it.

## Prior work and scope

- **Cubic counterexamples were public before this work.**
  - `n = 50`, the earliest public counterexample we found: the repository
    [djma/TxGraffiti-conjecture3-counterexample](https://github.com/djma/TxGraffiti-conjecture3-counterexample)
    (commit `7810f30`, 2026-07-23), which already ships a CNF and an LRAT proof of `i ≥ 16`.
    The Zenodo release [10.5281/zenodo.21852504](https://doi.org/10.5281/zenodo.21852504)
    (2026-08-08) is derived from it. K. Afrasyab,
    [arXiv:2609.10783](https://arxiv.org/abs/2609.10783), shows that the same graph even has
    `γ = 16 > 15 = γ_e`. Section 2 of that paper builds the graph from a 15-variable, 20-clause
    formula, and `search/check_blowup.py` rebuilds it.
  - 113 cubic counterexamples on 50 and 60 vertices: H. Iwane, GitHub repository
    `HirotadaIwane/independent-domination-counterexample` (first release 2026-07-27). The paper
    Zenodo [10.5281/zenodo.22924244](https://doi.org/10.5281/zenodo.22924244) (2026-09-23) adds the
    clause–literal correspondence for `k`-regular graphs and the open Problem 17 on `k ≥ 4`.
  - `n = 48`: the anonymous release in the repository
    [ipitchford/txgraffiti-order48-successor](https://github.com/ipitchford/txgraffiti-order48-successor)
    above (2026-08-24), which already ships an exhaustive proof-tree certificate of `i ≥ 16` and a
    Python checker for it; its Zenodo record is
    [10.5281/zenodo.22083656](https://doi.org/10.5281/zenodo.22083656).
  - Formal Conjectures issue
    [#6737](https://github.com/google-deepmind/formal-conjectures/issues/6737) (open, 2026-09-30)
    reports that the conjecture is false.
- **Earlier searches and a proved class.** The repository
  [takumayellow/math-autoresearch](https://github.com/takumayellow/math-autoresearch) (2026-07-26)
  checks every connected `r`-regular graph with `r = 3, n ≤ 18`; `r = 4, n ≤ 14`; `r = 5, n ≤ 12`;
  `r = 6, n ≤ 11`; and `r = 7, n ≤ 10`, and finds no counterexample. H. Achour, *The Clique-Fiber
  Principle* ([10.5281/zenodo.21819055](https://doi.org/10.5281/zenodo.21819055), 2026-08-06),
  proves `i ≤ µ*` for the Cartesian products `H□K_m` with `m ≥ 3` and `m > Δ(H)`. That class
  contains neither the prisms `G□K_2` nor the products `G□K_3` of cubic graphs searched above.
- **Domination versus edge domination.** C. Gupta, [arXiv:2608.22498](https://arxiv.org/abs/2608.22498),
  proves `γ ≤ γ_e` for regular graphs of degree at least 7 via a random transversal of a minimum
  maximal matching and the lopsided Local Lemma. Remark 1 there explains why the argument does
  not give `i ≤ γ_e` in general, and our `r ≥ 7` class result applies the same argument verbatim.
  The paper also derives `i ≤ γ_e` for `Δ`-regular graphs of sufficiently large girth when
  `3 ≤ Δ ≤ 6`, and its Section 8 asks whether unsatisfiable `(Δ, Δ − 1, Δ − 1)`-formulas exist for
  `Δ ∈ {4, 5, 6}`.
- **Bounded-occurrence SAT.** T. Zhang, T. Peitl and S. Szeider,
  [arXiv:2405.16149](https://arxiv.org/abs/2405.16149) (SAT 2024), determine the smallest
  unsatisfiable `(3, p, q)`-formulas. For `k = 3` our MU(1) remark is the `∞` entry `p = q = 2` of
  their Table 6.
- **Not found in the sources we checked:** the blow-up observation and the counterexamples for
  degrees divisible by 3, including 6; a Lean formalization of the refutation; a DRAT certificate
  for `G48` (the `G48` release has a proof-tree certificate, and djma's repository an LRAT
  certificate for its 50-vertex graph); and searches of degrees 4–6 at the sizes above. No novelty
  is claimed before external review.

No human has reviewed these results. They were produced by an AI model and are checked only by
the Lean kernel, `drat-trim` and the numerical cross-checks. Nothing has been submitted to Formal
Conjectures or anywhere else; any external submission needs human approval.

## Files

- `certificates/g48_cnf.py`: regenerates and audits the CNF from the Lean source (`--check`). It
  also prints `G48` as graph6 (`--g6`) and compares a graph6 file with it (`--same-as`).
- `certificates/g48_ids_le15.cnf`, `certificates/g48_ids_le15.drat`: the CNF and its DRAT proof.
- `search/`: `tx3check.c` (exact `i` and `µ*`), `transform.c` (line graph and products),
  `wblow.c` (weighted blow-ups), `sa_balanced_cnf.c` (annealing over balanced CNFs), `tx3lib.py`
  with `crosscheck.py`, `xcheck_c.py`, `check_blowup.py`, `prod_check.py` (SAT and CP-SAT
  cross-checks), `reproduce.sh`, `search_summary.txt`.
- `upstream/`: the Formal Conjectures snapshot.
- `upstream_statement_check.lean`: the mechanical faithfulness check (not imported by the
  library).
- [DETAILS.md](DETAILS.md): proofs and derivations.
