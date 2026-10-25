**English** | [한국어](README.ko.md)

# WOWII Graph Conjecture 61

## The original conjecture and partial results

For a finite simple connected graph \(G\), let \(f(G)\) be the number of
vertices of a maximum induced forest, \(r(G)\) the Havel--Hakimi
residue, and \(D(G)\) the diameter. The original conjecture is

\[
f(G)\ge r(G)+\left\lceil\frac{D(G)}3\right\rceil.
\]

In this folder we prove the following four results.

1. In every finite simple connected graph,
   \[
   f(G)\ge\alpha(G)+\left\lceil\frac{D(G)}4\right\rceil.
   \]
2. If there are at least two vertices, then \(f(G)\ge\alpha(G)+1\), and
   if \(f(G)=\alpha(G)+1\), then \(D(G)\le4\).
3. The original conjecture holds in every connected graph with
   \[
   D(G)\in\{0,1,2,3,5,6,9\}.
   \]
4. Every finite tree satisfies the original conjecture regardless of
   diameter.

The detailed proof is in [PROOF.md](PROOF.md). These results do not
close the remaining diameters for general graphs, so they are not a
resolution of the full original conjecture. The inequality
\(f(G)\ge\alpha(G)+1\) of result 2 is also proved in Lean, and an
exhaustive computer check finds no counterexample to the original
conjecture in several finite graph families; both are described below.

## Exhaustive computer check (2026-10-24)

### Verified statement

For every graph \(G\) in the four finite families below, the conjectured
inequality \(f(G)\ge r(G)+\lceil D(G)/3\rceil\) holds, so none of them
contains a counterexample. The quantities follow the upstream Lean
definitions. \(r(G)\) is `SimpleGraph.residue`, the Havel--Hakimi residue
(not the radius): sort the degree sequence in descending order, then
repeatedly remove the first entry \(d\), decrement the next \(d\) entries
with `List.splitAt` and truncated subtraction, and re-sort; \(r(G)\) is the
number of zeros left. \(f(G)\) is `largestInducedForestSize` and \(D(G)\)
is `SimpleGraph.diam`.

| family | enumeration | graphs | min slack |
|---|---|---|---|
| all connected graphs, \(n\le11\) | `geng -c n` | 1018690329 | 0 |
| all trees, \(n\le26\) | `gentreeg n` | 447672596 | 0 |
| connected graphs with cyclomatic number \(m-n+1\le c\): \(c=4\) for \(12\le n\le15\), \(c=3\) for \(n=16,17\), \(c=2\) for \(18\le n\le20\) | `geng -c n n-1:n-1+c` | 626942607 | 0 |
| connected graphs with \(12\le n\le18\) and \(D\ge n-5\) | `diampath_gen n D \| shortg` | 2046546 | 1 |

Here \(n\) is the number of vertices and \(m\) the number of edges. Write
\(s(G)=f(G)-r(G)-\lceil D(G)/3\rceil\) for the slack. In each of the first
three families the minimum slack is \(0\) at every order \(n\): the star
\(K_{1,n-1}\) (\(f=n\), \(r=n-1\), \(D=2\)) attains it, and among the
connected graphs with \(n\le11\) so does \(K_n\). The inequality is
therefore tight at every order. This is a finite search, not a proof of
the conjecture.

### All connected graphs with at most 11 vertices

| n | graphs | trees | min slack | graphs at min | max D | violations | crosscheck |
|---|---|---|---|---|---|---|---|
| 1 | 1 | 1 | 0 | 1 | 0 | 0 | 0 mismatches |
| 2 | 1 | 1 | 0 | 1 | 1 | 0 | 0 mismatches |
| 3 | 2 | 1 | 0 | 2 | 2 | 0 | 0 mismatches |
| 4 | 6 | 2 | 0 | 5 | 3 | 0 | 0 mismatches |
| 5 | 21 | 3 | 0 | 11 | 4 | 0 | 0 mismatches |
| 6 | 112 | 6 | 0 | 32 | 5 | 0 | 0 mismatches |
| 7 | 853 | 11 | 0 | 100 | 6 | 0 | 0 mismatches |
| 8 | 11117 | 23 | 0 | 338 | 7 | 0 | 0 mismatches |
| 9 | 261080 | 47 | 0 | 1231 | 8 | 0 | 0 mismatches |
| 10 | 11716571 | 106 | 0 | 5124 | 9 | 0 | 0 mismatches |
| 11 | 1006700565 | 235 | 0 | 26094 | 10 | 0 | sample: 0 mismatches |

"violations" counts the graphs that violate the conjecture or one of the
PROOF.md inequalities listed below, plus internal anomalies of the
checker. "crosscheck" counts disagreements between the fast and the
brute-force computations of \(f\), \(\alpha\), \(D\) and \(r\). For
\(n=11\) the brute force ran on a hash sample of 246176 graphs, not on
every graph.

By diameter, over all connected graphs with \(n\le 11\):

| D | graphs | min slack | graphs at min | min f-alpha | ceil(D/4) | ceil(D/3) | graphs with f-alpha < ceil(D/3) | min slack among them |
|---|---|---|---|---|---|---|---|---|
| 0 | 1 | 0 | 1 | 0 | 0 | 0 | 0 | - |
| 1 | 10 | 0 | 10 | 1 | 1 | 1 | 0 | - |
| 2 | 373528268 | 0 | 9215 | 1 | 1 | 1 | 0 | - |
| 3 | 611259790 | 0 | 12523 | 1 | 1 | 1 | 0 | - |
| 4 | 32578716 | 0 | 11190 | 1 | 1 | 2 | 185926 | 0 |
| 5 | 1252762 | 1 | 18066 | 2 | 2 | 2 | 0 | - |
| 6 | 65940 | 1 | 389 | 2 | 2 | 2 | 0 | - |
| 7 | 4496 | 1 | 649 | 2 | 2 | 3 | 51 | 1 |
| 8 | 327 | 2 | 161 | 2 | 2 | 3 | 1 | 2 |
| 9 | 18 | 3 | 18 | 4 | 3 | 3 | 0 | - |
| 10 | 1 | 3 | 1 | 5 | 3 | 4 | 0 | - |

"min f-alpha" is the minimum of \(f-\alpha\). The column "graphs with
f-alpha < ceil(D/3)" counts the graphs for which the stronger inequality
\(f(G)\ge\alpha(G)+\lceil D(G)/3\rceil\) fails. For those graphs the
conjecture holds only because \(r(G)<\alpha(G)\).

### Residual diameters 4, 7, 8 and at least 10

PROOF.md settles diameters \(\{0,1,2,3,5,6,9\}\) and all trees. The
remaining diameters are \(4\), \(7\), \(8\) and \(D\ge10\). The minimum
slack there, by family:

| family | residual D | graphs | min slack | graphs at min | graphs with f-alpha < ceil(D/3) | smallest graph6 at min slack |
|---|---|---|---|---|---|---|
| connected, \(n\le11\) | 4 | 32578716 | 0 | 11190 | 185926 | `E?zO` |
| connected, \(n\le11\) | 7 | 4496 | 1 | 649 | 51 | `H?ABAqW` |
| connected, \(n\le11\) | 8 | 327 | 2 | 161 | 1 | `` H?`D@`O `` |
| connected, \(n\le11\) | >= 10 | 1 | 3 | 1 | 0 | `J?AAD?oEAO?` |
| trees, \(n\le26\) | 4 | 8970 | 1 | 363 | 0 | `DkC` |
| trees, \(n\le26\) | 7 | 10943967 | 2 | 7 | 0 | `GhE?GC` |
| trees, \(n\le26\) | 8 | 36178575 | 2 | 1 | 0 | `HhE?GC@` |
| trees, \(n\le26\) | >= 10 | 331250953 | 3 | 12 | 0 | `JhCK?C@?G?_` |
| sparse, \(12\le n\le20\) | 4 | 3878499 | 0 | 1358 | 1704 | `K???????F?Z}` |
| sparse, \(12\le n\le20\) | 7 | 155279595 | 1 | 69 | 5931 | `K???C@_SKYTW` |
| sparse, \(12\le n\le20\) | 8 | 147446044 | 2 | 4490 | 956 | `K????B_FEEBW` |
| sparse, \(12\le n\le20\) | >= 10 | 82006435 | 2 | 1391 | 2693 | `K???EA_E?kGo` |
| \(D\ge n-5\), \(12\le n\le18\) | 7 | 94741 | 1 | 2936 | 646 | `K????CKHIeRW` |
| \(D\ge n-5\), \(12\le n\le18\) | 8 | 141783 | 2 | 15477 | 188 | `` K?????FP`qV? `` |
| \(D\ge n-5\), \(12\le n\le18\) | >= 10 | 1614921 | 2 | 15160 | 1745 | `` K???OH@_`oE_ `` |

Observations, all from the data above:

- **Diameter 4.** Slack \(0\) occurs from \(n=6\) on (four graphs on six
  vertices). One of them, `E?zO`, is a 4-cycle with one pendant vertex at
  each of two opposite cycle vertices: \(f=5\), \(\alpha=4\), \(r=3\),
  \(D=4\). It has \(f=\alpha+1\) with \(D=4\), so the bound \(D\le4\) in
  (6) of PROOF.md is attained, and \(f<\alpha+\lceil D/3\rceil\): the
  conjecture holds there only because \(r<\alpha\).
- **Diameter 7.** The minimum slack is \(1\), for example `H?ABAqW`
  (\(n=9\), \(f=8\), \(\alpha=5\), \(r=4\)). The stronger inequality
  \(f\ge\alpha+\lceil D/3\rceil\) fails from \(n=10\) on: three graphs on
  10 vertices, for example `I??E@osa_` with \(f=\alpha+2=8\) and
  \(r=\alpha-2=4\).
- **Diameter 8.** The minimum slack is \(2\); the path \(P_9\)
  (`` H?`D@`O ``) attains it. The stronger inequality fails for one graph
  on 11 vertices (`` J???F?[o`o? ``, \(f=9\), \(\alpha=7\), \(r=4\)),
  for 188 graphs of the \(D\ge n-5\) family and for 956 graphs of the
  sparse family.
- **Diameter at least 10.** Among connected graphs with \(n\le11\) only
  \(P_{11}\) has \(D\ge10\) (slack 3), and trees with \(n\le26\) and
  \(D\ge10\) have slack at least 3. The sparse and \(D\ge n-5\)
  families reach slack \(2\) at \(D=10\), for example the unicyclic
  graph `K???EA_E?kGo` on 12 vertices (\(f=11\), \(\alpha=7\),
  \(r=5\)).
- **Consequence for proofs.** For every
  \(D\in\{4,7,8,10,11,12,13,14\}\), that is, for every residual diameter
  up to 14, the families contain graphs with
  \(f<\alpha+\lceil D/3\rceil\). At these diameters no argument that
  bounds \(f-\alpha\) from below and then uses \(r\le\alpha\) can prove
  the conjecture; a proof needs more information about \(r\).

### Sanity check of PROOF.md

Every graph of every family above also satisfies \(r\le\alpha\)
(inequality (1)), \(f\ge\alpha+\lceil D/4\rceil\) (Theorem 1),
\(f\ge\alpha+1\) when \(n\ge2\) (inequality (5)) and
\(f=\alpha+1\Rightarrow D\le4\) (implication (6)). Every tree has \(f=n\)
and satisfies the conjecture (Theorem 4). Theorem 1 holds with equality
for some graph of every diameter \(D\le14\) in these families, and (6) is
attained with \(D=4\).

### Implementations and cross-checks

1. [`wowii61.cpp`](wowii61.cpp) is the fast path. \(f\) comes from a
   branch and bound over vertex subsets that keeps the current forest as a
   list of component bitmasks, discards vertices that would close a cycle
   and adds vertices with at most one possible neighbour without
   branching. \(\alpha\) comes from branching with the degree-\(\le1\)
   rule and \(D\) from a bitmask BFS from every vertex. \(r\) is a literal
   transcription of `havelHakimiStep`/`residueAux`. The program reads
   `geng`/`gentreeg` output, or enumerates all labeled graphs on
   \(n\le8\) vertices without nauty.
2. `wowii61 --crosscheck` runs separate brute-force code in the same
   program: all \(2^n\) vertex subsets for \(f\) (acyclic iff
   \(|E|=|V|-\#\)components) and for \(\alpha\), Floyd--Warshall for \(D\),
   and Havel--Hakimi on a count array for \(r\). It ran on every connected
   graph with \(n\le10\) and on the \(n=11\) hash sample, with zero
   disagreements.
3. [`wowii61_ref.py`](wowii61_ref.py) is an independent Python
   implementation: its own graph6 parser, subset search with union-find
   for \(f\), subset search for \(\alpha\), BFS for \(D\), and a list-based
   residue that follows the Lean definition line by line. With `--nx`,
   networkx recomputes the parse, connectivity, the diameter, \(\alpha\)
   (maximum clique of the complement) and the acyclicity of the forest
   witness. On all connected graphs with \(n\le9\) its summary is
   identical to the C++ summary. On hash samples of \(n=10\) (1/64, 182471
   graphs) and \(n=11\) (1/4096, 246176 graphs) every per-graph value
   agrees with the C++ value, and networkx agrees everywhere
   ([`results/reference_check.log`](results/reference_check.log)).
4. Enumeration completeness rests on nauty (`geng`, `gentreeg`,
   `shortg`). The graph counts match OEIS
   [A001349](https://oeis.org/A001349) (connected graphs, \(n\le11\)) and
   [A000055](https://oeis.org/A000055) (trees, \(n\le26\)). The labeled
   enumeration on CI matches [A001187](https://oeis.org/A001187).
   [`diampath_gen.cpp`](diampath_gen.cpp) lists every connected graph
   with diameter \(D\ge n-5\) along a diametral path (at most four
   vertices off the path). It reproduces the `geng` count of every
   \(n\le11\) and \(D\ge\max(1,n-5)\)
   ([`results/diampath_validation.log`](results/diampath_validation.log)).

### Reproduction

From this folder, with nauty 2.9.3 and a C++17 compiler on `PATH`:

```bash
python3 verify_small.py                    # CI check:  5 s wall
bash run_exhaustive.sh OUT conn 3          # n <= 10:  44 s wall,   69 s CPU
bash run_exhaustive.sh OUT conn11 3        # n = 11:  875 s wall, 1616 s CPU
bash run_exhaustive.sh OUT trees 2         # trees:  1539 s wall, 1789 s CPU
bash run_exhaustive.sh OUT sparse 3        # sparse: 2196 s wall, 4360 s CPU
bash run_exhaustive.sh OUT diampath 3      # D >= n-5: 31 s wall, 52 s CPU
PYTHON=python3-with-networkx bash run_exhaustive.sh OUT ref 1
                                           # reference: 1264 s wall, 648 s CPU
```

`diampath` and `ref` need the output of `conn` and `conn11`. The times
were measured on an Apple M5 Max shared with other jobs (load average
60--95) with Apple clang 21. The merged summaries written to `OUT`
(`connected_n1-10.txt`, `connected_n11.txt`, `trees_n1-26.txt`,
`sparse.txt`, `diampath_n12-18.txt`) should be identical to the files in
[`results/`](results/). Another nauty version may label graphs
differently, which can change only the `EX_` example lines. Each summary
holds the counts per \(n\), the histogram of
\((n,D,f-\alpha,\alpha-r)\), the violation and disagreement counters,
and the five lexicographically smallest graph6 strings at the minimum
slack and at the minimum \(f-\alpha\) for each \((n,D)\). [`wowii61_summary.py`](wowii61_summary.py) merges them and
prints the tables above. The hash samples of \(n=10,11\) are not
committed; `conn` and `conn11` regenerate them, and their SHA-256 sums
are in `results/reference_check.log`.

`verify_small.py` (CI) compiles `wowii61.cpp`, runs it with the brute-force
crosscheck on every labeled graph with \(n\le7\) (the connected counts
must equal A001187), compares the Python reference with it on every
labeled graph with \(n\le6\), and checks the committed summaries: OEIS
counts, histogram totals, zero counters, the inequalities re-checked on
the histograms, and for \(n\le7\) the same \((D,f-\alpha,\alpha-r)\)
values as the labeled enumeration.

### What is not claimed

- No proof of the conjecture, and no result for any graph outside the
  listed families. "No counterexample" is a statement about these finite
  families only.
- No novelty. Small-order checks of Graffiti conjectures are routine, and
  this computation may repeat unpublished checks.
- Completeness of the enumeration relies on nauty and on the OEIS counts.
  Apart from its trees, the counts of the sparse family are not compared
  with an independent source. CI re-runs only the labeled \(n\le7\) part
  and re-reads the committed summaries; the larger runs are local.
- The informal proofs in PROOF.md stay informal, except inequality (5),
  which is formalized below. The inequality \(r\le\alpha\) is quoted from
  the literature and only checked numerically here.

## Lean formalization of inequality (5)

[`AgenticConjectures/WowiiGraphConjecture61.lean`](../../AgenticConjectures/WowiiGraphConjecture61.lean)
proves inequality (5) of PROOF.md (the first part of Theorem 2) without
`sorry`, extra axioms or `native_decide`.

| declaration | statement |
|---|---|
| `largestInducedForestSize G` | `sSup {n \| ∃ s : Finset α, (G.induce s).IsAcyclic ∧ s.card = n}`, the same body as the upstream helper |
| `card_le_largestInducedForestSize` | a finset `s` with `(G.induce s).IsAcyclic` has `s.card ≤ largestInducedForestSize G` |
| `isAcyclic_induce_insert` | if `I` is independent, `G.induce (insert x I)` is acyclic |
| `indepNum_add_one_le_largestInducedForestSize` | `[Nontrivial α]`, `G.Connected` ⟹ `G.indepNum + 1 ≤ largestInducedForestSize G` |

Statement faithfulness. The upstream helper
`SimpleGraph.largestInducedForestSize` (FormalConjecturesForMathlib,
`Combinatorics/SimpleGraph/Induced.lean`) is not a dependency of this
repository, so the module copies its body verbatim:
`sSup { n | ∃ s : Finset α, (G.induce s).IsAcyclic ∧ s.card = n }`, with
`s` coerced to a set. \(\alpha(G)\) is mathlib's `SimpleGraph.indepNum`.
The type-class context `[Fintype α] [DecidableEq α] [Nontrivial α]` and
the hypothesis `G.Connected` are those of the upstream `conjecture61`.
`Nontrivial` is needed: the one-vertex graph has \(f=\alpha=1\). The
theorem involves neither the residue nor the diameter. It is a partial
result towards the upstream statement, not a proof of it, and the
upstream declaration stays `sorry`-marked and open.

## FormalConjectures upstream

The [local upstream snapshot](upstream/README.md) preserves the exact
Lean declaration of the original inequality at a pinned commit. The
declaration is a problem statement with a `sorry`, and the partial
results in this folder do not close that general statement.

## Source status and scope of verification

- The [WOWII Conjecture 61 original
  link](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/) is the
  source cited by FormalConjectures.
- As checked on 2026-08-11, the FormalConjectures main commit
  `9118d083ffca1536f521f9a7d103201f537ea670`'s
  [`GraphConjecture61.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/WrittenOnTheWallII/GraphConjecture61.lean)
  marked the original inequality as `category research open`.
- The four results above rely on the combinatorial arguments of
  [PROOF.md](PROOF.md) and the basic inequality
  \(r(G)\le\alpha(G)\). Only inequality (5) is proved in Lean. The
  exhaustive computer check covers finite graph families only and is not
  a certificate for the general statement.
