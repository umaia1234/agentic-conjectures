**English** | [한국어](README.ko.md)

# WOWII Graph Conjecture 189

## Statement

Conjecture 189 of *Written on the Wall II*, E. DeLaViña's list of conjectures of the program
Graffiti.pc, as quoted verbatim in the Formal Conjectures snapshot:

> If G is a simple connected graph with n > 1 such that maximum { dist_even(v) : dist_even(v) is
> the number of vertices at even distance from v } ≤ 1 + σ(G), then G has a Hamiltonian path.

Source: [Written on the Wall II](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/). Formal
Conjectures cites `http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj189` and
records the status as O (open). Here dist_even(v) counts v itself, since distance 0 is even.
σ(G) is the second entry of the nondecreasing degree sequence.

Below, (H) is the hypothesis: G is connected, n > 1 and max_v dist_even(v) ≤ 1 + σ(G).
*Traceable* means "has a Hamiltonian path". N₂(v) is the set of vertices at distance exactly two
from v.

## Result

**Status: partial.** The conjecture is not resolved. Lean 4 proves the following, with no `sorry`,
no extra axioms and no `native_decide`:

1. The conjecture holds when diam(G) ≤ 2. This reproduces condition (1) of Theorem B of Easwar and
   Johari.
2. Under (H), |N₂(v)| ≤ σ for every vertex v.
3. Under (H), n ≤ dist_even(x) + deg(x) + (dist_even(x) − 1)·σ for every vertex x. Hence every
   vertex has degree at least n − σ² − σ − 1, and n ≤ (σ + 1)².
4. Under (H), 4n ≤ 4(σ + 1) + 4·deg(x) + (σ + 1)² for every vertex x. Hence
   n ≤ 2σ + 1 + ⌊(σ + 1)²/4⌋, which is 11 for σ = 3 and 15 for σ = 4. When σ ≤ 4, every vertex
   has degree at least n − 11.

Three exhaustive computer searches find no counterexample:

5. All connected graphs on at most 11 vertices: 1,006,700,565 graphs at n = 11, of which
   27,429,222 satisfy (H).
6. All graphs with σ(G) ≤ 3. By item 3, a graph with σ(G) ≤ 3 that satisfies (H) has at most 16
   vertices, so a pruned search over n ≤ 16 covers them all. Up to isomorphism there are exactly
   654 such graphs. All have at most 10 vertices and all are traceable.
7. All graphs with σ(G) = 4. By item 4, a graph with σ(G) = 4 that satisfies (H) has at most 15
   vertices, so a pruned search over n ≤ 15 covers them all. Up to isomorphism there are exactly
   61,054 such graphs. All have at most 13 vertices and all are traceable.

So **Conjecture 189 holds for every graph with at most 11 vertices and for every graph with
σ(G) ≤ 4**. Items 5–7 are computer-assisted. They assume that nauty's `geng` and the search
programs are correct. Two C programs written independently of each other check every graph. A
standard-library Python script re-checks a Hamiltonian path for each of the 654 graphs in item 6
and each of the 61,054 graphs in item 7.

### Lean theorems

Module: `AgenticConjectures.WowiiGraphConjecture189`
([source](../../AgenticConjectures/WowiiGraphConjecture189.lean)).

| Theorem | Content |
| --- | --- |
| `statement` | the upstream `conjecture189`, as a `Prop`; not proved |
| `exists_isHamiltonian_of_ore` | if deg u + deg v ≥ n − 1 for all distinct non-adjacent u, v, then G is traceable (Ore) |
| `secondSmallestDegree_le_max` | σ ≤ max(deg u, deg v) for u ≠ v |
| `distEven_eq_card_sub_degree` | if diam ≤ 2, then dist_even(v) = n − deg v |
| `conjecture189_of_diam_le_two` | (H) and diam ≤ 2 imply traceable |
| `card_dist_eq_two_le` | (H) implies \|N₂(v)\| ≤ σ |
| `card_le_distEven_add_degree` | (H) implies n ≤ dist_even(x) + deg x + (dist_even(x) − 1)σ |
| `card_le_degree_add` | (H) implies n ≤ deg x + σ² + σ + 1 |
| `card_le_sq` | (H) implies n ≤ (σ + 1)² |
| `search_reduction` | (H) and σ ≤ 3 imply n ≤ 16, min degree ≥ n − 13, \|N₂(v)\| ≤ 3, and at least two vertices of degree ≤ 3 |
| `exists_card_add_mul_self_le` | (H) implies that every x has some s with n + s² ≤ dist_even(x) + deg x + s(σ + 1) |
| `four_mul_card_le` | (H) implies 4n ≤ 4(σ + 1) + 4 deg x + (σ + 1)² |
| `four_mul_card_le_sq` | (H) implies 4n ≤ 4(2σ + 1) + (σ + 1)² |
| `search_reduction_four` | (H) and σ ≤ 4 imply n ≤ 15, min degree ≥ n − 11, \|N₂(v)\| ≤ 4, and at least two vertices of degree ≤ 4 |
| `exists_degree_eq_secondSmallestDegree`, `two_le_card_degree_le` | some vertex has degree σ; at least two have degree ≤ σ |

## Method

### Diameter at most two

If diam(G) ≤ 2, the vertices at even distance from v are v and its non-neighbours. So
dist_even(v) = n − deg(v), and (H) says that deg(v) ≥ n − 1 − σ for every v. Two distinct
vertices satisfy σ ≤ max(deg u, deg v), since σ is the second-smallest degree. So
deg u + deg v ≥ n − 1, which is Ore's condition for a Hamiltonian path. The Lean proof of Ore's
condition is self-contained: take a longest path, close it into a cycle by the usual rotation,
then extend it.

### The order bound

Fix a vertex x and let D be the set of vertices at even distance from x, so |D| = dist_even(x).

- A vertex w at odd distance at least 3 from x has a neighbour y one step closer to x. That y is
  in D \ {x}.
- w is at distance exactly 2 from a fixed neighbour q(y) of y one step closer still. The path
  q(y)–y–w gives distance at most 2, and the distances from x give at least 2.
- Under (H), |N₂(p)| ≤ dist_even(p) − 1 ≤ σ for every p.

So the vertices at odd distance at least 3 number at most (|D| − 1)·σ. This gives
n ≤ |D| + deg(x) + (|D| − 1)·σ. With |D| ≤ σ + 1, a vertex x of degree σ gives n ≤ (σ + 1)².
Any vertex x gives deg(x) ≥ n − σ² − σ − 1.

### A sharper order bound

Let O(x) be the set of vertices at odd distance at least 3 from x, so
n = dist_even(x) + deg(x) + |O(x)|. Each z ∈ O(x) has a neighbour q(z) one step closer to x.
Take a minimum set Y of neighbours of x that contains, for every z ∈ O(x), a vertex on a
shortest path from x to q(z), and let s = |Y|. Then:

- every z ∈ O(x) is at even distance from some y ∈ Y;
- by the minimality of Y, every y ∈ Y has, besides itself, s − 1 vertices outside O(x) at even
  distance.

Under (H), each y ∈ Y therefore has at most σ + 1 − s vertices of O(x) at even distance, so
|O(x)| ≤ s·(σ + 1 − s) ≤ (σ + 1)²/4. Hence 4n ≤ 4(σ + 1) + 4·deg(x) + (σ + 1)², and a vertex of
degree σ gives n ≤ 2σ + 1 + ⌊(σ + 1)²/4⌋. [`DETAILS.md`](DETAILS.md) has the full proof.

### Exhaustive search for n ≤ 11

`geng -c n` from nauty 2.9.3 generates every connected graph once up to isomorphism. The output
goes through two checkers:

- [`hyp189.c`](hyp189.c) computes dist_even with bitset BFS, then σ and (H). For each (H) graph
  it decides traceability by depth-first search with a node budget, and falls back to an exact
  subset dynamic programme.
- [`ind189.c`](ind189.c) was written independently. It uses adjacency-list BFS and backtracking,
  with a pure subset-DP option `-dp`.

For n ≤ 11 the two programs agree on the number of (H) graphs and on their σ
histograms. Neither program finds an (H) graph without a Hamiltonian path.

| n | connected graphs | (H) graphs | (H) graphs by σ (σ: count) | open after Easwar–Johari |
| --- | ---: | ---: | --- | ---: |
| 2 | 1 | 1 | 1:1 | 0 |
| 3 | 2 | 2 | 1:1 2:1 | 0 |
| 4 | 6 | 5 | 1:1 2:3 3:1 | 0 |
| 5 | 21 | 15 | 2:9 3:5 4:1 | 0 |
| 6 | 112 | 51 | 2:15 3:27 4:8 5:1 | 0 |
| 7 | 853 | 247 | 2:5 3:163 4:67 5:11 6:1 | 0 |
| 8 | 11,117 | 1,476 | 3:293 4:1018 5:149 6:15 7:1 | 0 |
| 9 | 261,080 | 22,575 | 3:100 4:17012 5:5132 6:311 7:19 8:1 | 0 |
| 10 | 11,716,571 | 418,415 | 3:29 4:33433 5:360065 6:24249 7:614 8:24 9:1 | 24 |
| 11 | 1,006,700,565 | 27,429,222 | 4:7186 5:21987577 6:5321065 7:112195 8:1169 9:29 10:1 | 0 |

The last column counts the (H) graphs not covered by Theorem B of Easwar and Johari: 2-connected,
diameter at least 3, and n ≥ 2σ + 4. The 24 graphs at n = 10 all have σ = 3.

At n = 11, `geng`'s output was split into eight parts with its res/mod option, and both
checkers read every part. [`search_summary.txt`](search_summary.txt) has the raw summary
lines of all runs.

### Exhaustive search for σ(G) ≤ 3

[`prune189.c`](prune189.c) is a `PRUNE` hook for `geng`, run with SMAX=3. It discards a graph,
intermediate or final, in either of two cases:

- some vertex has more than three vertices at distance two;
- fewer than 2 − (n_final − n_current) vertices have degree at most three.

`geng` reaches each graph through a chain of induced subgraphs. Distance two in an induced
subgraph means non-adjacent with a common neighbour, so it is distance two in the whole graph
too. Degrees only grow along the chain. So by `search_reduction`, every (H) graph with σ ≤ 3
survives the pruning. For n = 15 and n = 16, `search_reduction` also gives minimum degree at least
n − 13, so the search there runs `geng -c -d2` and `geng -c -d3`.

As an empirical check, for every n ≤ 11 the pruned search finds exactly the σ ≤ 3 (H) graphs of
the unpruned search, as the same graph6 strings: 1, 2, 5, 14, 42, 168, 293, 100, 29 and 0
graphs.

| n | `geng` flags | graphs after pruning | (H) graphs (all σ ≤ 3) | CPU time |
| --- | --- | ---: | ---: | ---: |
| 2–9 | `-c` | 1, 2, 6, 20, 93, 396, 939, 785 | 1, 2, 5, 14, 42, 168, 293, 100 | < 0.1 s each |
| 10 | `-c` | 669 | 29 | 0.1 s |
| 11 | `-c` | 796 | 0 | 0.7 s |
| 12 | `-c` | 1,513 | 0 | 4.8 s |
| 13 | `-c` | 3,167 | 0 | 47 s |
| 14 | `-c` | 7,100 | 0 | 8.7 min |
| 15 | `-c -d2` | 2,125 | 0 | 76 min |
| 16 | `-c -d3` | 5 | 0 | 7.7 h |

Every (H) graph found is traceable. `hyp189`, `ind189` and [`certify.py`](certify.py) all agree
on the graphs that pass the pruning. [`sigma3_certificates.txt`](sigma3_certificates.txt) lists
the 654 graphs in graph6, each with a Hamiltonian path. `certify.py` is a third implementation
of dist_even and σ, using only the Python standard library. It re-checks connectivity, (H),
σ ≤ 3 and each path, and the per-order counts.

### Exhaustive search for σ(G) = 4

With SMAX=4 the same argument shows that the hook keeps every (H) graph with σ ≤ 4, now by
`search_reduction_four`. That theorem also gives n ≤ 15 and minimum degree at least n − 11, so
the search runs `geng -c` for n ≤ 14 and `geng -c -d4` for n = 15.

| n | `geng` flags | graphs after pruning | (H) graphs with σ ≤ 4 | of which σ = 4 | time |
| --- | --- | ---: | ---: | ---: | ---: |
| 2–9 | `-c` | 1, 2, 6, 21, 111, 808, 7,623, 54,274 | 1, 2, 5, 15, 50, 235, 1,311, 17,112 | 0, 0, 0, 1, 8, 67, 1,018, 17,012 | < 0.1 s each |
| 10 | `-c` | 133,566 | 33,462 | 33,433 | 0.7 s |
| 11 | `-c` | 136,772 | 7,186 | 7,186 | 6.1 s |
| 12 | `-c` | 166,081 | 2,044 | 2,044 | 53 s |
| 13 | `-c` | 341,208 | 285 | 285 | 8.6 min |
| 14 | `-c` | 1,001,800 | 0 | 0 | 23 min on 4 cores |
| 15 | `-c -d4` | 23 | 0 | 0 | 25 min on 4 cores |

Up to n = 13 the times are CPU time. For n = 14 and 15 they are wall-clock times for 128 res/mod
pieces, four at a time. For n ≤ 11 the pruned search finds exactly the σ = 4 (H) graphs of the
unpruned search, and for n ≤ 10 plain `geng` gives the same graph6 strings. Every (H) graph found
is traceable. `hyp189`, `ind189` and `certify.py --sigma4` agree on the graphs that pass the
pruning. [`sigma4_certificates.txt`](sigma4_certificates.txt) lists the 61,054 graphs with
σ = 4 in graph6, each with a Hamiltonian path. The (H) graphs with σ ≤ 3 that this search finds
are those of `sigma3_certificates.txt`.

2,243 of the σ = 4 graphs (1,973 at n = 12 and 270 at n = 13) are 2-connected, have diameter at
least 3 and have n ≥ 2σ + 4, so Theorem B of Easwar and Johari does not cover them.
[`DETAILS.md`](DETAILS.md) describes what the σ = 4 graphs show about the extremal cases, and
why the same search is out of reach for σ = 5.

## Reproduction

```bash
python3 certify.py sigma3_certificates.txt
python3 certify.py --sigma4 sigma4_certificates.txt
```

These are the CI checks. The first takes under a second and the second about 2 s. The full
searches need a C compiler and the nauty 2.9.3 source, unpacked and configured (`./configure`):

```bash
bash reproduce.sh /path/to/nauty2_9_3
```

`reproduce.sh` builds `hyp189`, `ind189` and `geng189`, which is `geng` with the hook. It runs
the unpruned search for n ≤ `FULL_MAX` (default 10; `FULL_MAX=11` reproduces the table), the
σ ≤ 3 search for n ≤ 16 and the σ ≤ 4 search for n ≤ 15. For n ≤ 10 it checks that plain
`geng` gives the same σ ≤ 3 and σ = 4 (H) graphs as the pruned searches. It also checks that
the certificates it regenerates list the same graphs as the committed ones. It stops on any
disagreement or counterexample. `SIGMA_MAX` and `SIGMA4_MAX` lower the largest order of the two
pruned searches, and `FULL_MAX=2 SIGMA_MAX=2` runs essentially only the σ ≤ 4 search. Times on
an Apple-silicon machine:

- the unpruned search runs `geng` into both checkers in one pipeline. It takes about 5 s for
  n ≤ 10 and about 7 min for n = 11 (wall-clock);
- the σ ≤ 3 search takes, in CPU time, under a minute for n ≤ 13, 9 min for n = 14, 76 min for
  n = 15 and 7.7 h for n = 16;
- the σ ≤ 4 search takes, in CPU time, about 10 min for n ≤ 13. With `JOBS=4`, n = 14 and
  n = 15 take about 25 min each (wall-clock). The whole σ ≤ 4 part, checks included, took
  53 min wall-clock and 3.3 CPU-hours.

`reproduce.sh` splits the larger orders (n ≥ 14 for σ ≤ 3, n ≥ 13 for σ ≤ 4) into pieces with
`geng`'s res/mod option and runs `JOBS` of them in parallel (default 4).

## Statement faithfulness

- `AgenticConjectures.WowiiGraphConjecture189.statement` is the universal closure of upstream
  `conjecture189` ([snapshot](upstream/README.md)). `distEven`, `degreeSequence` and
  `secondSmallestDegree` are copied term for term.
- dist_even(v) counts v itself, as upstream and Easwar–Johari do. The reading that leaves v out
  is false: in the claw K₁,₃, each leaf has two other vertices at even distance and the centre
  has none, so the maximum is 2 = 1 + σ, yet the claw has no Hamiltonian path.
- σ(G) is the second entry of the sorted degree sequence, counted with multiplicity. So σ equals
  the minimum degree when two vertices attain it. This matches upstream `secondSmallestDegree`
  and Easwar–Johari's d₂.
- The C and Python programs use the same definitions on graph6 input with exact integer
  arithmetic. The search half of items 5–7 is not formalized in Lean. Lean only certifies the
  reduction (items 1–4, `search_reduction` and `search_reduction_four`).
- **Toolchain.** This repository builds with Lean and mathlib `v4.30.0`; Formal Conjectures at
  `c094b97` pins `v4.33.1` (mathlib `0df444a`). The mathlib declarations the statement uses
  (`Connected`, `dist`, `edist`, `degree`, `neighborFinset`, `Walk.support`,
  `Walk.IsHamiltonian` and `Multiset.sort`) are textually identical in the two versions.
  `SimpleGraph` changed only the type of its proof field `symm` (`Std.Symm Adj` instead of
  `Symmetric Adj`), which leaves `Adj` unchanged. The module has not been compiled against
  `v4.33.1`.

## Prior art and scope

- R. Easwar and S. Johari, *Conditions for traceability under a bound on the size of
  even-distance sets*, [arXiv:2609.11719](https://arxiv.org/abs/2609.11719) (2026). Their Theorem B
  shows that G satisfying (H) is traceable in each of these cases:
  - diam ≤ 2;
  - n ≤ 2σ + 2;
  - n = 2σ + 3 and G is 2-connected;
  - G is not 2-connected.

  Item 1 above reproduces their first case by the same Ore argument. The paper reports no
  computations.
- O. Ore, *Note on Hamilton circuits*, Amer. Math. Monthly 67 (1960), 55. The path version is
  the form Easwar–Johari use.
- We did not find the bounds n ≤ (σ + 1)² and n ≤ 2σ + 1 + ⌊(σ + 1)²/4⌋, the σ ≤ 3 and σ ≤ 4
  reductions or the searches in the sources we checked. This is not a novelty claim.

No human has reviewed these results. They were produced by an AI model and are checked only by
the Lean kernel, the two independent checkers and the certificate script. Nothing has been
submitted to Formal Conjectures, to the WOWII maintainer or anywhere else; any external
submission needs human approval.

## Files

- [`DETAILS.md`](DETAILS.md): proof of the sharper order bound, what the σ = 4 graphs show, the
  σ = 5 benchmark and approaches that did not work.
- [`certify.py`](certify.py), [`sigma3_certificates.txt`](sigma3_certificates.txt) and
  [`sigma4_certificates.txt`](sigma4_certificates.txt): Hamiltonian-path certificates for the
  σ ≤ 3 and σ = 4 cases.
- [`hyp189.c`](hyp189.c), [`ind189.c`](ind189.c) and [`prune189.c`](prune189.c): search
  programs.
- [`reproduce.sh`](reproduce.sh): builds and runs the searches.
- [`search_summary.txt`](search_summary.txt): raw per-order summary lines from the runs.
- [`upstream/`](upstream/README.md): Formal Conjectures snapshot.
