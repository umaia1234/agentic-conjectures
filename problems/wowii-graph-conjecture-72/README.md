**English** | [한국어](README.ko.md)

# WOWII Graph Conjecture 72

## The conjecture

Conjecture 72 of E. DeLaViña's *Written on the Wall II* (conjectures of the
program Graffiti.pc) is dated April 4, 2004 and is listed with status `O`
(open). The row reads:

> If G is a simple connected graph, then tree(G) ≥ CEIL[average of ecc(v) + maximum of λ(v) /3]

This is the text of the
[2026-07-26 Wayback capture](https://web.archive.org/web/20260726061534/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/all.html)
of the list. The HTML source writes λ as the letter `l` in the Symbol font. The
definitions that the row links to (the list's `wowIIdefs.js`,
[2023-09-01 capture](https://web.archive.org/web/20230901203307/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/wowIIdefs.js),
entries 48, 21, 4 and 16) are the following.

- \(\operatorname{tree}(G)\) is the number of vertices of a largest induced
  tree of \(G\).
- \(\operatorname{ecc}(v)\) is the eccentricity of \(v\), the largest distance
  from \(v\) to a vertex of \(G\).
- \(\lambda(v)\) is the independence number of the subgraph induced by the
  neighbours of \(v\).
- \(\operatorname{CEIL}[x]\) is the smallest integer that is at least \(x\).

The average and the maximum are taken over all vertices. Write
\(A=\frac1n\sum_v\operatorname{ecc}(v)\) and \(L=\max_v\lambda(v)\).

### Two readings

The row does not say what `/3` divides.

- **Formal Conjectures reading.** The formal statement in
  google-deepmind/formal-conjectures divides only \(L\):
  \[
  \operatorname{tree}(G)\ \ge\ \bigl\lceil A+L/3\bigr\rceil .
  \]
  **This reading is false.** That was already stated publicly on 2026-07-23
  (see [Prior art and status](#prior-art-and-status)); this directory adds a
  Lean refutation.
- **Evenly divided reading.** \(\operatorname{tree}(G)\ge\lceil(A+L)/3\rceil\).
  This reading is true, by a short argument from a public post of 2026-07-23
  (see [Prior art and status](#prior-art-and-status)). A shortest path between
  two vertices at maximum distance \(D\) is induced, so
  \(\operatorname{tree}(G)\ge D+1\ge A+1\). A vertex together with a largest
  independent set of its neighbours induces a star, so
  \(\operatorname{tree}(G)\ge L+1\). Hence \(A+L\le2\operatorname{tree}(G)-2\).
  This repository does not formalize that argument.

Nothing here decides which reading Graffiti.pc or the list's author intended.

## Result

**Theorem.** The Formal Conjectures statement
`WrittenOnTheWallII.GraphConjecture72.conjecture72` (commit `c094b97`) is false.
There is a connected graph \(G\) on 28 vertices with
\(\operatorname{tree}(G)=7\), \(A=75/14\) and \(L=5\), so that
\[
\bigl\lceil A+L/3\bigr\rceil=\bigl\lceil 295/42\bigr\rceil=8>7=\operatorname{tree}(G).
\]

The falsity of this statement is not new; see
[Prior art and status](#prior-art-and-status). No human has reviewed this
refutation yet.

The graph \(G\) ([`g28.txt`](g28.txt)) consists of the following parts:

- a clique \(K_{11}\) on \(q_1,\dots,q_{10},p_0\);
- the edge \(p_0p_1\);
- four pairwise non-adjacent vertices \(m_1,\dots,m_4\), each adjacent to
  \(p_1\) and to \(p_3\);
- the edge \(p_3p_4\);
- a clique \(K_{11}\) on \(p_4,r_1,\dots,r_{10}\).

It has 120 edges. In the labels of `g28.txt` and of the Lean file,
\(p_0,p_1,m_1,\dots,m_4,p_3,p_4\) are the vertices \(0,\dots,7\), the \(q_i\)
are \(8,\dots,17\) and the \(r_i\) are \(18,\dots,27\).

| Vertices | \(q_i\), \(r_i\) | \(p_0\), \(p_4\) | \(p_1\), \(p_3\) | \(m_i\) |
| --- | ---: | ---: | ---: | ---: |
| Count | 20 | 2 | 2 | 4 |
| \(\operatorname{ecc}(v)\) | 6 | 5 | 4 | 3 |
| \(\lambda(v)\) | 1 | 2 | 5 | 2 |

So \(\sum_v\operatorname{ecc}(v)=120+10+8+12=150\) and \(A=150/28=75/14\). The
maximum \(L=5\) is attained at \(p_1\), whose neighbours
\(p_0,m_1,\dots,m_4\) are pairwise non-adjacent, and at \(p_3\). The set
\(\{q_1,p_0,p_1,m_1,\dots,m_4\}\) induces a tree on 7 vertices, and no 8
vertices induce a tree. The evenly divided reading holds on \(G\):
\(\lceil(A+L)/3\rceil=\lceil145/42\rceil=4\le7\).

## Proof idea

Give each vertex a level: 0 for the \(q_i\), 1 for \(p_0\), 2 for \(p_1\), 3 for
the \(m_i\), 4 for \(p_3\), 5 for \(p_4\) and 6 for the \(r_i\). Two distinct
vertices are adjacent exactly when their levels differ by 1, or both levels
are 0, or both are 6.

1. **Average eccentricity.** Along an edge the level changes by at most 1, so
   the distance between two vertices is at least the difference of their
   levels. A vertex of level \(\ell\) is therefore at distance at least
   \(\max(\ell,6-\ell)\) from \(q_1\) or \(r_1\). These bounds add up to 150,
   so \(A\ge75/14\).
2. **Local independence.** The five neighbours of \(p_1\) are pairwise
   non-adjacent, so \(L\ge\lambda(p_1)\ge5\).
3. **Induced trees.** Let \(T\) induce a tree.
   - Three vertices of a clique form a triangle, so \(T\) contains at most two
     vertices of each \(K_{11}\).
   - If \(p_1,p_3\in T\), two of the \(m_i\) would close the 4-cycle
     \(p_1m_ip_3m_j\), so \(T\) has at most one \(m_i\). That gives at most
     \(2+1+1+1+2=7\) vertices.
   - If \(p_1\in T\) and \(p_3\notin T\), no path inside \(T\) can pass from
     level 3 to level 5. Since \(T\) is connected, it misses the second
     clique, so \(|T|\le2+1+4=7\). The case \(p_3\in T\), \(p_1\notin T\) is
     symmetric.
   - If \(p_1,p_3\notin T\), every \(m_i\) is isolated in \(T\). So either
     \(T=\{m_i\}\), or \(T\) lies in the two cliques and \(|T|\le4\).

   Hence \(\operatorname{tree}(G)\le7\), and
   \(\operatorname{tree}(G)\le7<8\le\lceil75/14+5/3\rceil\le\lceil A+L/3\rceil\).

[DETAILS.md](DETAILS.md) gives every step with the Lean lemma that proves it.

## Lean formal proof

[`AgenticConjectures/WowiiGraphConjecture72.lean`](../../AgenticConjectures/WowiiGraphConjecture72.lean)
refutes the upstream statement. It uses no `sorry`, no extra axioms and no
`native_decide`; the small facts about the 28 levels are checked by `decide`
in the kernel. `#print axioms` lists only `propext`, `Classical.choice` and
`Quot.sound`.

| Declaration | Content |
| --- | --- |
| `statement`, `refuted` | The upstream statement for every vertex type `α : Type u`, and its negation, in every universe. |
| `graph`, `graph_connected` | The counterexample on any type `V ≃ Fin 28`, and its connectivity. |
| `averageEccentricity_ge` | \(A\ge150/28\), from `ecc_ge` and `sum_lvl`. |
| `five_le_indepNeighborsCard` | \(\lambda(p_1)\ge5\). |
| `card_le_seven`, `largestInducedTreeSize_le` | Every induced tree has at most 7 vertices, so \(\operatorname{tree}(G)\le7\). |
| `tree_lt_ceil` | \(\operatorname{tree}(G)<\lceil A+L/3\rceil\) for the counterexample. |
| `not_isAcyclic_of_triangle`, `not_isAcyclic_of_square`, `of_preserved` | An induced subgraph containing a triangle or a 4-cycle is not acyclic; a property that passes along the edges of a connected induced subgraph holds on all of it. |
| `card_le_indepNeighborsCard` | An independent set of neighbours of \(u\) bounds \(\lambda(u)\) from below. |

## Statement faithfulness

The refuted declaration, verbatim from lines 40 and 52–56 of
[`upstream/GraphConjecture72.lean`](upstream/GraphConjecture72.lean):

```lean
variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

@[category research open, AMS 5]
theorem conjecture72 (G : SimpleGraph α) (h : G.Connected) :
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    ⌈averageEccentricity G + (maxL : ℝ) / 3⌉ ≤ (largestInducedTreeSize G : ℝ) := by
  sorry
```

- **Definitions.** `averageEccentricity`, `largestInducedTreeSize` and
  `indepNeighborsCard` are copied term for term from
  FormalConjecturesForMathlib at commit `c094b97`. They are at line 34 of
  `Combinatorics/SimpleGraph/Eccentricity.lean`, line 39 of
  `Combinatorics/SimpleGraph/LargestInducedTree.lean` and line 40 of
  `Combinatorics/SimpleGraph/Independence.lean`, and use the same section
  variables. Only the namespace differs: they are in
  `AgenticConjectures.WowiiGraphConjecture72`, not `SimpleGraph`.
- **Match with the source definitions.** `averageEccentricity G` is
  \(\frac1n\sum_v\) of `(G.eccent v).toNat`. For a connected finite graph
  `G.eccent v` is finite and equals \(\operatorname{ecc}(v)\), so this is
  \(A\). `largestInducedTreeSize G` is the supremum of the orders of vertex
  sets that induce a tree, which is \(\operatorname{tree}(G)\) because that set
  of orders is finite. `indepNeighborsCard G v` is the independence number of
  the subgraph induced by the open neighbourhood, which is \(\lambda(v)\).
- **Statement.** `statement` is the upstream theorem with its hypotheses and
  conclusion copied verbatim, quantified over every vertex type `α : Type u`
  (bound explicitly; the hypothesis `h` is unnamed). The ceiling is
  `Int.ceil`, the division by 3 is real division of \(L\) alone, and both
  sides are compared in \(\mathbb R\). No natural-number subtraction occurs.
  `import Mathlib` replaces `FormalConjecturesUtil`, and the
  `@[category research open, AMS 5]` attribute and the
  `module`/`public`/`@[expose]` keywords are dropped.
- **Hypotheses.** The counterexample satisfies the upstream hypotheses
  `[Fintype α] [DecidableEq α] [Nontrivial α]` and `G.Connected`. Upstream's
  `α : Type*` is universe polymorphic; `refuted` holds for every universe,
  with the counterexample on `ULift (Fin 28)`.
- **Mechanical check.**
  [`upstream_statement_check.lean`](upstream_statement_check.lean) declares
  the three definitions again in their upstream namespace `SimpleGraph`. It
  then states the upstream theorem as a proposition in its upstream namespace
  `WrittenOnTheWallII.GraphConjecture72`, and refutes it with our `refuted`.
  Elaboration has to unfold the upstream constants to ours, so any mismatch
  would make the file fail. It prints the three standard axioms. Four
  perturbed copies, run outside the repository, fail as expected: the
  statement with `/ 2` instead of `/ 3`, and each definition changed in turn
  (dividing by \(n+1\), counting induced forests, and using the clique number
  of the neighbourhood). The file is not imported by the library.
- **Toolchain.** This repository builds with Lean and mathlib v4.30.0, while
  Formal Conjectures at `c094b97` pins v4.33.1. The graph definitions the
  statement uses (`eccent`, `edist`, `dist`, `IsAcyclic`, `IsTree`, `induce`,
  `neighborSet`, `indepNum`, `Connected`) are textually identical in the two
  versions. The only change in `SimpleGraph` is the type of the proof field
  `symm` (`Std.Symm Adj` instead of `Symmetric Adj`), which leaves `Adj`
  unchanged. The refutation has not been compiled against v4.33.1.
- **Scope.** Only the Formal Conjectures reading is refuted. The evenly
  divided reading is not formalized here, and nothing is claimed about which
  reading the list intends.

## Numerical cross-check

The Lean proof is the certificate. [`verify_wowii72.py`](verify_wowii72.py)
recomputes the counterexample with an independent implementation, using only
the Python standard library and exact fractions.

- It rebuilds the graph from the level rule and checks that it equals
  `g28.txt`.
- It computes every eccentricity by breadth-first search (sum 150) and every
  \(\lambda(v)\) by exhaustive search (maximum 5).
- It computes \(\operatorname{tree}(G)=7\) twice. The first method grows every
  induced tree by one leaf at a time. The second tests every vertex subset of
  order at most 8: by deleting leaves, an induced tree on more than 8 vertices
  would contain one on exactly 8. The two methods agree at every order: there
  are 28, 120, 44, 108, 214, 162 and 420 induced trees of orders 1 to 7, and
  none of order 8.
- It checks \(\lceil75/14+5/3\rceil=8>7\) and \(\lceil(75/14+5)/3\rceil=4\le7\),
  and checks the invariants on paths, cycles, complete graphs and stars.

The default (CI) mode takes about 6 s. With `--graph6` the script evaluates
both readings on every connected graph that `geng` produces.

| Input | Graphs | \(\lceil A+L/3\rceil=\operatorname{tree}\) | Minimum of \(\operatorname{tree}-(A+L/3)\) | Violations | Time |
| --- | ---: | ---: | ---: | ---: | ---: |
| `geng -c`, \(n=2,\dots,9\) | 273,192 | 1,407 | 1/3 | 0 | 49 s |
| `geng -c`, \(n=10\), in three parts | 11,716,571 | 3,761 | 4/15 | 0 | 29.2 min wall, 74.9 min CPU |

The graph totals match OEIS A001349. Neither reading fails on any graph with at
most 10 vertices, so a counterexample to the formal statement needs more than
10 vertices.

## Prior art and status

- **WOWII.** Row 72 has status `O` in the
  [2026-07-26 capture](https://web.archive.org/web/20260726061534/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/all.html)
  of the list. It does not appear on either list of resolved conjectures
  ([resolved.htm](https://web.archive.org/web/20260723211227/http://cms.uhd.edu/faculty/delavinae/research/wowII/resolved.htm)
  and
  [resolvedT.htm](https://web.archive.org/web/20260723211215/http://cms.uhd.edu/faculty/delavinae/research/wowII/resolvedT.htm),
  2026-07-23 captures).
- **Public claim (2026-07-23).** An
  [X post by @4thRT](https://x.com/4thRT/status/2080412225232400539),
  produced with the model GPT 5.6 Sol, proves the evenly divided reading. It
  also states that the reading which divides only \(L\) by three, the one
  Formal Conjectures later chose, is false on a family of graphs. The tracker
  VibeMathed
  [records the post](https://vibemathed.com/problem/wowii-conjecture-72-two-induced-trees-pin-down-tree-g)
  with status "Candidate", and re-derived the proved reading on 2026-08-17.
  **The falsity of the formal statement is therefore not new.** We did not
  compare our graph with the family in that post.
- **Formal Conjectures.** `conjecture72` was added by
  [google-deepmind/formal-conjectures#3796](https://github.com/google-deepmind/formal-conjectures/pull/3796)
  (commit `4eee17c`, 2026-10-23). It is marked `research open` and closed by
  `sorry` at `c094b97` and at `main` `37f0808` (2026-10-24), and no later
  commit touches the file. Searches of that repository's issues and pull
  requests for `GraphConjecture72` and `conjecture72` returned nothing
  (2026-10-25 UTC).
  In the review of #3796 the first draft divided the whole sum by 3; the
  reviewer asked to keep the grouping displayed in the source row, and the
  merged statement divides only \(L\).
- **Formal artifacts.** GitHub code searches for `GraphConjecture72` and
  `conjecture72` (2026-10-25 UTC) found no formal proof or disproof of either
  reading. Apart from the upstream file, they return only the tracker's review
  script and an unrelated identifier that contains `conjecture7292`.

No human has reviewed the Lean refutation. It has not been submitted to
Formal Conjectures, to the WOWII maintainer, or anywhere else; any external
submission, such as a proposal to change the upstream statement, needs human
approval.

## Reproduction

From the repository root:

```bash
lake build AgenticConjectures.WowiiGraphConjecture72
lake env lean problems/wowii-graph-conjecture-72/upstream_statement_check.lean
python3 scripts/check_axioms.py
```

Once mathlib is built, the module compiles in about 4 s and the upstream check
runs in about 5 s.

From this directory (the `geng` runs need nauty):

```bash
python3 verify_wowii72.py
for n in 2 3 4 5 6 7 8 9; do geng -cq $n; done | python3 verify_wowii72.py --graph6
for k in 0 1 2; do geng -cq 10 $k/3 | python3 verify_wowii72.py --graph6; done
```

The [upstream snapshot](upstream/README.md) keeps the exact Formal
Conjectures source.
