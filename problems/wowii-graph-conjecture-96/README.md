**English** | [한국어](README.ko.md)

# WOWII Graph Conjecture 96

## The conjecture

Conjecture 96 of E. DeLaViña's *Written on the Wall II* (conjectures of the
program Graffiti.pc) is dated April 21, 2004 and is listed with status `O`
(open). The row reads:

> If G is a simple connected graph, then α(G) ≤ 1 + minimum dist_even(v)*(maximum of λ(v) -1)

This is the text of the
[2026-07-26 Wayback capture](https://web.archive.org/web/20260726061534/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/all.html)
of the list. The HTML source writes α and λ as the letters `a` and `l` in the
Symbol font, and `even` as a subscript of `dist`. The definitions that the row
links to (the list's `wowIIdefs.js`,
[2023-09-01 capture](https://web.archive.org/web/20230901203307/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/wowIIdefs.js))
are the following.

- \(\alpha(G)\) is the independence number.
- \(\operatorname{dist}_{\mathrm{even}}(v)\) is the number of vertices whose
  distance from \(v\) is even. Distance 0 is even, so \(v\) itself counts.
- \(\lambda(v)\) is the independence number of the subgraph induced by the
  neighbours of \(v\).

Minimum and maximum are taken over all vertices. In symbols, the conjecture is

\[
\alpha(G)\le 1+\Bigl(\min_v\operatorname{dist}_{\mathrm{even}}(v)\Bigr)
\Bigl(\max_v\lambda(v)-1\Bigr).
\]

### Why the formal statement assumes at least two vertices

Read literally, the row is false for the one-vertex graph \(K_1\). There
\(\alpha=1\), \(\min\operatorname{dist}_{\mathrm{even}}=1\) and
\(\max\lambda=0\), so the right-hand side is \(1+1\cdot(0-1)=0<1\).

The Formal Conjectures statement therefore adds the hypothesis
`[Nontrivial α]`, which means at least two vertices, and its docstring gives
this reason. Our theorem is exactly that statement. It proves the inequality
for every connected graph with at least two vertices, and claims nothing about
\(K_1\) beyond the failure above. The same \(K_1\) failure was formalized
earlier by another project (see [Prior art and status](#prior-art-and-status)).

## Result

**Theorem.** Let \(G\) be a finite simple connected graph with at least two
vertices. Then

\[
\alpha(G)\le 1+\Bigl(\min_v\operatorname{dist}_{\mathrm{even}}(v)\Bigr)
\Bigl(\max_v\lambda(v)-1\Bigr).
\]

The bound is tight:

- Every star \(K_{1,m}\) with \(m\ge1\) attains it. At the centre
  \(\operatorname{dist}_{\mathrm{even}}=1\), and \(\max\lambda=\alpha=m\).
- Every complete graph \(K_n\) with \(n\ge2\) attains it, since
  \(\alpha=\max\lambda=1\).

The proof gives a bound for every root \(v\), not only for a vertex that
minimises \(\operatorname{dist}_{\mathrm{even}}\). For every connected graph
(including \(K_1\)) and every vertex \(v\),

\[
\alpha(G)\le\max\bigl(1,\lambda(v)\bigr)
+\sum_{\substack{u\ne v\\ d(v,u)\text{ even}}}\max\bigl(1,\lambda(u)-1\bigr).
\tag{per-root}
\]

Bound each term by \(\Lambda=\max_u\lambda(u)\), assuming \(\Lambda\ge2\). The
right-hand side becomes
\(\Lambda+(\operatorname{dist}_{\mathrm{even}}(v)-1)(\Lambda-1)
=1+\operatorname{dist}_{\mathrm{even}}(v)(\Lambda-1)\).

## Proof idea

Write \(\Lambda=\max_u\lambda(u)\), \(E(v)=\operatorname{dist}_{\mathrm{even}}(v)\)
and \(d\) for the graph distance.

1. With at least two vertices, every vertex has a neighbour, so
   \(\lambda(u)\ge1\) for all \(u\) and \(\Lambda\ge1\).
2. Suppose \(\Lambda=1\), and suppose two vertices are non-adjacent. Then some
   vertex \(x\) has a vertex \(w\) at distance exactly 2, with a common
   neighbour \(y\). The pair \(\{x,w\}\) is independent in the neighbourhood
   of \(y\), so \(\lambda(y)\ge2\), a contradiction. Hence \(G\) is complete,
   and \(\alpha=1\) equals the right-hand side.
3. Suppose \(\Lambda\ge2\). Fix a root \(v\) and a maximum independent set
   \(I\). Send each \(x\in I\) to itself when \(d(v,x)\) is even. Otherwise send
   it to a BFS parent, a neighbour one step closer to \(v\). Every image is at
   even distance from \(v\). Now count \(|I|\) by fibres.
   - Over \(u\in I\), the fibre is \(\{u\}\). Any other vertex of the fibre
     would be a vertex of \(I\) adjacent to \(u\).
   - Over \(u\notin I\), the fibre is an independent set of neighbours of
     \(u\). So it has at most \(\lambda(u)\) elements.
   - Over \(u\notin I\) with \(u\ne v\), we can do better. The parent of \(u\)
     is at distance \(d(v,u)-1\) from \(v\), while the fibre is at distance
     \(d(v,u)+1\). So the parent is adjacent to no fibre vertex, and adding it
     keeps the set independent. Hence the fibre has at most \(\lambda(u)-1\)
     elements.

   Summing over the \(E(v)\) vertices at even distance gives the per-root
   bound. That bound is at most
   \(\Lambda+(E(v)-1)(\Lambda-1)=1+E(v)(\Lambda-1)\). Taking \(v\) with
   \(E(v)\) minimal proves the theorem.

[DETAILS.md](DETAILS.md) gives every step with the Lean lemma that proves it.

## Lean formal proof

[`AgenticConjectures/WowiiGraphConjecture96.lean`](../../AgenticConjectures/WowiiGraphConjecture96.lean)
proves the upstream theorem. It uses no `sorry`, no extra axioms and no
`native_decide`. `#print axioms` lists only `propext`, `Classical.choice` and
`Quot.sound`.

| Declaration | Content |
| --- | --- |
| `conjecture96` | The upstream statement, verbatim, under `[Nontrivial α]` and `G.Connected`. |
| `statement`, `statement_holds` | The same statement quantified over all finite vertex types, and its proof. |
| `indepNum_le_perRoot` | The per-root bound, for every connected graph and every root. |
| `indepNum_le_of_two_le` | \(\alpha\le1+E(v)(L-1)\) when every \(\lambda(u)\le L\) and \(L\ge2\). |
| `indepNum_le_one` | \(\alpha\le1\) when every \(\lambda(u)\le1\). |
| `one_le_indepNeighborsCard` | \(\lambda(u)\ge1\) when there are at least two vertices. |
| `exists_parent`, `exists_dist_two` | A BFS parent exists, and a vertex at distance exactly 2 exists. |
| `card_le_indepNeighborsCard`, `two_le_indepNeighborsCard` | Independent sets of neighbours give lower bounds on \(\lambda\). |

## Statement faithfulness

- **Definitions.** `distEven` and `indepNeighborsCard` are copied term for term
  from FormalConjecturesForMathlib at commit `c094b97`. They are at line 396
  of `Combinatorics/SimpleGraph/VertexDistance.lean` and line 40 of
  `Combinatorics/SimpleGraph/Independence.lean`, and use the same section
  variables. Only the namespace differs: they are in
  `AgenticConjectures.WowiiGraphConjecture96`, not `SimpleGraph`.
- **Match with the source definitions.** `distEven G v` counts the `w` with
  `Even (G.dist v w)`, so `v` itself is included. `indepNeighborsCard G v` is
  the independence number of the subgraph induced by `G.neighborSet v`, the
  open neighbourhood. Mathlib's `G.dist` is 0 for unreachable pairs, but \(G\)
  is connected, so it is the usual distance.
- **Statement.** The text of `conjecture96` is the upstream theorem verbatim.
  We drop only the `@[category research open, AMS 5]` attribute and the
  `module`/`public`/`@[expose]` keywords, and import `Mathlib` instead of
  `FormalConjecturesUtil`.
- **Toolchain.** This repository builds with Lean and mathlib `v4.30.0`;
  Formal Conjectures at `c094b97` pins `v4.33.1` (mathlib `0df444a`). The graph
  declarations the statement uses (`indepNum`, `IsNIndepSet`, `IsIndepSet`,
  `dist`, `edist`, `Walk`, `Walk.length`, `Reachable`, `Connected`, `induce`,
  `neighborSet`) are textually identical in the two versions. `SimpleGraph`
  changed its `symm` field from `Symmetric Adj` to the equivalent
  `Std.Symm Adj`, and `SimpleGraph.comap` changed only proof fields. The
  statement therefore means the same in both versions, but the proof has been
  compiled only against `v4.30.0`.
- **At least two vertices.** `[Nontrivial α]` is the deliberate upstream
  restriction explained above. It also makes `Finset.univ.image …` nonempty,
  so `min'` and `max'` are the minimum and maximum over all vertices.
- **Subtraction.** The inequality is stated in \(\mathbb R\), so
  \(\max\lambda-1\) is signed subtraction, as in the source. The proof shows
  \(\max\lambda\ge1\), so this equals the natural-number difference used
  inside the proof. In the per-root bound, \(\lambda(u)-1\) is natural-number
  subtraction inside \(\max(1,\cdot)\), where truncation never matters.
- **Mechanical check.**
  [`upstream_statement_check.lean`](upstream_statement_check.lean) declares
  the two definitions again in their upstream namespace `SimpleGraph`. It then
  restates the upstream theorem in its upstream namespace
  `WrittenOnTheWallII.GraphConjecture96`, and closes it with our
  `conjecture96`. Elaboration has to unfold the upstream constants to ours, so
  any mismatch would make the file fail. It prints the three standard axioms.
  The file is not imported by the library.

## Numerical cross-check

The Lean proof is the certificate. [`verify_wowii96.py`](verify_wowii96.py) is
an independent brute-force check of both the conjecture and the per-root
bound, using only the Python standard library.

| Input | Graphs | (graph, root) pairs | Conjecture tight | Per-root tight | Time |
| --- | ---: | ---: | ---: | ---: | ---: |
| Default (CI) mode: all labelled graphs with \(n=2,\dots,6\), plus stars \(K_{1,m}\), \(m\le12\) | 27,487 | 164,120 | 9,455 | 45,622 | 0.7 s |
| `geng -c`, \(n=2,\dots,9\) | 273,192 | 2,445,436 | 14,917 | 73,458 | 22 s |
| `geng -c`, \(n=10\), in three parts | 11,716,571 | 117,165,710 | 279,788 | 1,188,438 | 9.1 min wall, 23.2 min CPU |

- No run found a violation, and the minimum slack is 0 in every run.
- The labelled counts for each order match OEIS A001187. The `geng` totals
  match A001349.
- Default mode also checks equality on the stars and the \(K_1\) failure of
  the literal row.
- A second implementation in C, [`check_wowii96.c`](check_wowii96.c), reports
  the same graph, pair and tight counts on both `geng` inputs, including the
  per-root tight counts 73,458 for \(n\le9\) and 1,188,438 for \(n=10\). It
  shares no code with the Python script: it has its own graph6 parser and finds
  independence numbers by branching. It takes 0.2 s for \(n\le9\) and 6 s for
  \(n=10\), and `--selftest` checks hand-computed invariants of small graphs,
  including \(K_1\), the stars and the Petersen graph.

## Prior art and status

- **WOWII.** Row 96 has status `O` in the
  [2026-07-26 capture](https://web.archive.org/web/20260726061534/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/all.html)
  of the list. It does not appear on either list of resolved conjectures
  ([resolved.htm](https://web.archive.org/web/20260723211227/http://cms.uhd.edu/faculty/delavinae/research/wowII/resolved.htm)
  and
  [resolvedT.htm](https://web.archive.org/web/20260723211215/http://cms.uhd.edu/faculty/delavinae/research/wowII/resolvedT.htm),
  2026-07-23 captures).
- **Formal Conjectures.** `conjecture96` was added by
  [google-deepmind/formal-conjectures#3796](https://github.com/google-deepmind/formal-conjectures/pull/3796),
  merged on 2026-10-23. It is marked `research open` and closed by `sorry` at
  `c094b97` and at `main` `37f0808` (2026-10-24). Searches of that
  repository's issues and pull requests for `conjecture96` and
  `GraphConjecture96` returned nothing (2026-10-25 UTC).
- **txmy/ultra-mathematician.** A run of 2026-07-25 in
  [txmy/ultra-mathematician](https://github.com/txmy/ultra-mathematician/tree/d52f81ad64dfc77e9a89dee8ae97db983ac6d5f7/runs/run-2026-07-25-001/tasks/audit-wowii-96-final)
  formalized the \(K_1\) counterexample to the literal row. Its audit notes
  that the `[Nontrivial α]` version, then in the pull request above, was
  unproved. It does not address graphs with at least two vertices.
- **Kuberwastaken/c5-k4.** This repository evaluates conjecture 96 on a single
  graph, where it holds.
- **Literature.** Searches of arXiv, Zenodo/OpenAlex and GitHub code (for
  `GraphConjecture96`, `dist_even`, and "Written on the Wall") found no proof
  (2026-10-25 UTC).

Not finding a proof does not establish novelty, and none is claimed. No human
has reviewed this proof or its formalization; it was produced by an AI model
and is checked only by the Lean kernel and the numerical cross-checks. It has
not been submitted to Formal Conjectures, to the WOWII maintainer, or anywhere
else; any external submission needs human approval.

## Reproduction

From the repository root:

```bash
lake build AgenticConjectures.WowiiGraphConjecture96
lake env lean problems/wowii-graph-conjecture-96/upstream_statement_check.lean
python3 scripts/check_axioms.py
```

Once mathlib is built, the module compiles in about 4 s and the upstream check
runs in about 4 s.

From this directory (the `geng` runs need nauty, and `check_wowii96.c` needs a
C compiler):

```bash
python3 verify_wowii96.py
for n in 2 3 4 5 6 7 8 9; do geng -cq $n; done | python3 verify_wowii96.py --graph6
for k in 0 1 2; do geng -cq 10 $k/3 | python3 verify_wowii96.py --graph6; done
cc -O2 -o /tmp/check_wowii96 check_wowii96.c && /tmp/check_wowii96 --selftest
for n in 2 3 4 5 6 7 8 9; do geng -cq $n; done | /tmp/check_wowii96
geng -cq 10 | /tmp/check_wowii96
```

The [upstream snapshot](upstream/README.md) keeps the exact Formal
Conjectures source.
