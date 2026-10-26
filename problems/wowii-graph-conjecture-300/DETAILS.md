**English** | [한국어](DETAILS.ko.md)

# WOWII Conjecture 300: details

This file supports [README.md](README.md). It covers:

- the reading of the statement and its sources;
- full paper proofs for the family \(G_t\) and for the 12-vertex graph \(H\);
- rounding, and the reading without the complement;
- every computation, with its method and cross-checks;
- the smallest counterexamples;
- what is not covered.

Throughout, \(G\) is a finite simple connected graph with \(n\ge3\) vertices, \(N_G(v)\) is
the set of neighbours of \(v\), \(N_G[v]=N_G(v)\cup\{v\}\), and \(\omega\) is the clique
number. The conjecture was refuted before us: by a third-party audit of the live page, the
WOWII page records a refutation by William Weishuhn dated July 26, 2026 (see
[Blind spot and prior refutation](#blind-spot-and-prior-refutation)).

## Reading of the statement

Row 300 of the list (section "Upper bounds for Total Domination", Mar. 1, 2007, status `O` in
every capture we read, the last of 2026-07-26) says, in the notation of the list,
\(\gamma_t(G)\le\tfrac12[n(G)+\text{frequency of }\lambda_{\min}(\bar G)]\) for every simple
connected graph with \(n(G)>2\). It links entries 94, 3, 4 and 31 of the definitions file
`wowIIdefs.js` (capture of 2026-07-23):

- 94, total domination number: the size of a smallest set of vertices to which every vertex
  is adjacent;
- 3, the number of vertices;
- 4, local independence \(\lambda(v)\): the independence number of the subgraph induced by
  the neighbours of \(v\); \(\lambda_{\min}\) is the smallest value over the vertices;
- 31, the complement.

**"Frequency of".** The list does not define the phrase. Every use of a frequency that we
found counts vertices:

- definition 18, "frequency of degree one": the number of vertices of degree one;
- definition 62, "frequency of degree k": the number of occurrences of degree \(k\) among
  the vertices;
- the note of Oct. 2008 under Conjecture 303 (\(\gamma_t\le\deg_{\mathrm{avg}}(C)+\) frequency
  of \(\lambda_{\max}(\bar G)\)) describes its counterexample by \(\gamma_t=6\),
  \(\deg_{\mathrm{avg}}(C)=3.5\) and frequency of \(\lambda_{\max}(\bar G)\) equal to 2;
- the note of July 21, 2026 under Conjecture 209 describes a family of graphs on \(m+4\)
  vertices in which \(\lambda_{\max}=3\) "with frequency m".

So the frequency of \(\lambda_{\min}(\bar G)\) is
\(f(G)=|\{v:\lambda_{\bar G}(v)=\min_u\lambda_{\bar G}(u)\}|\), where
\(\lambda_{\bar G}\) is the local independence computed in \(\bar G\).

**The complement.** The HTML of row 300 draws a bar over the last G with
`<span style="text-decoration: overline">G</span>` in the captures of 2010-07-17,
2016-10-09, 2026-07-23 and 2026-07-26, and the row links definition 31. Conjecture 301, of the
same date and marked true, reads \(\gamma_t(G)\le\omega(G)+\) frequency of
\(\lambda_{\max}(\bar G)\). DeLaViña, Liu, Pepper, Waller and West prove it as Theorem 10 of
*Some conjectures of Graffiti.pc on total domination*, Congr. Numer. 185 (2007) 81–95, in the
form \(\gamma_t\le\omega+|A|\), where \(A\) is the set of vertices whose local independence in
\(\bar G\) is maximum. We read 300 with the same meaning of "frequency" and of the bar.

**No rounding.** The list writes CEIL and FLOOR where it means them (row 305, for example,
has CEIL). Row 300 has neither, so the bound \(\tfrac12(n+f)\) is a real number.

**Local independence in the complement.** The neighbours of \(v\) in \(\bar G\) are the
vertices outside \(N_G[v]\), and an independent set of \(\bar G\) is a clique of \(G\). So
\[
\lambda_{\bar G}(v)=\omega\bigl(G-N_G[v]\bigr),
\]
the clique number of the graph that remains after deleting \(v\) and its neighbours (0 if
nothing remains). All proofs below use this form. The Lean statement uses the definitions
directly: `indepNeighborsCard Gᶜ v` is the independence number of `Gᶜ` induced on the
neighbour set of `v` in `Gᶜ`.

**A violation needs \(2\gamma_t\ge n+2\).** \(f\ge1\), so \(\gamma_t>\tfrac12(n+f)\) forces
\(2\gamma_t\ge n+f+1\ge n+2\).

## The family \(G_t\)

For \(t\ge0\) let \(k=t+4\). The vertices of \(G_t\) are the hubs \(h_0,\dots,h_{k-1}\), the
middles \(m_0,\dots,m_{k-1}\) and the leaves \(\ell_0,\dots,\ell_{k-1}\). The edges are:

- \(h_ih_j\) for \(i<j<4\): the hubs \(h_0,\dots,h_3\) form a \(K_4\);
- \(h_0h_j\) for \(4\le j<k\): the \(t\) pendant hubs hang at \(h_0\);
- \(h_im_i\) and \(m_i\ell_i\) for every \(i\): each hub carries a path of length 2.

So \(G_t\) is the 2-corona of \(K_4\) with \(t\) pendant vertices at one vertex. It has
\(n=3k\) vertices and is connected. In Lean, `family t` puts \(h_i\), \(m_i\), \(\ell_i\) at
`(0, i)`, `(1, i)`, `(2, i)`, and \(G_1\) with the label \(5l+i\) for `(l, i)` is the
15-vertex graph of the README.

**Cliques.** The only \(K_4\) of \(G_t\) is \(\{h_0,\dots,h_3\}\). A middle or a leaf lies in no
triangle (its neighbours are not adjacent), and neither does a pendant hub (its neighbours
\(h_0\) and its middle are not adjacent). So every clique with four vertices is the \(K_4\) of
hubs, and every triangle consists of three hubs \(h_i\) with \(i<4\).

**\(\gamma_t(G_t)=2k\).** The hubs and the middles form a total dominating set: a hub is
adjacent to its middle, and a middle or a leaf is adjacent to a middle or a hub of its own
path. Conversely let \(D\) be total dominating. The only neighbour of \(\ell_i\) is \(m_i\),
so \(m_i\in D\). The neighbours of \(m_i\) are \(h_i\) and \(\ell_i\), so one of them is in
\(D\). The sets \(\{h_i,m_i,\ell_i\}\) are disjoint, and each meets \(D\) in at least two
vertices, so \(|D|\ge2k\).

**\(\lambda_{\bar G}\) at every vertex.**

| Vertex \(v\) | \(N_G[v]\) | \(\omega(G-N_G[v])\) |
| --- | --- | ---: |
| \(h_i\), \(i<4\) | all four hubs of the \(K_4\), \(m_i\), and the pendant hubs if \(i=0\) | 2 |
| \(h_j\), \(j\ge4\) (pendant hub) | \(h_j\), \(h_0\), \(m_j\) | 3 |
| \(m_i\), \(i<4\) | \(m_i\), \(h_i\), \(\ell_i\) | 3 |
| \(m_j\), \(j\ge4\) | \(m_j\), \(h_j\), \(\ell_j\) | 4 |
| \(\ell_i\), any \(i\) | \(\ell_i\), \(m_i\) | 4 |

- At \(h_i\), \(i<4\): no hub of the \(K_4\) is left. Every remaining edge contains a middle
  (\(h_jm_j\) for a pendant hub, or \(m_j\ell_j\)), and two middles are never adjacent, so no
  triangle is left. An edge \(m_j\ell_j\) with \(j\ne i\) is left. So the value is 2.
- At a pendant hub \(h_j\): \(h_1,h_2,h_3\) are left and form a triangle; \(h_0\) is gone,
  so the \(K_4\) is not. The value is 3.
- At \(m_i\), \(i<4\): the three hubs of the \(K_4\) other than \(h_i\) are left; \(h_i\) is
  gone. The value is 3.
- At \(m_j\), \(j\ge4\), and at every leaf: the whole \(K_4\) is left. The value is 4.

So \(\lambda_{\min}(\bar G_t)=2\), attained exactly at \(h_0,\dots,h_3\): \(f(G_t)=4\).

**The gap.** \(2\gamma_t(G_t)=4k=3k+4+t=n+f+t\). So \(\gamma_t-\tfrac12(n+f)=t/2\): every
\(t\ge1\) violates the bound, and the violation is unbounded. \(t=0\) (12 vertices) gives
equality.

Lean proves this for every \(t\): \(\gamma_t=2k\) (`totalDominationNumber_family`),
\(\lambda_{\bar G}=2\) at the hubs of the \(K_4\) and \(\lambda_{\bar G}\ge3\) at every other vertex,
hence \(\lambda_{\min}=2\) with frequency 4 (`localIndependenceMin_compl_family`,
`localIndependenceMinFreq_compl_family`), the gap (`family_gap`) and the violation
(`family_violates`, and `family_violates_ceil` for the rounded-up bound when \(t\ge2\)). The
exact values 3 and 4 in the table are proved in Lean for \(t=1\) and checked by
`check_wowii300.py` for \(t\le4\).

**The 15-vertex graph \(G_1\).** Besides the general argument, the Lean file checks every
value of \(\lambda_{\bar G}\) on \(G_1\) from certificates: for each vertex \(v\), a clique of
\(G\) outside \(N_G[v]\) with \(\lambda(v)\) vertices (`wit15`), and a colouring of
\(G-N_G[v]\) with \(\lambda(v)\) colours that is proper for \(G\) (`col15`). A colouring with
\(c\) colours bounds every clique by \(c\). `decide +kernel` checks all of them
(`indepNeighborsCard_compl_counterexample`): 2 at the vertices 0–3, 3 at 4–8, 4 at 9–14.

## The 12-vertex graph \(H\)

\(H\) has the vertices \(0,\dots,11\) and the 13 edges

```text
4-5 1-6 2-7 6-8 7-9 8-9 3-10 4-10 5-10 0-11 3-11 8-11 9-11
```

(graph6 `K??I@?A?WwQE`): the triangles \(T_1=\{8,9,11\}\) and \(T_2=\{4,5,10\}\), the path
\(11-3-10\) between them, the leaf 0 at 11, and the paths \(8-6-1\) and \(9-7-2\). It is
connected, and its leaves are 0, 1 and 2.

**\(\gamma_t(H)=7\).** \(\{4,6,7,8,9,10,11\}\) is total dominating: 0, 3, 8 and 9 are
adjacent to 11 or 8; 1 to 6; 2 to 7; 4, 5 and 3 to 10; 6 to 8; 7 to 9; 10 and 5 to 4; 11 to
8. Conversely let \(D\) be total dominating.

1. The leaves 0, 1 and 2 have the single neighbours 11, 6 and 7, so \(11,6,7\in D\).
2. The neighbours of 6 are 1 and 8, so one of them is in \(D\).
3. The neighbours of 7 are 2 and 9, so one of them is in \(D\).
4. The neighbours of 5 are 4 and 10, so some \(w\in\{4,10\}\) is in \(D\), and \(w\) has a
   neighbour \(w'\in D\). The neighbours of 4 are 5 and 10, and those of 10 are 3, 4 and 5,
   so \(\{w,w'\}\) is a 2-subset of \(\{3,4,5,10\}\).

The sets \(\{11\}\), \(\{6\}\), \(\{7\}\), \(\{1,8\}\), \(\{2,9\}\) and \(\{3,4,5,10\}\) are
disjoint, so \(|D|\ge1+1+1+1+1+2=7\).

**\(\lambda_{\bar G}\).** \(H\) has exactly two triangles, \(T_1\) and \(T_2\), and no
\(K_4\), so \(\lambda_{\bar G}\le3\) everywhere.

- \(N_H[3]=\{3,10,11\}\) meets both triangles. What remains is the path
  \(1-6-8-9-7-2\), the edge \(4-5\) and the isolated vertex 0: a forest with an edge. So
  \(\lambda_{\bar G}(3)=2\).
- The closed neighbourhoods that meet \(T_1\) are those of 0, 3, 6, 7, 8, 9 and 11; those
  that meet \(T_2\) are those of 3, 4, 5 and 10. Only vertex 3 is in both lists, so every
  \(v\ne3\) leaves a whole triangle: \(\lambda_{\bar G}(v)=3\).

So \(\lambda_{\min}(\bar G)=2\) with frequency 1, and \(\gamma_t(H)=7>\tfrac12(12+1)\). The
Lean file proves exactly this (`totalDominationNumber_graph12`,
`indepNeighborsCard_compl_graph12`, `graph12_violates`, `not_statement_graph12`). Its
certificates are the edge \(\{8,9\}\) or a triangle outside \(N_H[v]\), the 2-colouring of
\(H-N_H[3]\) given by the bipartition of the forest, and a single proper 3-colouring of \(H\)
for all other vertices.

## Rounding

- \(G_1\) (15 vertices) violates the real bound by 1/2: \(10>9.5\). Rounded down, the bound
  is 9 and still fails; rounded up, it is 10 and holds.
- \(G_2\) (18 vertices) has \(\gamma_t=12\) and \(f=4\), so the bound is \(11\), an integer.
  The violation is 1, and it survives any rounding. `family_violates_ceil` proves
  \(\lceil\tfrac12(n+f)\rceil<\gamma_t\) for every \(t\ge2\).
- All ten counterexamples on 12 vertices violate the bound by exactly 1/2, so the bound
  rounded up holds on 12 vertices. Six of the ten counterexamples on 13 vertices have
  \(\gamma_t=8\) and \(f=1\): bound 7, violation 1. So the smallest counterexamples to the
  rounded-up bound have 13 vertices (computation, not Lean).

## Without the complement

If \(\lambda\) is computed in \(G\) instead of \(\bar G\), then in \(G_t\) every leaf has
\(\lambda=1\) (one neighbour), every middle has \(\lambda=2\) (its two neighbours are not
adjacent), and every hub has \(\lambda\ge2\) (a hub of the \(K_4\) has its middle and one other
hub of the \(K_4\) as non-adjacent neighbours; a pendant hub has \(h_0\) and its middle). So
\(\lambda_{\min}(G_t)=1\) with frequency \(k\), and the bound is \(\tfrac12(3k+k)=2k=\gamma_t\):
equality for every \(t\). `check_wowii300.py` checks this for \(t\le4\). In \(H\), the
vertices with \(\lambda=1\) are the leaves 0, 1, 2 and the vertices 4 and 5 (each has two
adjacent neighbours), so this reading gives the bound \(\tfrac12(12+5)=8.5\ge7\). We did not
search under this reading and claim nothing about it.

## Computation

The computation is supporting evidence, not part of the Lean proof. Three programs are in this
directory.

- [`check_wowii300.py`](check_wowii300.py) (Python standard library) finds \(\gamma_t\) by
  searching vertex subsets in order of size. It computes \(\lambda_{\bar G}\) twice and
  requires agreement: as the largest independent set of \(\bar G\) inside
  \(N_{\bar G}(v)\), by enumerating independent sets, and as the largest clique of
  \(G-N_G[v]\), by enumerating cliques. `--graph6` checks graph6 input.
- [`sweep_wowii300.c`](sweep_wowii300.c) does the same with 64-bit vertex masks:
  \(\gamma_t\) by trying the \(k\)-subsets in order of \(k\) (Gosper's hack), and
  \(\lambda_{\bar G}(v)=\omega(G-N_G[v])\) by a branching clique search. It prints the same
  summary lines as `check_wowii300.py --graph6`; `-p` also prints a `NEAR` line for every
  graph with \(2\gamma_t\ge n\).
- [`closure_wowii300.sh`](closure_wowii300.sh) lists the connected graphs with
  \(\gamma_t\ge k\) on \(n\) vertices (see below).

Both checkers compute \(\lambda_{\bar G}\) only when \(2\gamma_t\ge n\). This covers every
possible violation (\(2\gamma_t\ge n+2\)) and every equality (\(2\gamma_t=n+f\ge n+1\)).
The slack is \(n+f-2\gamma_t\); a violation is a negative slack.

### All connected graphs on 3 to 11 vertices

`geng -c` (nauty 2.9.3) lists the connected graphs. The C program checked all of them; the
Python program checked \(n\le10\) and printed output identical to the C program's.

| \(n\) | Graphs | \(\gamma_t\) histogram | \(2\gamma_t\ge n\) | Slack histogram |
| ---: | ---: | --- | ---: | --- |
| 3 | 2 | {2: 2} | 2 | {0: 1, 2: 1} |
| 4 | 6 | {2: 6} | 6 | {1: 2, 2: 2, 4: 2} |
| 5 | 21 | {2: 19, 3: 2} | 2 | {0: 1, 4: 1} |
| 6 | 112 | {2: 96, 3: 14, 4: 2} | 16 | {1: 5, 2: 3, 3: 1, 4: 4, 5: 1, 6: 2} |
| 7 | 853 | {2: 670, 3: 163, 4: 20} | 20 | {0: 2, 3: 4, 4: 3, 5: 2, 6: 9} |
| 8 | 11,117 | {2: 8191, 3: 2583, 4: 340, 5: 3} | 343 | {1: 31, 2: 14, 3: 7, 4: 48, 5: 84, 6: 59, 7: 19, 8: 81} |
| 9 | 261,080 | {2: 183149, 3: 70667, 4: 7151, 5: 111, 6: 2} | 113 | {0: 4, 1: 1, 2: 1, 3: 11, 4: 19, 5: 21, 6: 16, 8: 40} |
| 10 | 11,716,571 | {2: 7888271, 3: 3566498, 4: 257828, 5: 3898, 6: 76} | 3,974 | {0: 1, 1: 189, 2: 83, 3: 145, 4: 366, 5: 802, 6: 1002, 7: 551, 8: 266, 10: 569} |
| 11 | 1,006,700,565 | {2: 649682614, 3: 339921423, 4: 16900235, 5: 193187, 6: 3095, 7: 11} | 3,106 | {0: 74, 1: 43, 2: 85, 3: 278, 4: 583, 5: 716, 6: 494, 7: 234, 8: 5, 10: 594} |

No slack is negative: **no connected graph on at most 11 vertices violates the bound.** The
\(n=10\) equality is ``I?`CR?ogO`` (\(\gamma_t=6\), \(f=2\)). At \(n=11\) the eleven graphs
with \(\gamma_t=7\), the only ones that could violate the bound, have slack 1 (one graph, with
\(f=4\)), 3 (two), 4 (three) and 8 (five); the Python program recomputed all eleven.

### Connected graphs with large \(\gamma_t\) on 12 to 14 vertices

Listing all connected graphs on 12 vertices with `geng` is out of reach here (there are about
\(1.6\times10^{11}\)), but a violation needs \(\gamma_t\ge\lceil n/2\rceil+1\): 7 for \(n=12\), 8 for \(n=13\) and
\(n=14\). `closure_wowii300.sh n k` lists every connected graph on \(n\) vertices with
\(\gamma_t\ge k\).

**Why the list is complete.** If \(H'\) is a spanning subgraph of \(G\) without isolated
vertices, every total dominating set of \(H'\) is one of \(G\), so
\(\gamma_t(H')\ge\gamma_t(G)\). Let \(G\) be connected with \(\gamma_t(G)\ge k\), let \(T\)
be a spanning tree of \(G\), and add the edges of \(G-T\) to \(T\) one at a time. Every graph
on the way is a spanning subgraph of \(G\) that contains \(T\), so it has
\(\gamma_t\ge k\). The script starts from all trees on \(n\) vertices (`gentreeg`) with
\(\gamma_t\ge k\). At each step it adds one edge to every graph of the current list in every
possible way (`addedgeg`), puts the results in canonical form (`labelg`), removes duplicates
(`sort -u`), and keeps those with \(\gamma_t\ge k\). It stops when the list is empty. Every
graph on the way from \(T\) to \(G\) is reached, \(G\) included, up to isomorphism.

The \(\gamma_t\) filter reads the `NEAR` lines of `sweep_wowii300 -p`, which cover every
graph with \(2\gamma_t\ge n\); this is why the script requires \(2k\ge n\).

| \(n\) | \(k\) | Graphs with \(\gamma_t\ge k\) | \(\gamma_t\) histogram | Slack histogram | Violations |
| ---: | ---: | ---: | --- | --- | ---: |
| 12 | 7 | 889 | {7: 883, 8: 6} | {-1: 10, 0: 10, 1: 12, 2: 60, 3: 122, 4: 208, 5: 169, 6: 97, 8: 3, 10: 198} | 10 |
| 13 | 8 | 406 | {8: 406} | {-2: 6, -1: 4, 0: 5, 1: 28, 2: 50, 3: 85, 4: 79, 5: 48, 10: 101} | 10 |
| 14 | 8 | 39,316 | {8: 39258, 9: 58} | {-1: 989, 0: 663, 1: 1283, 2: 3183, 3: 6380, 4: 9140, 5: 7813, 6: 3953, 7: 1632, 8: 1, 10: 16, 12: 4263} | 989 |

The summary lines are in [`closure_summary.txt`](closure_summary.txt). The C and the Python
program print them identically. On 13 vertices the slack histogram covers only
\(\gamma_t\ge8\); graphs with \(\gamma_t=7\) and \(f=1\), which would have slack 0, were not
listed.

### Cross-checks

- The numbers of connected graphs for \(n\le11\) match OEIS A001349, and the numbers of
  trees on 12, 13 and 14 vertices (551, 1,301, 3,159) match OEIS A000055.
- Copies of the two checkers that also accept disconnected graphs reproduce the triangle
  OEIS A332400 (graphs by total domination number) for \(n\le10\) (C) and \(n\le9\)
  (Python). Its column \(\gamma_t=2\) is OEIS A332406.
- The C and the Python program print identical output on all connected graphs with
  \(n\le10\), and identical summary lines on the closure lists for \(n=12,13,14\). For
  \(n=14\) the sets of violating graphs were also compared and are equal.
- The closure script reproduces the exhaustive lists, compared as sets of canonical graph6
  strings: \(\gamma_t\ge5\) on 8 vertices (3 graphs) and on 9 vertices (113),
  \(\gamma_t\ge6\) on 10 vertices (76), \(\gamma_t\ge6\) on 11 vertices (3,106) and
  \(\gamma_t\ge7\) on 11 vertices (11).
- The connected graphs with \(\gamma_t=2n/3\) on 3, 6, 9 and 12 vertices (2, 2, 2 and 6
  graphs) are exactly \(C_3\), \(C_6\) and the 2-coronas of the connected graphs on 1 to 4
  vertices, compared as sets of canonical graph6 strings (see
  [Literature context](#literature-context)).

## The smallest counterexamples

**12 vertices.** Exactly ten graphs, all with \(\gamma_t=7\), \(\lambda_{\min}(\bar G)=2\)
and \(f=1\) (violation 1/2). In canonical graph6 (nauty 2.9.3), with the number of edges:

| graph6 | Edges | Vertex with \(\lambda_{\bar G}=2\) |
| --- | ---: | ---: |
| `K??I@?A?WwQE` (\(H\)) | 13 | 3 |
| `K?G?K?@OGkBE` | 13 | 3 |
| `K?Ca??CEOFOL` | 14 | 7 |
| `K?D@?o@_?H_V` | 14 | 8 |
| `K?O_?ODC_co[` | 14 | 6 |
| `KA?_GAAAOQa[` | 14 | 7 |
| `K?EA?o@GGH_V` | 15 | 8 |
| `KAG?OGD__BaR` | 15 | 10 |
| ``KAGC?GD?Wc`R`` | 15 | 9 |
| `KAG?GM?CGP_^` | 16 | 11 |

Each has exactly three leaves.

**13 vertices.** Ten graphs. Six have \(\gamma_t=8\) and \(f=1\) and violate the bound by 1:
`L?_?I?_?O@aoEE`, `L?EA@??@?p?U?\`, `LC@@??C?gQ@HC[`, `L?EA@?W?GG_R?V`,
``L?`@?_PA?G_R?Z``, ``L?`@?_PA?G_R?^``. Four have \(\gamma_t=8\) and \(f=2\) and violate it
by 1/2: `L?O?HAO??A_qEE`, `L?O@?_C?_AocAM`, `L?c?I?_@_A?DCF`, `L?EA@?A?Oo?F@L`.

**14 vertices.** 989 graphs, all with \(\gamma_t=8\) and \(f=1\).

`python3 check_wowii300.py` re-checks the ten graphs on 12 vertices and the six on 13
vertices from scratch.

## Literature context

The following results appear in our sources only as quoted in Table 1 of M. A. Henning and
A. Yeo, *A new upper bound on the total domination number of a graph*, Electron. J. Combin.
14 (2007) #R65, and the discussion after it; we did not read the original papers. None of
them is used in the Lean proof or in the computation.

- Cockayne, Dawes and Hedetniemi, Networks 10 (1980) 211–219: \(\gamma_t\le2n/3\) for every
  connected graph with \(n\ge3\).
- Brigham, Carrington and Vitray, J. Combin. Math. Combin. Comput. 34 (2000) 81–96,
  characterize the graphs that attain this bound; Henning–Yeo do not restate the
  characterization. On 3, 6, 9 and 12 vertices, the connected graphs with \(\gamma_t=2n/3\)
  that our programs find are exactly \(C_3\), \(C_6\) and the 2-coronas of the connected graphs
  on 1 to 4 vertices.
- Henning, *Graphs with large total domination number*, J. Graph Theory 35 (2000) 21–45:
  Table 1 states \(\gamma_t\le4n/7\) for connected graphs with minimum degree at least 2,
  except \(C_3\), \(C_5\), \(C_6\) and \(C_{10}\). On 10 vertices our programs find two further
  connected graphs with minimum degree 2 and \(\gamma_t=6>40/7\): `IK_PA?H@g` (two vertices
  of degree 3 joined by an edge and by two paths of length 5) and `ISP@?SECW` (a 4-cycle whose
  two pairs of opposite vertices are joined by paths of length 4). Both satisfy the main
  theorem of Henning–Yeo. The original theorem may carry hypotheses that the table omits; we
  have not checked, and we did not use this bound.

## Blind spot and prior refutation

- **Prior refutation.** The audit `results/transcription_audit.md` of Kuberwastaken/c5-k4
  (commit `2448b85`, 2026-08-12) compares a July 2026 parse of the page with a live fetch of
  2026-08-12 (`menu.htm`: "last update 8/6/26"). It lists 300 as changed to `F`, with the note
  dated July 26, 2026: William Weishuhn (CU Boulder), a family with arbitrarily large
  violation, with Codex-assisted verification. We have not seen that note on the page or the
  family, so we cannot compare it with \(G_t\).
- **Blind spot.** The last Wayback capture of `all.html` is from 2026-07-26 (06:15 UTC), and
  row 300 is still `O` there. When we checked on 2026-10-25, the live site redirected to an
  HTTPS host that timed out. Notes added after the last capture, including Weishuhn's, can
  only be seen through the c5-k4 audit. Other resolutions could exist that we could not see.

## What is and is not proved

- **Lean** (only the three standard axioms): the statement as formalized is false
  (`not_statement`, `not_statement_graph12`); \(G_t\) violates it by \(t/2\) for every
  \(t\ge1\), and its rounded-up form for \(t\ge2\); \(H\) violates it.
- **Computation only:**
  - that no connected graph on at most 11 vertices violates the bound;
  - the lists on 12 to 14 vertices, the counts 10, 10, 989, and so the minimum order 12;
  - the minimum order 13 for the rounded-up bound.
- **Reading choices** (the bar, "frequency" as a count, no rounding) are ours, argued
  above. The Lean statement fixes them; a different reading is a different statement.
- **Review.** No human has reviewed this work.
