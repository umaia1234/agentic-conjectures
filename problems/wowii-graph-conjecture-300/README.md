**English** | [한국어](README.ko.md)

# WOWII Graph Conjecture 300

Conjecture 300 of E. DeLaViña's *Written on the Wall II* (WOWII), the list of
conjectures of the program Graffiti.pc, is dated March 1, 2007. It bounds the
total domination number of a connected graph by half of its order plus the
number of vertices at which the local independence of the complement is
smallest. **That the conjecture is false is not new.** A transcription audit
in the repository Kuberwastaken/c5-k4 (2026-08-12) reports that the WOWII page
now marks it false. The audit cites the page's note of July 26, 2026: William
Weishuhn (CU Boulder) found a family of graphs with arbitrarily large violation,
with Codex-assisted verification. We could not read that note or see that
family. An earlier scouting run of this project found the 15-vertex
counterexample below without knowing of the note. This directory adds a Lean
refutation, a Lean proof that an infinite family violates the bound by
\(t/2\) for every \(t\ge1\), and a Lean proof for a counterexample on 12
vertices, which an exhaustive computation shows to be the smallest order; we
found no earlier formal proof. Our searches of 2026-10-25 (UTC)
covered Formal Conjectures, GitHub, MathDB, Zenodo, OpenAlex, arXiv, the
trackers AFTD, trureturing and c5-k4, and the Wayback Machine. The c5-k4 audit
is the only source we found that reports a resolution. There is a blind spot:
the page itself is unreachable (checked 2026-10-25), and its last archived
copy is from July 26. No novelty is claimed. No human has reviewed this
work, and nothing has been submitted anywhere, including the page owner,
Formal Conjectures and MathDB. Details are under
[Prior art and status](#prior-art-and-status).

## The conjecture

Row 300 sits in the section "Upper bounds for Total Domination" of the list.
It has status `O` (open) in every Wayback capture of the list that we read,
up to the last one, of 2026-07-26. It reads:

> If G is a simple connected graph such that n(G)> 2, then γ<sub>t</sub>(G) ≤ (1/2)*[n(G) + frequency of λ<sub>min</sub>(Ḡ)]

This is the text of the
[2026-07-26 capture](https://web.archive.org/web/20260726061534/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/all.html).
The source URL of the list is
<http://cms.dt.uh.edu/faculty/delavinae/research/wowII/>, unreachable when
checked on 2026-10-25.
The HTML writes γ as the letter `g` in the Symbol font. It draws the bar over
the last G with the CSS style `text-decoration: overline`. The row links
entries 94, 3, 4 and 31 of the list's definitions file `wowIIdefs.js`
([2026-07-23 capture](https://web.archive.org/web/20260723161838/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/wowIIdefs.js)).
Paraphrased, they say the following.

- **Total domination number** \(\gamma_t(G)\): the size of a smallest set
  \(D\) of vertices such that every vertex is adjacent to a vertex of \(D\).
- **Order** \(n(G)\): the number of vertices.
- **Local independence** \(\lambda(v)\): the independence number of the
  subgraph induced by the neighbours of \(v\). \(\lambda_{\min}\) is the
  smallest local independence over all vertices.
- **Complement** \(\bar G\): the graph on the same vertices in which two
  vertices are adjacent exactly when they are not adjacent in \(G\).

### Reading

- **Frequency.** The list has no separate definition of "frequency of". Where
  it defines a frequency (entries 18 and 62, the frequencies of degree one and
  of degree \(k\)), it means the number of vertices that attain the value. So
  the frequency of \(\lambda_{\min}(\bar G)\) is
  \[
  f(G)=\bigl|\{v:\lambda_{\bar G}(v)=\min_u\lambda_{\bar G}(u)\}\bigr|,
  \]
  where \(\lambda_{\bar G}(v)\) is the local independence of \(v\) computed in
  \(\bar G\).
- **The complement.** The bar is in the HTML of every capture, and definition
  31 is linked. The sibling Conjecture 301, of the same date and marked true,
  has the same form with "frequency of λ<sub>max</sub>(Ḡ)". DeLaViña, Liu,
  Pepper, Waller and West prove it as Theorem 10 of *Some conjectures of
  Graffiti.pc on total domination* (Congr. Numer. 185 (2007) 81–95), with
  \(A=\{v:\text{the local independence of }v\text{ in }\bar G\text{ is maximum}\}\)
  in place of the frequency: \(\gamma_t\le\omega+|A|\). We read 300 in the same
  way.
- **No rounding.** The row writes no CEIL or FLOOR (the list writes them out
  when it uses them), so the bound is a real number.

So the conjecture says: every connected graph \(G\) with \(n(G)\ge3\)
satisfies
\[
\gamma_t(G)\ \le\ \tfrac12\bigl(n(G)+f(G)\bigr).
\]
An independent set of \(\bar G\) is a clique of \(G\), and the neighbours of
\(v\) in \(\bar G\) are the vertices outside the closed neighbourhood
\(N_G[v]\). Hence \(\lambda_{\bar G}(v)=\omega(G-N_G[v])\), the clique number of
what remains of \(G\) after deleting \(v\) and its neighbours.

## Result

**Theorem (Lean).** The conjecture is false. The graph \(G_1\) below has 15
vertices, \(\gamma_t(G_1)=10\) and \(f(G_1)=4\), and
\(10>\tfrac12(15+4)=9.5\).

\(G_1\) is built from \(K_4\) on the vertices 0, 1, 2, 3 and a pendant vertex
4 at vertex 0. Each of these five *hubs* \(h\) then gets a path
\(h-(h+5)-(h+10)\), with *middle* vertex \(h+5\) and *leaf* \(h+10\). So
\(G_1\) is the 2-corona of \(K_4\) plus a pendant vertex. It has 17 edges:

```text
0-1 0-2 0-3 0-4 0-5 1-2 1-3 1-6 2-3 2-7 3-8 4-9 5-10 6-11 7-12 8-13 9-14
```

Its graph6 string is `N~aA@?OA?G?O?O?G?A?`. The local independence in the
complement takes these values:

| Vertices | 0–3 (hubs of the \(K_4\)) | 4 (pendant hub) | 5–8 (their middles) | 9 (middle at 4) | 10–14 (leaves) |
| --- | ---: | ---: | ---: | ---: | ---: |
| \(\lambda_{\bar G}(v)=\omega(G-N_G[v])\) | 2 | 3 | 3 | 4 | 4 |

So \(\lambda_{\min}(\bar G)=2\), attained at four vertices, and the bound is
\(\tfrac12(15+4)=9.5<10\).

**The family.** For \(t\ge0\) let \(G_t\) be the 2-corona of \(K_4\) with
\(t\) pendant vertices at one vertex of the \(K_4\). It has \(n=3(t+4)\)
vertices, \(\gamma_t(G_t)=2(t+4)\) and \(f(G_t)=4\), so
\[
2\gamma_t(G_t)=n(G_t)+f(G_t)+t .
\]
Every \(t\ge1\) is a counterexample, and the violation \(t/2\) is unbounded.
From \(t=2\) on the violation is at least 1, so the bound fails even when it is
rounded up: \(G_2\) has 18 vertices, \(\gamma_t=12\) and
\(\lceil(18+4)/2\rceil=11\). The case \(t=0\) (12 vertices, \(\gamma_t=8\)) is
an equality. Lean proves all of this for every \(t\).

Without the bar, with \(\lambda\) computed in \(G\) itself, the leaves are the
vertices of smallest local independence (\(\lambda=1\)), there are \(t+4\) of
them, and every \(G_t\) attains equality. We claim nothing about that reading.

**Theorem (Lean).** The graph \(H\) below has 12 vertices,
\(\gamma_t(H)=7\) and \(f(H)=1\), and \(7>\tfrac12(12+1)=6.5\). It consists of
the triangles \(\{8,9,11\}\) and \(\{4,5,10\}\), the path \(11-3-10\) between
them, the leaf 0 at vertex 11, and the paths \(8-6-1\) and \(9-7-2\). It has
13 edges:

```text
4-5 1-6 2-7 6-8 7-9 8-9 3-10 4-10 5-10 0-11 3-11 8-11 9-11
```

Its graph6 string is `K??I@?A?WwQE`. Vertex 3 is the only vertex whose
closed neighbourhood \(\{3,10,11\}\) meets both triangles, so
\(\lambda_{\bar G}(3)=2\), while \(\lambda_{\bar G}(v)=3\) at the other eleven
vertices.

**Smallest counterexamples (computation).** No connected graph on at most 11
vertices violates the bound, so 12 is the smallest order of a counterexample.
On 12 vertices there are exactly ten counterexamples up to isomorphism,
\(H\) among them. All ten have \(\gamma_t=7\) and \(f=1\), so they violate the
bound by 1/2. On 13 vertices there are ten. Six of them have \(\gamma_t=8\) and
\(f=1\), so they violate the bound by 1 and are the smallest counterexamples
to the bound rounded up. On 14 vertices there are 989. This part is
computation, not Lean; see [Numerical cross-check](#numerical-cross-check).

## Proof idea

1. **\(\gamma_t(G_t)=2(t+4)\).** The only neighbour of a leaf is its middle, so
   every total dominating set contains every middle. A middle needs a
   neighbour in the set too, and its neighbours are its hub and its leaf. So
   the set meets each of the \(t+4\) paths hub–middle–leaf in at least two
   vertices. The hubs and the middles form a total dominating set of that
   size.
2. **\(\lambda_{\bar G}=2\) at the four hubs of the \(K_4\).** \(N_G[h]\)
   contains all four hubs of the \(K_4\), and all pendant hubs when \(h\) is
   the vertex that carries them. So no two hubs outside \(N_G[h]\) are
   adjacent, and every edge of \(G-N_G[h]\) contains a middle. Two middles are
   never adjacent, so a clique has at most two vertices. A middle and its leaf
   outside \(N_G[h]\) form a clique of two.
3. **\(\lambda_{\bar G}\ge3\) at every other vertex.** \(N_G[v]\) contains at
   most one hub of the \(K_4\), so at least three of them, pairwise adjacent,
   lie in \(G-N_G[v]\).

Hence \(\lambda_{\min}(\bar G_t)=2\) with frequency exactly 4.

For the 12-vertex graph \(H\): a total dominating set contains 11, 6 and 7,
the only neighbours of the leaves 0, 1 and 2. It also contains a neighbour of
6 (1 or 8), a neighbour of 7 (2 or 9), a neighbour \(w\) of 5 (4 or 10) and a
neighbour of \(w\), which lies in \(\{3,4,5,10\}\). These seven vertices are
distinct, and \(\{4,6,7,8,9,10,11\}\) is total dominating, so
\(\gamma_t(H)=7\). \(H\) has no \(K_4\), so \(\lambda_{\bar G}\le3\)
everywhere. A triangle outside \(N_H[v]\) gives \(\lambda_{\bar G}(v)=3\) for
\(v\ne3\). \(H-N_H[3]\) is a forest with an edge, so \(\lambda_{\bar G}(3)=2\).

[DETAILS.md](DETAILS.md) writes out every step and the exact values of
\(\lambda_{\bar G}\).

## Lean formal proof

[`AgenticConjectures/WowiiGraphConjecture300.lean`](../../AgenticConjectures/WowiiGraphConjecture300.lean)
compiles in about 7 s once mathlib is built. It uses no `sorry`, no extra
axioms and no `native_decide`; the finite checks on the 15- and 12-vertex
graphs run `decide +kernel`. `#print axioms` lists only `propext`,
`Classical.choice` and `Quot.sound` for every registered theorem.

| Declaration | Content |
| --- | --- |
| `statement`, `not_statement` | The conjecture as a `Prop`, and its negation from the 15-vertex graph. |
| `not_statement_graph12`, `graph12_violates` | The negation again from the 12-vertex graph \(H\), and the strict inequality \(\tfrac12(12+1)<7\) for \(H\). |
| `graph12`, `graph12_connected`, `card_graph12`, `totalDominationNumber_graph12` | \(H\) on `Fin 12` with the edge list `edges12` above, connected, \(n=12\), \(\gamma_t=7\). |
| `indepNeighborsCard_compl_graph12`, `localIndependenceMin_compl_graph12`, `localIndependenceMinFreq_compl_graph12` | Every value of \(\lambda_{\bar G}\) on \(H\) (2 at vertex 3, 3 elsewhere), so \(\lambda_{\min}(\bar G)=2\) with frequency 1. |
| `family`, `family_connected`, `card_family` | \(G_t\) on `Fin 3 × Fin (t + 4)`, connected, with \(3(t+4)\) vertices. |
| `totalDominationNumber_family` | \(\gamma_t(G_t)=2(t+4)\). |
| `indepNeighborsCard_compl_family_hub`, `three_le_indepNeighborsCard_compl_family` | \(\lambda_{\bar G}=2\) at the hubs of the \(K_4\), and \(\ge3\) elsewhere. |
| `localIndependenceMin_compl_family`, `localIndependenceMinFreq_compl_family` | \(\lambda_{\min}(\bar G_t)=2\), with frequency 4. |
| `family_gap`, `family_violates`, `family_violates_ceil` | \(2\gamma_t=n+f+t\); the bound fails for \(t\ge1\), and its ceiling fails for \(t\ge2\). |
| `counterexample_adj_iff` | `family 1` is the 15-vertex graph above, with the vertex `(l, i)` labelled \(5l+i\). |
| `counterexample_connected`, `card_counterexample`, `totalDominationNumber_counterexample`, `localIndependenceMin_compl_counterexample`, `localIndependenceMinFreq_compl_counterexample` | Connected, \(n=15\), \(\gamma_t=10\), \(\lambda_{\min}(\bar G)=2\) with frequency 4. |
| `indepNeighborsCard_compl_counterexample` | Every value of \(\lambda_{\bar G}\) on the 15-vertex graph, from clique and colouring certificates checked by `decide +kernel`, independently of the general lemmas. |
| `card_le_indepNeighborsCard`, `indepNeighborsCard_le` | Lower and upper bounds on local independence from an independent set and from a colouring. |

## Statement faithfulness

Formal Conjectures has no statement of Conjecture 300, so `statement` is ours.
It mirrors Formal Conjectures (google-deepmind/formal-conjectures, commit
`49ba26b`, Apache-2.0) so that it could be ported there:

```lean
def statement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 2 < Fintype.card V →
    (totalDominationNumber G : ℝ) ≤
      (1 / 2) * ((Fintype.card V : ℝ) + (localIndependenceMinFreq Gᶜ : ℝ))
```

- **Definitions.** `IsTotalDominating`, `IsTotalNDominatingSet` and
  `totalDominationNumber` are copied term for term from
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Domination.lean`
  (lines 75–91), `indepNeighborsCard` from `.../SimpleGraph/Independence.lean`
  (line 40), and `localIndependenceMin` from
  `FormalConjectures/WrittenOnTheWallII/GraphConjecture145.lean` (line 61).
  They differ in three ways, all listed in the module docstring. They live in
  the module's namespace. The field notation `G.IsTotalDominating D` is
  therefore written `IsTotalDominating G D`. And `localIndependenceMin`
  assumes `[Nonempty α]` instead of `[Nontrivial α]`; its body only needs a
  nonempty vertex set.
- **Match with the source definitions.** `totalDominationNumber G` is the
  infimum of the sizes of the vertex sets \(D\) in which every vertex has a
  neighbour. For a connected graph with at least two vertices such sets exist,
  so this is \(\gamma_t(G)\). `indepNeighborsCard G v` is the independence
  number of the subgraph induced by the neighbours of \(v\), which is
  \(\lambda(v)\). Applied to `Gᶜ` it is \(\lambda_{\bar G}(v)\).
  `localIndependenceMin Gᶜ` is its minimum over all vertices.
- **The frequency.** `localIndependenceMinFreq Gᶜ` is ours: the number of
  vertices \(v\) with `indepNeighborsCard Gᶜ v = localIndependenceMin Gᶜ`.
- **Statement.** The binders and hypotheses are those of
  `conjecture309Statement` in Formal Conjectures' `GraphConjecture309.lean`,
  another WOWII upper bound for \(\gamma_t\): every finite vertex type, every
  simple graph, `G.Connected`, and `2 < Fintype.card V` for \(n(G)>2\). The
  bound is compared in \(\mathbb R\), with no rounding and no natural-number
  subtraction. The binders `[DecidableEq V]` and `[DecidableRel G.Adj]` do not
  occur in the conclusion, so they exclude no graph. `V : Type` lives in
  universe 0, as in `conjecture309Statement`; the counterexamples' vertex
  types `Fin 3 × Fin 5` and `Fin 12` are in it.
- **Toolchain.** This repository builds with Lean and mathlib v4.30.0, while
  Formal Conjectures at `49ba26b` pins Lean v4.33.1. The copied definitions
  compile here unchanged; the refutation has not been compiled against
  v4.33.1.

## Numerical cross-check

The Lean proof is the certificate. Two independent programs back it up.

- [`check_wowii300.py`](check_wowii300.py) recomputes everything from the
  definitions with the Python standard library. It finds \(\gamma_t\) by
  searching vertex subsets in order of size, and \(\lambda_{\bar G}\) twice:
  as the largest independent set of \(\bar G\) inside each complement
  neighbourhood, and as the largest clique of \(G-N_G[v]\). By default it
  checks that the graph6 string is the graph above and that
  \(\gamma_t(G_1)=10\), checks \(G_t\) for \(t=0,\dots,4\) with both
  readings, and checks the ten counterexamples on 12 vertices (the first is
  \(H\)) and the six on 13 vertices that violate the bound by 1. That takes
  about 1 s.
- [`sweep_wowii300.c`](sweep_wowii300.c) is a bitmask C program for exhaustive
  sweeps. It takes graph6 input from `geng` and prints the same summary lines
  as `check_wowii300.py --graph6`.
- [`closure_wowii300.sh`](closure_wowii300.sh) lists every connected graph on
  \(n\) vertices with \(\gamma_t\ge k\), for orders where `geng` cannot list all
  graphs. Every total dominating set of a spanning subgraph without isolated
  vertices is one of the whole graph, so deleting edges never lowers
  \(\gamma_t\). Hence a connected graph with \(\gamma_t\ge k\) arises from one
  of its spanning trees, which has \(\gamma_t\ge k\), by adding edges one at a
  time through graphs with \(\gamma_t\ge k\). The script starts from the trees
  (`gentreeg`) and adds one edge in every way (`addedgeg`), keeping the graphs
  with \(\gamma_t\ge k\) and removing isomorphic copies (`labelg`), until
  nothing is left.

Both programs skip the local independence when \(2\gamma_t<n\), because
\(f\ge1\) means a violation needs \(2\gamma_t\ge n+2\), that is
\(\gamma_t\ge\lceil n/2\rceil+1\). Up to 11 vertices every connected graph was
checked; on 12 to 14 vertices every connected graph with
\(\gamma_t\ge\lceil n/2\rceil+1\) was:

| Order \(n\) | Graphs checked | \(2\gamma_t\ge n+2\) | Equality \(2\gamma_t=n+f\) | Violations |
| ---: | ---: | ---: | ---: | ---: |
| 3–9 | 273,191 (all connected) | 7 | 8 | 0 |
| 10 | 11,716,571 (all connected) | 76 | 1 | 0 |
| 11 | 1,006,700,565 (all connected) | 11 | 74 | 0 |
| 12 | 889 (\(\gamma_t\ge7\)) | 889 | 10 | 10 |
| 13 | 406 (\(\gamma_t\ge8\)) | 406 | 5 | 10 |
| 14 | 39,316 (\(\gamma_t\ge8\)) | 39,316 | 663 | 989 |

On 12 to 14 vertices the equality column counts only the graphs checked: on
13 vertices, graphs with \(\gamma_t=7\) and \(f=1\) would also attain equality,
and they were not listed.

**So the smallest counterexamples have 12 vertices.** The graph counts up to
\(n=11\) match OEIS A001349. On \(n\le10\) the two programs print identical
output. Their distributions of \(\gamma_t\) match the triangle OEIS A332400
(graphs by total domination number) for \(n\le10\) and \(n\le9\)
respectively; that comparison used copies that also accept disconnected
graphs. At \(n=11\) only the C program ran, in 20 parts taking 292 s in all
(76 s of wall time, four parts at a time). The Python program re-checked the
11 graphs with \(\gamma_t=7\); the closest has \(f=4\) and misses a violation
by 1/2. The closure script reproduces the exhaustive lists, compared as sets
of canonical graph6 strings: the 113 graphs with \(\gamma_t\ge5\) on 9
vertices, the 76 with \(\gamma_t\ge6\) on 10, and the 3,106 with
\(\gamma_t\ge6\) and the 11 with \(\gamma_t\ge7\) on 11. Its lists on 12 to 14
vertices give identical summary lines in the C and the Python program. The
number of trees, 551, 1,301 and 3,159, matches OEIS A000055.
[DETAILS.md](DETAILS.md) gives the full tables and the counterexamples.

## Prior art and status

- **WOWII.** Row 300 has status `O`, with the bar over G, in each capture
  of `all.html` that we read: 2010-07-17, 2016-10-09, 2026-07-23 (two) and
  2026-07-26. The
  [2026-07-26 capture](https://web.archive.org/web/20260726061534/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/all.html)
  is the last one. The live site now redirects to an HTTPS host that times
  out (checked 2026-10-25), so later notes cannot be read there.
- **Weishuhn (July 26, 2026).** Kuberwastaken/c5-k4 added the audit
  `results/transcription_audit.md` in commit `2448b85` (2026-08-12). It
  compares a parse from July 2026 with a live fetch of the page made on
  2026-08-12, whose `menu.htm` said "last update 8/6/26". Its table of
  status changes lists 300 as `F`, with the note: "July 26 2026 William
  Weishuhn (CU Boulder), family with arbitrarily large violation;
  Codex-assisted verification". The fetched page files are not in that
  repository, and its parsed data still lists 300 as open. We found nothing
  else on this result: no paper, preprint, repository or post. So we do not
  know Weishuhn's family or whether it resembles \(G_t\). **The refutation of
  Conjecture 300 is therefore not new.** What this directory adds is a Lean
  proof.
- **Other searches (2026-10-25, UTC).**
  - Formal Conjectures: the tree at `main` (`1353892`, 20:20 UTC) has no
    `GraphConjecture300.lean`. Issues and pull requests for "WOWII 300",
    `GraphConjecture300`, "Conjecture 300" and "WrittenOnTheWallII 300" found
    only an unrelated "Erdos 9" issue numbered 300.
  - The branches of RhudeJJJJ's fork of Formal Conjectures: nothing on 300.
  - GitHub code search for `GraphConjecture300`, "WOWII 300", `wowii_300`
    and `conjecture300`: nothing.
  - MathDB, Zenodo, OpenAlex and arXiv: nothing.
  - The trackers AFTD (`kb.json`) and trureturing: nothing.
  - Only the c5-k4 audit mentioned a resolution.
- **The 2007 paper.** It proves Conjecture 301, the sibling bound, as
  Theorem 10 (see [Reading](#reading)). It does not treat 300.

No human has reviewed the Lean refutation. Nothing has been submitted to the
WOWII maintainer, to Formal Conjectures, to MathDB or anywhere else; any
external submission needs human approval.

## Reproduction

From the repository root:

```bash
lake build AgenticConjectures.WowiiGraphConjecture300
python3 scripts/check_axioms.py
```

From this directory (the sweeps need nauty, version 2.9.3 here, and a C
compiler):

```bash
python3 check_wowii300.py
for n in 3 4 5 6 7 8 9; do geng -cq $n; done | python3 check_wowii300.py --graph6
geng -cq 10 | python3 check_wowii300.py --graph6
mkdir -p build && cc -O2 -o build/sweep_wowii300 sweep_wowii300.c
for n in 3 4 5 6 7 8 9 10; do geng -cq $n; done | build/sweep_wowii300
for r in $(seq 0 19); do geng -cq 11 $r/20 | build/sweep_wowii300 || echo "part $r FAILED"; done
sh closure_wowii300.sh 10 6 | sort > build/closure10.txt
geng -cq 10 | build/sweep_wowii300 -p | awk -F'[ =]' '$1 == "NEAR" && $6 >= 6 {print $2}' | labelg -qg | sort | diff - build/closure10.txt
for n in 12 13 14; do sh closure_wowii300.sh $n $(( (n + 1) / 2 + 1 )) | build/sweep_wowii300 | grep "^n=$n:"; done | diff - closure_summary.txt
for n in 12 13 14; do sh closure_wowii300.sh $n $(( (n + 1) / 2 + 1 )) | python3 check_wowii300.py --graph6 | grep "^n=$n:"; done | diff - closure_summary.txt
```

The sweeps of all graphs end with `OK`; the line for \(n=11\) is printed once
per part. The closure runs compare their summary lines with
[`closure_summary.txt`](closure_summary.txt). To list the counterexamples on
12 vertices, run `sh closure_wowii300.sh 12 7 | build/sweep_wowii300` and read
the `VIOLATION` lines.

Measured on an Apple-silicon machine, one part at a time: about 1 s for the
default check, 4 s for \(n\le9\) and 4 min for \(n=10\) in Python, 3 s for
\(n\le10\) in C, about 5 min for the 20 parts of \(n=11\) (the parts can run in
parallel), 3 s for the closure check on 10 vertices, and 25 s (C) or about
2 min (Python) for 12 to 14 vertices.

The definitions come from
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
(Apache-2.0). The graph lists come from nauty's `geng`, `gentreeg`,
`addedgeg` and `labelg`: B. D. McKay and A. Piperno, *Practical graph
isomorphism, II*, J. Symbolic Comput. 60 (2014) 94–112.
