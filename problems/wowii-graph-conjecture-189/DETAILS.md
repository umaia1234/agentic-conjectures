**English** | [한국어](DETAILS.ko.md)

# Mathematical details for WOWII Graph Conjecture 189

This file explains the transversal bound behind the σ ≤ 4 search, what the σ = 4 data shows
about extremal graphs, why σ = 5 is out of reach, and approaches that did not work. The Lean
module ([source](../../AgenticConjectures/WowiiGraphConjecture189.lean)) is the authoritative
proof of the bounds; this is a guide to it. Notation is as in the [README](README.md): (H) is the
hypothesis, and σ is the second-smallest degree.

## 1. The vertex partition

Fix a vertex x. Let D(v) be the set of vertices at even distance from v, so
|D(v)| = dist_even(v) ≤ σ + 1 under (H). Let O(x) be the set of vertices at odd distance at
least 3 from x. Every vertex is at even distance from x, adjacent to x, or in O(x), so

  n = dist_even(x) + deg(x) + |O(x)|.

Every bound on n below is a bound on |O(x)|. The bound in `card_le_distEven_add_degree` charges
each vertex of O(x) to a vertex of D(x) \ {x} that sees it at distance two, which gives
|O(x)| ≤ (dist_even(x) − 1)·σ ≤ σ² and n ≤ (σ + 1)².

## 2. The transversal bound

`exists_card_add_mul_self_le`: under (H), every vertex x has an s ≥ 0 with

  n + s² ≤ dist_even(x) + deg(x) + s·(σ + 1),

that is, |O(x)| ≤ s·(σ + 1 − s).

**Proof.** For z ∈ O(x) fix a neighbour q(z) with d(x, q(z)) = d(x, z) − 1. This distance is
even and at least 2. For a vertex p ≠ x let Dn(p) be the set of neighbours y of x with
d(y, p) = d(x, p) − 1, the neighbours of x on geodesics from x to p. It is never empty.

1. *If y ∈ Dn(q(z)), then y is at even distance from z.* Indeed
   d(y, z) ≤ d(y, q(z)) + 1 = d(x, z) − 1, and d(y, z) ≥ d(x, z) − 1 because y is adjacent to
   x. So d(y, z) = d(x, z) − 1, which is even.
2. Let Y ⊆ N(x) be a set of minimum size s that meets Dn(q(z)) for every z ∈ O(x). Such sets
   exist, since N(x) itself is one. By minimality each y ∈ Y has a *private* z_y ∈ O(x): y is
   the only element of Y in Dn(q(z_y)).
3. *Each y′ ∈ Y has |D(y′)| ≥ s + |D(y′) ∩ O(x)|.* Map every other y ∈ Y to a vertex f(y):
   - if y is not adjacent to y′, let f(y) = y. Both are neighbours of x, so d(y′, y) = 2;
   - if y is adjacent to y′, let f(y) = q(z_y). Then d(y′, q(z_y)) is at most
     d(y, q(z_y)) + 1 = d(x, q(z_y)) and at least d(x, q(z_y)) − 1. It is not
     d(x, q(z_y)) − 1, because y′ ∉ Dn(q(z_y)) by privacy. So it equals d(x, q(z_y)), which is
     even.

   Each f(y) is at even distance from y′ and outside O(x), since it is a neighbour of x or at
   even distance from x. f is injective: two values q(z_y) = q(z_{y″}) would put y″ in
   Dn(q(z_y)), against privacy, and a value y has distance 1 from x while a value q(z) has even
   distance. No value equals y′. So D(y′) contains y′, the s − 1 values of f, and
   D(y′) ∩ O(x), all distinct.
4. Under (H), |D(y′)| ≤ σ + 1, so |D(y′) ∩ O(x)| ≤ σ + 1 − s. By step 1 the sets D(y) ∩ O(x)
   for y ∈ Y cover O(x), so |O(x)| ≤ s·(σ + 1 − s). ∎

Since 4s(σ + 1 − s) ≤ (σ + 1)², `four_mul_card_le` gives 4n ≤ 4(σ + 1) + 4·deg(x) + (σ + 1)²
for every x. At a vertex of degree σ this is `four_mul_card_le_sq`:

  n ≤ 2σ + 1 + ⌊(σ + 1)² / 4⌋.

For σ ≤ 4 it gives n ≤ deg(x) + 11 at every vertex. `search_reduction_four` collects what the
search uses: if (H) holds and σ ≤ 4, then n ≤ 15, the minimum degree is at least n − 11, every
vertex has at most four vertices at distance two, and at least two vertices have degree at most
four.

| σ | old bound (σ + 1)² | new bound 2σ + 1 + ⌊(σ + 1)²/4⌋ | largest (H) graph |
| ---: | ---: | ---: | ---: |
| 1 | 4 | 4 | 4 |
| 2 | 9 | 7 | 7 |
| 3 | 16 | 11 | 10 |
| 4 | 25 | 15 | 13 |
| 5 | 36 | 20 | unknown, at least 11 |

The last column comes from the searches. The new bound is exact for σ = 1 and σ = 2 (the path
P₄ and the cycle C₇) and overshoots by one for σ = 3 and by two for σ = 4.

## 3. The σ ≤ 4 search

[`prune189.c`](prune189.c) with SMAX=4 discards a graph, intermediate or final, if some vertex
has more than four vertices at distance two, or if too few vertices can still end with degree at
most four. The README's argument for SMAX=3 applies word for word. Distance two in an induced
subgraph is distance two in the whole graph, and degrees only grow along `geng`'s chain of
induced subgraphs. So every (H) graph with σ ≤ 4 and n vertices survives the pruning of order n.
`search_reduction_four` bounds n by 15 and justifies `geng -d4` at n = 15. `hyp189`, `ind189`
and `certify.py --sigma4` then read every surviving graph and agree on the σ = 4 (H) graphs.

| n | graphs after pruning | (H) graphs with σ ≤ 4 | of which σ = 4 |
| ---: | ---: | ---: | ---: |
| 2–4 | 1, 2, 6 | 1, 2, 5 | 0 |
| 5 | 21 | 15 | 1 |
| 6 | 111 | 50 | 8 |
| 7 | 808 | 235 | 67 |
| 8 | 7,623 | 1,311 | 1,018 |
| 9 | 54,274 | 17,112 | 17,012 |
| 10 | 133,566 | 33,462 | 33,433 |
| 11 | 136,772 | 7,186 | 7,186 |
| 12 | 166,081 | 2,044 | 2,044 |
| 13 | 341,208 | 285 | 285 |
| 14 | 1,001,800 | 0 | 0 |
| 15 (`-d4`) | 23 | 0 | 0 |

For n ≤ 11 these are exactly the σ = 4 counts of the unpruned search, and for n ≤ 10 plain
`geng` gives the same graph6 strings. The other graphs in the third column have σ ≤ 3, and
their numbers match `sigma3_certificates.txt`.

## 4. What the σ = 4 data shows

The 61,054 (H) graphs with σ = 4 are listed in
[`sigma4_certificates.txt`](sigma4_certificates.txt). Together with the complete lists for
σ ≤ 3, they show the following. None of it is formalized.

- **Largest graphs.** For σ = 1, 2, 3, 4 the largest (H) graphs have n = 3σ + 1 vertices: one
  graph (P₄), 5 graphs, 29 graphs and 285 graphs. For even σ the circulant
  C_{3σ+1}(1, …, σ/2) shows that 3σ + 1 is always reached. It is σ-regular with σ vertices at
  distance two and σ at distance three from each vertex, so dist_even = σ + 1 everywhere. For
  σ = 4 it is C₁₃(1, 2), the only regular graph among the 285.
- **Where the proof loses.** In every (H) graph with σ ≤ 4, every vertex x of degree σ has
  |O(x)| ≤ σ. For σ = 3 and σ = 4, vertices of larger degree reach σ + 1. A proof of
  |O(x)| ≤ σ at degree-σ vertices would give n ≤ 3σ + 1, which is sharp for even σ. The
  transversal argument gives only |O(x)| ≤ ⌊(σ + 1)²/4⌋, which is 6 for σ = 4. In C₁₃(1, 2),
  for example, it takes s = 2 and allows three vertices of O(x) per y ∈ Y, but only two occur.
- **The hypothesis is tight at the top.** Every σ = 4 (H) graph with n = 12 or 13 has
  max dist_even = 5 = σ + 1. For 155 of the 2,044 graphs at n = 12 and 44 of the 285 at n = 13,
  every vertex has dist_even = 5.
- **Shape at n = 13.** 283 of the 285 graphs have minimum degree 4 and two have minimum degree 3.
  266 have diameter 3 and 19 have diameter 4. Seen from a vertex of minimum degree, the distance
  layers have sizes (1, 4, 4, 4) in 264 graphs, (1, 4, 3, 4, 1) in 14, (1, 4, 2, 4, 2) in 5 and
  (1, 3, 4, 5) in 2.
- **Hamiltonian cycles.** The σ = 4 (H) graphs without a Hamiltonian cycle are the ones with a
  cut vertex (Easwar–Johari's case 4), plus 19 two-connected graphs at n = 9. From n = 10 on,
  every two-connected σ = 4 (H) graph has a Hamiltonian cycle. In particular, every graph that
  Easwar–Johari's theorem leaves open has a Hamiltonian cycle, which is more than the
  conjecture asks.

| n | σ = 4 (H) graphs | max dist_even = 5 | 2-connected | Hamiltonian cycle | diameter ≥ 3 | open after Easwar–Johari |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 5 | 1 | 0 | 1 | 1 | 0 | 0 |
| 6 | 8 | 1 | 7 | 7 | 0 | 0 |
| 7 | 67 | 19 | 62 | 62 | 5 | 0 |
| 8 | 1,018 | 648 | 960 | 960 | 147 | 0 |
| 9 | 17,012 | 16,962 | 15,679 | 15,660 | 5,219 | 0 |
| 10 | 33,433 | 33,418 | 21,277 | 21,277 | 33,433 | 0 |
| 11 | 7,186 | 7,182 | 7,139 | 7,139 | 7,186 | 0 |
| 12 | 2,044 | 2,044 | 1,973 | 1,973 | 2,044 | 1,973 |
| 13 | 285 | 285 | 270 | 270 | 285 | 270 |

The last column counts the 2-connected graphs with diameter at least 3 and n ≥ 2σ + 4 = 12,
which Theorem B of Easwar and Johari does not cover. The search adds these 2,243 graphs to the
known traceable cases. It also shows that no σ = 4 (H) graph has 14 or 15 vertices.

## 5. σ = 5

For σ = 5 the bound gives n ≤ 20, and the degree bound n ≤ deg(x) + 15 restricts `geng` only
from n = 17 on. The same pruned search with SMAX=5 grows by a factor of 20 to 30 per order:

| n | graphs after pruning | CPU time |
| ---: | ---: | ---: |
| 9 | 213,221 | 0.08 s |
| 10 | 4,137,667 | 2.5 s |
| 11 | 47,134,920 | 80 s |
| 12 | about 110 million | about 28 min |

The n = 12 row is extrapolated from pieces 0, 21 and 42 of 64 (`geng -c 12 r/64`), which took
24 to 29 s and kept about 1.7 million graphs each. At this rate n = 13 needs about half a CPU-day,
and every further order multiplies the cost again, so σ = 5 was not attempted. Even the bound
n ≤ 3σ + 1 = 16 that the data suggest would not bring it within reach. A search organised by
distance layers from a vertex of degree σ might.

## 6. Approaches that did not work

- **Edge identity.** For an edge xy, the distances of any vertex to x and to y differ by at most
  one, so n = dist_even(x) + dist_even(y) + |OO(xy)| − |EE(xy)|. Here OO(xy) and EE(xy) are
  the vertices at odd, respectively even, distance from both ends. We found no bound on OO(xy)
  that improves on the vertex bounds.
- **Induced paths.** For an induced path x–y–w, let c(v) be the number of vertices among x, y
  and w at even distance from v. Double counting gives
  n = Σ_r dist_even(r) − Σ_{c(v) ≥ 1} (c(v) − 1) + |U|, where r runs over x, y and w and U is the
  set of vertices at odd distance from all three. Under (H) this is n ≤ 3(σ + 1) + |U| minus the
  overlaps, and U could not be bounded well enough.
