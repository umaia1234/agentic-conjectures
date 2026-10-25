**English** | [한국어](DETAILS.ko.md)

# Mathematical details for WOWII Conjecture 72

This file states every step of the refutation together with the Lean
declaration or internal `have` that proves it. All names refer to
[`AgenticConjectures/WowiiGraphConjecture72.lean`](../../AgenticConjectures/WowiiGraphConjecture72.lean),
namespace `AgenticConjectures.WowiiGraphConjecture72`.

Scope: this refutes only the Formal Conjectures statement `conjecture72` at
`c094b97`, which divides only \(L\) by 3. The evenly divided reading
\(\lceil(A+L)/3\rceil\le\operatorname{tree}(G)\) is not addressed. The falsity
of this statement was already stated publicly on 2026-07-23; see the
[README](README.md#prior-art-and-status).

## Notation

The counterexample lives on any vertex type \(V\) with an equivalence
\(e:V\simeq\) `Fin 28`. The vertex \(e^{-1}(i)\) is called \(i\) below.

| Notation | Meaning | Lean |
| --- | --- | --- |
| \(G\) | the counterexample | `graph e` |
| \(\ell(v)\) | the level of \(v\), in \(\{0,\dots,6\}\) | `lvl (e v)` |
| \(d(x,y)\) | graph distance | `(graph e).dist x y` |
| \(\operatorname{ecc}(v)\) | eccentricity, as a natural number | `((graph e).eccent v).toNat` |
| \(A\) | average eccentricity | `averageEccentricity (graph e)` |
| \(\lambda(v)\) | independence number of the subgraph induced by \(N(v)\) | `indepNeighborsCard (graph e) v` |
| \(L\) | \(\max_v\lambda(v)\) | `maxL`, written `(Finset.univ.image …).max' hne` |
| \(\operatorname{tree}(G)\) | order of a largest induced tree | `largestInducedTreeSize (graph e)` |

The named vertices are \(p_0=0\), \(p_1=1\), \(m_1,\dots,m_4=2,\dots,5\),
\(p_3=6\), \(p_4=7\), \(q_1,\dots,q_{10}=8,\dots,17\) and
\(r_1,\dots,r_{10}=18,\dots,27\), as in [`g28.txt`](g28.txt).

## Dependency chain

```text
refuted (§6)
└── tree_lt_ceil (§5)
    ├── averageEccentricity_ge (§2.3)
    │   └── sum_ecc_ge (§2.2) ── ecc_ge (§2.1) ── lvl_le_dist ── lvl_walk
    │                                          └── graph_connected (§1.2)
    ├── five_le_indepNeighborsCard (§3) ── card_le_indepNeighborsCard
    └── largestInducedTreeSize_le (§4.5) ── card_le_seven (§4.3, §4.4)
        ├── not_isAcyclic_of_triangle, not_isAcyclic_of_square (§4.1)
        ├── of_preserved (§4.2)
        └── adj_of_succ, adj_of_le_one, adj_of_five_le (§1.1)
```

## 1. The graph

### 1.1 Levels and adjacency

`lvl` gives \(\ell=0\) to \(q_i\), 1 to \(p_0\), 2 to \(p_1\), 3 to \(m_i\), 4
to \(p_3\), 5 to \(p_4\) and 6 to \(r_i\). Facts about the 28 values are proved
by `decide` in the kernel:

- `lvl_le_six`: \(\ell\le6\);
- `lvl_eq_one`, `lvl_eq_two`, `lvl_eq_four`, `lvl_eq_five`: the levels 1, 2,
  4 and 5 contain only \(p_0\), \(p_1\), \(p_3\) and \(p_4\);
- `lvl_eq_three`: level 3 consists of \(m_1,\dots,m_4\).

`graph e` makes two vertices adjacent when they are distinct and
\(\ell(u)+1=\ell(v)\), or \(\ell(v)+1=\ell(u)\), or \(\ell(u)=\ell(v)=0\), or
\(\ell(u)=\ell(v)=6\). This relation is symmetric and irreflexive.
[`verify_wowii72.py`](verify_wowii72.py) checks that it gives exactly the 120
edges of `g28.txt`.

- `lvl_adj`: along an edge the level changes by at most 1.
- `adj_of_succ`: vertices on consecutive levels are adjacent.
- `adj_of_le_one`: two distinct vertices of level at most 1 are adjacent.
  Both cannot have level 1, since only \(p_0\) does. So their levels are 0 and
  0, or 0 and 1. `adj_of_five_le` is the same statement for levels at least 5.

So levels 0 and 1 form a clique \(K_{11}\), and so do levels 5 and 6.

### 1.2 Connectivity: `graph_connected`

Let \(\operatorname{depth}(i)=|\ell(i)-2|\) (`depth`). The vertex `par i`
is \(p_0\) for level 0, \(m_1\) for level 4, \(p_3\) for level 5, \(p_4\) for
level 6, and \(p_1\) otherwise. `par_spec` (by `decide`) says that for
\(i\ne p_1\) we have `par i` \(\ne i\),
\(\operatorname{depth}(\texttt{par } i)+1=\operatorname{depth}(i)\), and the
two levels are consecutive, so `par i` is a neighbour of \(i\). By induction on
the depth, every vertex reaches \(p_1\); depth 0 means \(i=p_1\)
(`depth_eq_zero`). Hence \(G\) is connected.

## 2. Average eccentricity

### 2.1 Distances dominate level differences: `lvl_walk`, `lvl_le_dist`, `ecc_ge`

- `lvl_walk`: along a walk of length \(k\) the level changes by at most \(k\).
  This is induction on the walk with `lvl_adj`.
- `lvl_le_dist`: apply this to a shortest path
  (`Connected.exists_path_of_dist`), so \(|\ell(u)-\ell(v)|\le d(u,v)\).
- `ecc_ge`: \(\max(\ell(u),6-\ell(u))\le\operatorname{ecc}(u)\).
  1. `hne`: \(G\) is connected and finite, so its extended diameter is finite
     (`connected_iff_ediam_ne_top`), and so is `eccent u`
     (`eccent_le_ediam`).
  2. `key`: \(d(u,w)\le\operatorname{ecc}(u)\) for every \(w\), from
     `edist_le_eccent`, `Reachable.coe_dist_eq_edist` and `ENat.toNat_le_toNat`.
  3. Apply `key` and `lvl_le_dist` with \(w=r_1\) (level 6) and \(w=q_1\)
     (level 0). Then \(6-\ell(u)\le d(u,r_1)\le\operatorname{ecc}(u)\) and
     \(\ell(u)\le d(u,q_1)\le\operatorname{ecc}(u)\).

### 2.2 The sum: `sum_ecc_ge`

`sum_lvl` (by `decide`) gives
\(\sum_{i<28}\max(\ell(i),6-\ell(i))=150\). The levels contribute
\(10\cdot6+5+4+4\cdot3+4+5+10\cdot6=150\). Reindexing along \(e\)
(`Equiv.sum_comp`) and `ecc_ge` give \(\sum_v\operatorname{ecc}(v)\ge150\).

### 2.3 The average: `averageEccentricity_ge`

\(|V|=28\) (`Fintype.card_congr e`), so \(A=\frac1{28}\sum_v
\operatorname{ecc}(v)\ge150/28=75/14\). The bound is attained: the script
finds eccentricities 6, 5, 4, 3, 4, 5, 6 on levels 0 to 6. Lean needs only the
lower bound.

## 3. Local independence: `five_le_indepNeighborsCard`

`card_le_indepNeighborsCard u S`: if every vertex of \(S\) is adjacent to
\(u\) and \(S\) is independent, then \(|S|\le\lambda(u)\). The proof views
\(S\) as an independent set of the subgraph induced by \(N(u)\) and applies
`IsIndepSet.card_le_indepNum`.

Apply it with \(u=p_1\) and \(S=\{p_0,m_1,\dots,m_4\}\).

- These vertices have levels 1 and 3, so each is adjacent to \(p_1\), which
  has level 2.
- Two of them have levels differing by 0 or 2, and none has level 0 or 6, so
  no two are adjacent.

Hence \(L\ge\lambda(p_1)\ge5\). The step from \(\lambda(p_1)\) to the maximum is
`Finset.le_max'`, inside `tree_lt_ceil`. In fact \(L=5\), attained at \(p_1\)
and \(p_3\), as the script finds.

## 4. Induced trees have at most seven vertices

### 4.1 Short cycles: `not_isAcyclic_of_triangle`, `not_isAcyclic_of_square`

Let \(s\) be a vertex set.

- If \(a,b,c\in s\) are pairwise adjacent, the edge \(ab\) and the path
  \(a\,c\,b\) are two paths from \(a\) to \(b\) in the subgraph induced by
  \(s\), of lengths 1 and 2. This contradicts `IsAcyclic.path_unique`.
- If \(a,b,c,d\in s\) form a 4-cycle \(a\,b\,c\,d\,a\) with \(a\ne c\) and
  \(b\ne d\), the paths \(a\,b\,c\) and \(a\,d\,c\) have different supports.

### 4.2 Propagation: `of_preserved`

Suppose the subgraph induced by \(s\) is connected, and a property \(P\) passes
from \(u\) to \(v\) whenever \(u,v\in s\) are adjacent. If \(P\) holds at one
vertex of \(s\), it holds at every vertex of \(s\). The proof is induction on a
walk in the induced subgraph.

### 4.3 Facts about an induced tree: `card_le_seven`

Let \(T\) be a vertex set that induces a tree. The proof splits \(T\) by
level:

- `sQ` is the part of level at most 1;
- `s1` is the part of level 2;
- `sM` is the part of level 3;
- `s6` is the part of level 4;
- `sR` is the part of level at least 5.

`htot` gives \(|T|\le\) `sQ.card + s1.card + sM.card + s6.card + sR.card`. The
internal `have`s are the following.

- `hQ`, `hR`: \(|sQ|\le2\) and \(|sR|\le2\). Three vertices of one clique form
  a triangle (§4.1).
- `hM`: \(|sM|\le4\), since `sM` lies in \(\{m_1,\dots,m_4\}\).
- `h1`, `h6`: \(|s1|\le1\) and \(|s6|\le1\), since levels 2 and 4 contain one
  vertex each.
- `h1'`, `h6'`: if \(p_1\notin T\) then `s1` is empty, and if \(p_3\notin T\)
  then `s6` is empty.
- `hsq`: if \(|sM|\ge2\), then \(p_1\) and \(p_3\) are not both in \(T\).
  Otherwise two vertices \(m,m'\) of `sM` would form the 4-cycle
  \(p_1\,m\,p_3\,m'\,p_1\) (§4.1).
- `hiso`: if \(p_1,p_3\notin T\) and \(m\in sM\), then \(T=\{m\}\). The only
  neighbours of \(m\) are \(p_1\) and \(p_3\), so the property "equals \(m\)"
  passes along every edge inside \(T\). By §4.2 every vertex of \(T\) equals
  \(m\).
- `hsepR`: if \(p_1\in T\) and \(p_3\notin T\), then `sR` is empty. An edge
  from level at most 4 to level at least 5 must start at level 4, that is at
  \(p_3\). So "level at most 4" passes along edges inside \(T\). It holds at
  \(p_1\), so by §4.2 it holds on all of \(T\).
- `hsepQ`: symmetrically, if \(p_3\in T\) and \(p_1\notin T\), then `sQ` is
  empty, using the property "level at least 2".

### 4.4 The four cases

| \(p_1\in T\) | \(p_3\in T\) | Used | Bound on \(\lvert T\rvert\) |
| --- | --- | --- | --- |
| yes | yes | `hsq`: \(\lvert sM\rvert\le1\) | \(2+1+1+1+2=7\) |
| yes | no | `hsepR`, `h6'` | \(2+1+4=7\) |
| no | yes | `hsepQ`, `h1'` | \(4+1+2=7\) |
| no | no | `h1'`, `h6'`, then `hiso` if `sM` is nonempty | \(1\), or \(2+2=4\) |

### 4.5 The tree number: `largestInducedTreeSize_le`

Every element of the set in the definition of `largestInducedTreeSize` is the
order of a vertex set that induces a tree, so it is at most 7. `csSup_le'` then
gives \(\operatorname{tree}(G)\le7\). In fact \(\operatorname{tree}(G)=7\):
\(\{q_1,p_0,p_1,m_1,\dots,m_4\}\) induces a tree. The script checks this, and
Lean does not need it.

## 5. The violation: `tree_lt_ceil`

From §2.3 and §3, \(A+L/3\ge75/14+5/3=295/42>7\). By `Int.lt_ceil`,
\(7<\lceil A+L/3\rceil\) in \(\mathbb Z\), so \(8\le\lceil A+L/3\rceil\) after
casting to \(\mathbb R\). With §4.5,
\(\operatorname{tree}(G)\le7<8\le\lceil A+L/3\rceil\). The margin before
rounding is only \(295/42-7=1/42\).

## 6. The refutation: `refuted`

`statement.{u}` says that every finite connected graph on a vertex type
`α : Type u` with at least two vertices satisfies
\(\lceil A+L/3\rceil\le\operatorname{tree}(G)\). Apply it to
`α = ULift (Fin 28)` and `graph Equiv.ulift`. The instances `Fintype`,
`DecidableEq` and `Nontrivial` of `ULift (Fin 28)` come from mathlib, and
connectivity is `graph_connected`. The conclusion contradicts `tree_lt_ceil`.
So `refuted : ¬ statement.{u}` holds in every universe.

## 7. Checks outside Lean

- [`verify_wowii72.py`](verify_wowii72.py) recomputes the exact values
  \(A=75/14\), \(L=5\) and \(\operatorname{tree}(G)=7\), with two independent
  computations of the tree number (README, *Numerical cross-check*).
- On \(G\) the evenly divided reading holds:
  \(\lceil(A+L)/3\rceil=\lceil145/42\rceil=4\le7\).
- No connected graph with at most 10 vertices violates either reading.
