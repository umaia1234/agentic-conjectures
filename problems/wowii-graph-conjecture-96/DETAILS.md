**English** | [한국어](DETAILS.ko.md)

# Mathematical details for WOWII Conjecture 96

This file states every step of the proof together with the Lean declaration
or internal `have` that proves it. All names refer to
[`AgenticConjectures/WowiiGraphConjecture96.lean`](../../AgenticConjectures/WowiiGraphConjecture96.lean),
namespace `AgenticConjectures.WowiiGraphConjecture96`.

## Notation

\(G\) is a finite simple graph on a vertex type \(V\) with \(n=|V|\).

| Notation | Meaning | Lean |
| --- | --- | --- |
| \(d(x,y)\) | graph distance; 0 if \(y\) is unreachable from \(x\) | `G.dist x y` |
| \(N(u)\) | open neighbourhood of \(u\) | `G.neighborSet u` |
| \(\alpha\) | independence number of \(G\) | `G.indepNum` |
| \(\lambda(u)\) | independence number of the subgraph induced by \(N(u)\) | `indepNeighborsCard G u` |
| \(\mathcal E_v\) | the set \(\{w : d(v,w)\text{ even}\}\), which contains \(v\) | `Finset.univ.filter fun w => Even (G.dist v w)` |
| \(E(v)\) | \(\lvert\mathcal E_v\rvert\) | `distEven G v` |
| \(\Lambda\) | \(\max_u\lambda(u)\) | `maxL` in `conjecture96` |
| \(a\mathbin{\dot-}b\) | truncated natural-number subtraction | `a - b` on `ℕ` |

## Dependency chain

```text
conjecture96 (§6)
├── one_le_indepNeighborsCard (§2.3)
│   ├── exists_parent (§1.1)
│   └── card_le_indepNeighborsCard (§2.1)
├── indepNum_le_one (§3)
│   ├── exists_dist_two (§1.2)
│   ├── exists_parent (§1.1)
│   └── two_le_indepNeighborsCard (§2.2) ── card_le_indepNeighborsCard (§2.1)
└── indepNum_le_of_two_le (§5)
    └── indepNum_le_perRoot (§4)
        ├── exists_parent (§1.1)
        └── card_le_indepNeighborsCard (§2.1)
```

`statement_holds` is `conjecture96` quantified over all finite vertex types
with at least two elements.

## 1. Distance facts

**Fact 1.0** (mathlib `SimpleGraph.Adj.diff_dist_adj`). If \(a\) and \(b\) are
adjacent, then for every \(u\) the distance \(d(u,b)\) equals \(d(u,a)\),
\(d(u,a)+1\) or \(d(u,a)\mathbin{\dot-}1\). This needs no connectivity
hypothesis.

### 1.1 BFS parent: `exists_parent`

**Claim.** Let \(G\) be connected and \(x\ne v\). Then some \(y\) is adjacent
to \(x\) with \(d(v,y)+1=d(v,x)\).

**Proof.**

1. Take a path \(p\) from \(v\) to \(x\) of length \(d(v,x)\)
   (`Connected.exists_path_of_dist`).
2. Its reverse is a walk from \(x\) to \(v\) of the same length. The internal
   `key` analyses this walk by cases.
   - The `nil` case would force \(x=v\), which is excluded.
   - In the `cons` case the walk starts with an edge \(x\sim y\) and continues
     with a walk \(q'\) from \(y\) to \(v\) with
     \(\lvert q'\rvert+1=d(v,x)\) (`hlen`).
3. Since \(d(y,v)\le\lvert q'\rvert\) (`dist_le`) and distance is symmetric,
   \(d(v,y)\le d(v,x)-1\) (`h1`).
4. Fact 1.0 for the edge \(y\sim x\) excludes \(d(v,y)<d(v,x)-1\). So
   \(d(v,y)+1=d(v,x)\).

### 1.2 A vertex at distance two: `exists_dist_two`

**Claim.** Let \(G\) be connected with \(d(x,z)\ge2\). Then some \(w\)
satisfies \(d(x,w)=2\).

**Proof.** Write \(d(x,z)=k+2\) and induct on \(k\).

- If \(k=0\), take \(w=z\).
- Otherwise \(z\ne x\), because \(d(x,x)=0\). By §1.1 with root \(x\), \(z\) has
  a neighbour \(y\) with \(d(x,y)=k+1\). Apply the induction hypothesis to
  \(y\).

## 2. Local independence bounds

### 2.1 `card_le_indepNeighborsCard`

**Claim.** If \(S\subseteq N(u)\) and no two distinct elements of \(S\) are
adjacent, then \(\lvert S\rvert\le\lambda(u)\).

**Proof.**

1. Lift \(S\) to a finset \(T\) of the subtype `G.neighborSet u`. Then
   \(\lvert T\rvert=\lvert S\rvert\) (`hT`, from `Finset.card_subtype`, since
   every element of \(S\) satisfies the predicate).
2. In `G.induce (G.neighborSet u)`, two elements are adjacent exactly when
   their underlying vertices are adjacent in \(G\) (`comap_adj`). So \(T\) is
   independent there.
3. `IsIndepSet.card_le_indepNum` gives \(\lvert T\rvert\le\lambda(u)\). The
   subtype is `Finite` because \(V\) is a `Fintype`.

### 2.2 `two_le_indepNeighborsCard`

**Claim.** If \(x\sim y\), \(y\sim z\), \(x\ne z\) and \(x\not\sim z\), then
\(\lambda(y)\ge2\).

**Proof.** Apply §2.1 to \(S=\{x,z\}\subseteq N(y)\). The set is independent
because \(x\not\sim z\), and has two elements because \(x\ne z\)
(`Finset.card_pair`).

### 2.3 `one_le_indepNeighborsCard` (uses `[Nontrivial α]`)

**Claim.** Let \(G\) be connected with \(n\ge2\). Then \(\lambda(u)\ge1\) for
every \(u\).

**Proof.**

1. Since \(n\ge2\), some \(x\) differs from \(u\) (`exists_ne`).
2. By §1.1 with root \(x\), \(u\) has a neighbour \(y\).
3. Apply §2.1 to \(S=\{y\}\).

This is the only step that needs \(n\ge2\). The other use of
`[Nontrivial α]` is that the vertex set is nonempty, so `min'` and `max'`
exist. For \(K_1\), \(\lambda=0\) and the conjecture fails.

## 3. Case \(\Lambda\le1\): `indepNum_le_one`

**Claim.** Let \(G\) be connected with \(\lambda(u)\le1\) for every \(u\). Then
\(\alpha\le1\).

**Proof.**

1. Take an independent set \(I\) with \(\lvert I\rvert=\alpha\)
   (`exists_isNIndepSet_indepNum`, `card_eq`). Assume
   \(\lvert I\rvert>1\) (`hlt'`).
2. Pick distinct \(x,z\in I\) (`Finset.one_lt_card`). They are not adjacent
   (`hnadj`).
3. \(d(x,z)\ne0\) because \(x\ne z\) and \(G\) is connected
   (`Connected.dist_eq_zero_iff`). \(d(x,z)\ne1\) because \(x\not\sim z\)
   (`dist_eq_one_iff_adj`). So \(d(x,z)\ge2\) (`h2`).
4. By §1.2, some \(w\) has \(d(x,w)=2\). In particular \(w\ne x\) (`hwx`).
5. By §1.1 with root \(x\), \(w\) has a neighbour \(y\) with \(d(x,y)=1\).
   Hence \(x\sim y\) (`hxy`).
6. \(x\not\sim w\), since otherwise \(d(x,w)=1\) (`hnxw`).
7. §2.2 on \(x\sim y\sim w\) gives \(\lambda(y)\ge2\). This contradicts
   \(\lambda(y)\le1\).

## 4. Per-root bound: `indepNum_le_perRoot`

**Claim.** Let \(G\) be connected; no lower bound on \(n\) is needed. For every
vertex \(v\),

\[
\alpha\le\max\bigl(1,\lambda(v)\bigr)
+\sum_{u\in\mathcal E_v\setminus\{v\}}\max\bigl(1,\lambda(u)\mathbin{\dot-}1\bigr).
\]

**Setup.**

- \(I\) is an independent set with \(\lvert I\rvert=\alpha\). The internal
  `hind` records that no two distinct elements of \(I\) are adjacent.
- `hpar` and `choose` give a function \(\pi\) (`par`). For \(x\ne v\),
  \(\pi(x)\sim x\) and \(d(v,\pi(x))+1=d(v,x)\), by §1.1. The value
  \(\pi(v)\) is never used.
- \(\varphi(x)=x\) if \(d(v,x)\) is even, and \(\varphi(x)=\pi(x)\)
  otherwise (`φ`).
- The fibre over \(u\) is \(F(u)=\{x\in I:\varphi(x)=u\}\).

**Step 4.1 (`hφ`).** If \(\varphi(x)=u\) and \(x\ne u\), then \(u\sim x\) and
\(d(v,u)+1=d(v,x)\).

- If \(d(v,x)\) is even, then \(\varphi(x)=x=u\), which is excluded.
- Otherwise \(x\ne v\), because \(d(v,v)=0\) is even. Then \(u=\pi(x)\), and
  the parent property applies.

**Step 4.2 (`hmaps`).** \(\varphi\) maps \(I\) into \(\mathcal E_v\).

- If \(d(v,x)\) is even, then \(\varphi(x)=x\in\mathcal E_v\).
- Otherwise \(d(v,x)=d(v,\pi(x))+1\) is odd, so \(d(v,\pi(x))\) is even
  (`Nat.even_add_one`).

**Step 4.3 (`hF1`).** If \(u\in I\), then \(\lvert F(u)\rvert\le1\).

Let \(x\in F(u)\) with \(x\ne u\). By 4.1, \(u\sim x\), but \(u\) and \(x\) are
distinct elements of \(I\). So \(F(u)\subseteq\{u\}\).

**Step 4.4 (`hfib`).** If \(u\notin I\) and \(x\in F(u)\), then \(u\sim x\) and
\(d(v,u)+1=d(v,x)\).

Here \(x\in I\) and \(u\notin I\), so \(x\ne u\). Apply 4.1.

**Step 4.5 (`hF2`).** If \(u\notin I\), then \(\lvert F(u)\rvert\le\lambda(u)\).

By 4.4, \(F(u)\subseteq N(u)\). Also \(F(u)\subseteq I\) is independent. Apply
§2.1.

**Step 4.6 (`hF3`).** If \(u\notin I\) and \(u\ne v\), then
\(\lvert F(u)\rvert+1\le\lambda(u)\).

Let \(w=\pi(u)\). Since \(u\ne v\), \(w\sim u\) and \(d(v,w)+1=d(v,u)\).

- (a) \(w\notin F(u)\) (`hwnot`). Every \(x\in F(u)\) has \(d(v,x)=d(v,u)+1\)
  by 4.4, while \(d(v,w)=d(v,u)-1\).
- (b) \(w\) is adjacent to no \(x\in F(u)\) (`hnadj`). Here
  \(d(v,x)=d(v,w)+2\), but adjacent vertices have distances to \(v\) that
  differ by at most 1 (Fact 1.0).
- (c) Let \(S=F(u)\cup\{w\}\).
  - \(S\subseteq N(u)\): \(w\sim u\), and \(F(u)\subseteq N(u)\) by 4.4.
  - \(S\) is independent. Pairs inside \(F(u)\subseteq I\) are non-adjacent,
    and pairs \((w,x)\) are non-adjacent by (b).
  - §2.1 gives \(\lvert S\rvert\le\lambda(u)\), and
    \(\lvert S\rvert=\lvert F(u)\rvert+1\) by (a) and
    `Finset.card_insert_of_notMem`.

Whether \(w\) lies in \(I\) does not matter.

**Step 4.7 (assembly).** Since \(\varphi\) maps \(I\) into \(\mathcal E_v\)
(4.2) and \(v\in\mathcal E_v\) (`hv`),

\[
\alpha=\lvert I\rvert=\sum_{u\in\mathcal E_v}\lvert F(u)\rvert
=\lvert F(v)\rvert+\sum_{u\in\mathcal E_v\setminus\{v\}}\lvert F(u)\rvert
\]

by `Finset.card_eq_sum_card_fiberwise` and `Finset.add_sum_erase`. Then each
term is bounded:

| Term | Case | Bound | Reference |
| --- | --- | --- | --- |
| \(\lvert F(v)\rvert\) | \(v\in I\) | \(\le1\le\max(1,\lambda(v))\) | 4.3 |
| \(\lvert F(v)\rvert\) | \(v\notin I\) | \(\le\lambda(v)\le\max(1,\lambda(v))\) | 4.5 |
| \(\lvert F(u)\rvert\), \(u\ne v\) | \(u\in I\) | \(\le1\le\max(1,\lambda(u)\mathbin{\dot-}1)\) | 4.3 |
| \(\lvert F(u)\rvert\), \(u\ne v\) | \(u\notin I\) | \(\le\lambda(u)\mathbin{\dot-}1\le\max(1,\lambda(u)\mathbin{\dot-}1)\) | 4.6 |

In the last row \(\lambda(u)\ge\lvert F(u)\rvert+1\ge1\), so the truncated
subtraction is the ordinary one. `add_le_add` and `Finset.sum_le_sum` combine
the bounds.

## 5. Case \(\Lambda\ge2\): `indepNum_le_of_two_le`

**Claim.** Let \(G\) be connected, \(L\ge2\), and \(\lambda(u)\le L\) for every
\(u\). Then \(\alpha\le1+E(v)(L-1)\) for every \(v\).

**Proof.**

1. Each summand satisfies \(\max(1,\lambda(u)\mathbin{\dot-}1)\le L-1\),
   because \(1\le L-1\) and \(\lambda(u)\mathbin{\dot-}1\le L-1\). There are
   \(\lvert\mathcal E_v\setminus\{v\}\rvert=E(v)-1\) summands
   (`Finset.card_erase_of_mem`). So the sum is at most \((E(v)-1)(L-1)\)
   (`hsum`, via `Finset.sum_le_card_nsmul`).
2. \(\max(1,\lambda(v))\le L\) (`hroot`).
3. \(E(v)\ge1\) because \(v\in\mathcal E_v\) (`hE`).
4. With §4, \(\alpha\le L+(E(v)-1)(L-1)\). Substitute \(E(v)=e+1\) and
   \(L=m+1\). The bound becomes \(\alpha\le(m+1)+em=1+(e+1)m\). This is the
   claim; `hring` and `omega` close it.

## 6. The theorem: `conjecture96`

Write `minDistEven` for the minimum of the image of `distEven G`, and `maxL`
for the maximum of the image of `indepNeighborsCard G`. Both images are
nonempty because the vertex type is nonempty.

1. `hl`: \(\lambda(u)\le\) `maxL` for every \(u\) (`Finset.le_max'`).
2. Some \(v\) has `distEven G v = minDistEven` (`Finset.min'_mem`,
   `Finset.mem_image`).
3. `hL1`: `maxL` \(\ge1\), by §2.3 at \(v\).
4. `key`: \(\alpha\le1+\) `minDistEven` \(\cdot\) (`maxL` \(-1\)) in \(\mathbb N\).
   - If `maxL` \(<2\), every \(\lambda(u)\le1\). By §3, \(\alpha\le1\), which is
     at most the right-hand side.
   - If `maxL` \(\ge2\), apply §5 at the minimiser \(v\) with \(L=\) `maxL`.
5. `hcast`: since `maxL` \(\ge1\), the cast of the natural number
   `maxL - 1` to \(\mathbb R\) is the real number `(maxL : ℝ) - 1`
   (`Nat.cast_sub`). So `key` cast to \(\mathbb R\) is exactly the upstream
   inequality.

## 7. Boundary and tightness checks

- **\(n=1\).** `[Nontrivial α]` excludes this case. The literal row is false
  here (\(1\le0\)). The per-root bound of §4 still holds:
  \(1\le\max(1,0)+0\).
- **\(K_2\) and every \(K_n\), \(n\ge2\).** Here \(\alpha=1\) and
  \(\Lambda=1\), so the right-hand side is 1. The bound is tight, through §3.
- **Stars \(K_{1,m}\), \(m\ge2\).** The centre \(c\) has \(E(c)=1\) and
  \(\lambda(c)=m\). Each leaf has \(E=m\) and \(\lambda=1\). Also
  \(\alpha=m=1+1\cdot(m-1)\), so the bound is tight, through §5. In §4 with
  root \(c\), \(I\) is the set of leaves, all of them odd. Their common parent
  is \(c\notin I\), and the fibre over \(c\) has \(m=\lambda(c)\) elements
  (step 4.5).
- **Numerical check.** [`verify_wowii96.py`](verify_wowii96.py) re-checks both
  inequalities on every connected graph up to 10 vertices; see the
  [README](README.md#numerical-cross-check).
