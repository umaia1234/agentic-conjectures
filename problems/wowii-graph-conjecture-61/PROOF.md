**English** | [한국어](PROOF.ko.md)

# Partial Theorems for WOWII Graph Conjecture 61

## Notation and basic inequality

For a finite simple connected graph \(G\) we write

- \(\alpha(G)\): the independence number,
- \(f(G)\): the number of vertices of a maximum induced forest,
- \(r(G)\): the Havel--Hakimi residue,
- \(D(G)\): the diameter.

The Havel--Hakimi residue is the number of zeros remaining after
repeatedly applying Havel--Hakimi elimination to the degree sequence. In
this document we use the basic inequality

\[
r(G)\le\alpha(G). \tag{1}
\]

The original inequality under examination is

\[
f(G)\ge r(G)+\left\lceil\frac{D(G)}3\right\rceil. \tag{2}
\]

## Theorem 1: A general lower bound using the independence number and the diameter

For every finite simple connected graph \(G\),

\[
\boxed{f(G)\ge\alpha(G)+\left\lceil\frac{D(G)}4\right\rceil.} \tag{3}
\]

### Proof

If \(D=0\), the graph has one vertex and the claim is trivial. Now
suppose \(D\ge1\). Let \(I\) be a maximum independent set and let

\[
P=v_0v_1\cdots v_D
\]

be a geodesic path realizing the diameter. Define the position set

\[
S:=\{i\in\{0,\ldots,D\}:v_i\notin I\}.
\]

Since \(I\) is an independent set, consecutive \(v_i,v_{i+1}\) cannot
both belong to \(I\). Hence every consecutive position pair
\(\{i,i+1\}\) meets \(S\).

Perform the following greedy selection on \(S\).

\[
s_1=\min S,
\]

\[
s_{j+1}=\min\{s\in S:s\ge s_j+3\},
\]

stopping when no next choice exists. Let \(m\) be the number of choices.
Since the first consecutive position pair meets \(S\), we have
\(s_1\le1\). If a next choice exists, at least one of \(s_j+3,s_j+4\)
lies in \(S\), so

\[
s_{j+1}\le s_j+4.
\]

If \(D\ge s_m+4\) after the last choice, one of \(s_m+3,s_m+4\) could
still be chosen, a contradiction. Therefore

\[
D\le s_m+3\le1+4(m-1)+3=4m.
\]

That is,

\[
m\ge\left\lceil\frac D4\right\rceil. \tag{4}
\]

Set

\[
X:=\{v_{s_1},\ldots,v_{s_m}\}.
\]

The distance along \(P\) between any two distinct vertices of \(X\) is
at least 3. A subpath of a geodesic path is again a geodesic path, so
the \(G\)-distance between the two vertices is also at least 3. Hence
the two vertices are not adjacent and have no common neighbor.

Accordingly, in \(G[I\cup X]\),

- there are no edges inside \(I\),
- there are no edges inside \(X\), and
- a vertex of \(I\) cannot be adjacent to two vertices of \(X\) at the
  same time.

Therefore \(G[I\cup X]\) is a disjoint union of stars with centers in
\(X\) together with isolated vertices; in particular, it is a forest.
Hence

\[
f(G)\ge|I|+|X|
\ge\alpha(G)+\left\lceil\frac D4\right\rceil.
\]

## Theorem 2: Minimum slack and the diameter

In a connected graph with at least two vertices,

\[
f(G)\ge\alpha(G)+1. \tag{5}
\]

Moreover,

\[
\boxed{f(G)=\alpha(G)+1\implies D(G)\le4.} \tag{6}
\]

### Proof

Choose a maximum independent set \(I\). In a connected nontrivial graph
\(I\ne V(G)\), so we can pick some \(x\in V(G)\setminus I\).
\(G[I\cup\{x\}]\) is a union of one star and isolated vertices, hence an
induced forest, and (5) holds.

Now assume \(f(G)=\alpha(G)+1\) and set

\[
J:=V(G)\setminus I.
\]

If \(|J|=1\), then by connectivity \(G\) is a star and \(D\le2\).

Suppose \(|J|\ge2\) and choose distinct \(x,y\in J\). The size of
\(I\cup\{x,y\}\) is \(\alpha+2\), so this set cannot induce a forest and
therefore contains a cycle.

If \(xy\in E(G)\), then \(d(x,y)=1\). If \(xy\notin E(G)\), then since
\(I\) is independent and the only vertices outside \(I\) are \(x,y\),
the cycle contains a 4-cycle of the form

\[
x-u-y-v-x.
\]

Hence \(x,y\) have a common neighbor and \(d(x,y)=2\). In the end,

\[
d(x,y)\le2\qquad(x,y\in J). \tag{7}
\]

Each \(i\in I\) has a neighbor in \(J\) by connectivity. Therefore

\[
d(i,y)\le3\qquad(i\in I,\ y\in J),
\]

\[
d(i,j)\le4\qquad(i,j\in I).
\]

The distance between every two vertices is at most 4, so \(D(G)\le4\).

## Theorem 3: Completely settled diameters

(2) holds in every connected graph with

\[
\boxed{D(G)\in\{0,1,2,3,5,6,9\}.}
\]

### Proof

If \(D=0\), the graph has one vertex and the claim is trivial by (1).

If \(D\in\{1,2,3\}\), then

\[
\left\lceil\frac D4\right\rceil
=\left\lceil\frac D3\right\rceil=1.
\]

Hence, from (1) and (3),

\[
f(G)\ge\alpha(G)+1\ge r(G)+1.
\]

If \(D\in\{5,6\}\), then by (5) we have \(f\ge\alpha+1\). By (6)
equality is impossible, and since \(f,\alpha\) are integers,

\[
f(G)\ge\alpha(G)+2.
\]

Also \(\lceil D/3\rceil=2\), so (2) holds.

If \(D=9\), then from (3),

\[
f(G)\ge\alpha(G)+\left\lceil\frac94\right\rceil
=\alpha(G)+3\ge r(G)+3,
\]

and \(\lceil9/3\rceil=3\).

## Theorem 4: All trees

Every finite tree \(T\) satisfies (2) regardless of diameter.

### Proof

Set

\[
n:=|V(T)|,
\]

\[
\nu(T):=\text{the maximum matching number},
\qquad
\tau(T):=\text{the minimum vertex cover number}.
\]

The tree itself is a forest, so

\[
f(T)=n. \tag{8}
\]

By the complementation relation between independent sets and vertex
covers,

\[
\alpha(T)=n-\tau(T). \tag{9}
\]

Every vertex cover must contain at least one distinct endpoint from each
edge of a matching, so

\[
\tau(T)\ge\nu(T). \tag{10}
\]

A diameter path has \(D+1\) vertices, and choosing alternate edges
yields a matching of size

\[
\left\lfloor\frac{D+1}{2}\right\rfloor
=\left\lceil\frac D2\right\rceil.
\]

Therefore

\[
\nu(T)\ge\left\lceil\frac D2\right\rceil. \tag{11}
\]

Combining (1), (9)--(11),

\[
r(T)\le\alpha(T)\le n-\left\lceil\frac D2\right\rceil.
\]

Consequently

\[
\begin{aligned}
r(T)+\left\lceil\frac D3\right\rceil
&\le n-\left\lceil\frac D2\right\rceil
+\left\lceil\frac D3\right\rceil\\
&\le n=f(T).
\end{aligned}
\]

Therefore (2) holds for every tree.
