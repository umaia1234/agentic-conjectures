**English** | [한국어](DETAILS.ko.md)

# Mathematical details: lower bounds and the search reduction

This note proves the three lower bounds that
[`MinModulusMultisetSum.lean`](../../AgenticConjectures/MinModulusMultisetSum.lean)
formalizes, and justifies the reduction used by the two exhaustive searches.
None of it proves Conjecture 1 in general.

Throughout, $N\ge1$, $A\subseteq\mathbb Z_N$ has $|A|=n$, and $A$ is
*valid* if the constant function $1$ is the only $m:A\to\mathbb Z_{\ge0}$
with

$$\sum_{a\in A}m(a)=n,\qquad \sum_{a\in A}m(a)\,a=\sum_{a\in A}a \pmod N .$$

Such an $m$ different from $1$ is called a *rival*.

## 1. The rival principle

**Lemma 1** (`IsValidMod.eq_of_rival`). Let $A$ be valid and
$p,q:A\to\mathbb Z_{\ge0}$ with $q\le 1+p$ pointwise,
$\sum p=\sum q$ and $\sum p(a)a=\sum q(a)a$. Then $p=q$.

*Proof.* $m=1+p-q$ takes values in $\mathbb Z_{\ge0}$, has total weight $n$
and weighted sum $\sum a$. Validity gives $m=1$, that is $p=q$. $\square$

Every argument below picks $p\neq q$ with equal weight, a pointwise bound
$q\le1+p$ (usually $q\le1$), and a weighted-sum identity that is equivalent to
the coincidence to be ruled out.

## 2. Distinct translated subset sums: $N\ge 2^{n-1}$

Fix $a_0\in A$, put $B=A\setminus\{a_0\}$, and for $S\subseteq B$ let

$$\sigma(S)=\sum_{x\in S}(x-a_0)\in\mathbb Z_N .$$

**Lemma 2** (`IsValidMod.ssum_injOn`). $\sigma$ is injective on subsets of
$B$.

*Proof.* Let $\sigma(S)=\sigma(T)$ with $S\ne T$. Removing $S\cap T$ from both
gives disjoint $S',T'$, not both empty, with $\sigma(S')=\sigma(T')$; say
$|S'|\le|T'|$. Take $p=\mathbf 1_{S'}+(|T'|-|S'|)\mathbf 1_{a_0}$ and
$q=\mathbf 1_{T'}$. Both have weight $|T'|$, and
$\sum p(a)a=\sum q(a)a$ is exactly $\sigma(S')=\sigma(T')$. Since $q\le1$,
Lemma 1 gives $p=q$, which fails at any element of $S'\cup T'$ (it lies in
$B$, so not at $a_0$, and in exactly one of the disjoint sets). $\square$

**Theorem 1** (`IsValidMod.two_pow_le`). A valid $n$-set mod $N$ has
$N\ge2^{n-1}$.

*Proof.* Lemma 2 injects the $2^{n-1}$ subsets of $B$ into $\mathbb Z_N$.
$\square$

This is the cyclic case of M. Inal's theorem for all finite abelian groups
(the translated differences $x-a_0$ form a dissociated family); see the
README for the source and for its formalization by the author of the
conjecture.

## 3. A Sidon-type property: $N\ge n(n-1)$

**Lemma 3** (`IsValidMod.add_eq_add`). If $x,w,y,z\in A$, $x\ne w$ and
$x+w=y+z$, then $\{x,w\}=\{y,z\}$.

*Proof.* Take $p=\mathbf 1_y+\mathbf 1_z$ and $q=\mathbf 1_x+\mathbf 1_w$.
Both have weight $2$, and their weighted sums are $y+z$ and $x+w$. Since
$x\ne w$, $q\le1$, so Lemma 1 gives $p=q$. Evaluating at $x$ and $w$ gives
$\{x,w\}=\{y,z\}$. $\square$

Without the hypothesis $x\neq w$ the same argument leaves a third case,
$x=w$ and $y=z$ (`IsValidMod.add_eq_add'`).

**Lemma 4** (`eq_of_two_mul_eq_zero`, `IsValidMod.half_pair_unique`).
$\mathbb Z_N$ has at most one nonzero element $h$ with $2h=0$ (namely $N/2$).
Hence, if $p\ne q$ and $r\ne s$ in $A$ satisfy $2(p-q)=2(r-s)=0$, then
$\{p,q\}=\{r,s\}$.

*Proof.* If $2h=0$ and $h\ne0$, then $h$ is $N/2$. So $p-q=r-s$, that is
$p+s=r+q$, and Lemma 3 (in the three-case form) gives $p=r,\,s=q$ or
$p=s,\,r=q$. The remaining case $p=q$ is excluded. $\square$

**Theorem 2** (`IsValidMod.card_mul_card_sub_one_le`). A valid $n$-set has
$N\ge n(n-1)$.

*Proof.* Consider the $n(n-1)$ ordered pairs $(x,y)$, $x\ne y$, and their
differences $x-y\ne0$. If $x-y=x'-y'$ for distinct pairs, then
$x+y'=x'+y$. Lemma 3 shows that this forces $(x',y')=(y,x)$, and then
$2(x-y)=0$. By Lemma 4 at most one unordered pair has a difference of order
two. So at least $n(n-1)-1$ distinct nonzero differences occur, and
$n(n-1)-1\le N-1$. $\square$

**Corollary** (`statement_of_le_four`). Conjecture 1 holds for $n\le4$:
$2^n-2^{\lfloor\log_2n\rfloor}$ equals $2,6,12$ for $n=2,3,4$, which is
$n(n-1)$.

For $n=5$ the bounds give only $N\ge20$, while the conjectured minimum is
$28$.

## 4. Doubled differences: $N\ge 2^{n-1}+n-2$

**Lemma 5** (`IsValidMod.two_mul_ne_ssum`). With $a_0,B,\sigma$ as in §2,
$b\in B$ and $\emptyset\ne T\subseteq B$, we have $2(b-a_0)\ne\sigma(T)$.

*Proof.* If $b\in T$, then $\sigma(T)=(b-a_0)+\sigma(T\setminus\{b\})$, so the
equality would give $\sigma(\{b\})=\sigma(T\setminus\{b\})$. That contradicts
Lemma 2, because $b\notin T\setminus\{b\}$. If $b\notin T$, take

$$p=2\cdot\mathbf 1_b+(|T|-2)^+\,\mathbf 1_{a_0},\qquad
q=\mathbf 1_T+(2-|T|)^+\,\mathbf 1_{a_0}.$$

Both have weight $\max(|T|,2)$, and $\sum p(a)a=\sum q(a)a$ is exactly
$2(b-a_0)=\sigma(T)$. Moreover $q\le1\le1+p$, because $a_0\notin T$ and $q(a_0)\le1$.
Lemma 1 gives $p=q$, but $p(b)=2\neq0=q(b)$. $\square$

This is the argument in Inal's proof of the equality case (his Theorem 4.1),
where it shows that $2(g_i-g_0)$ is not a nonempty subset sum.

**Theorem 3** (`IsValidMod.two_pow_add_le`). A valid $n$-set with $n\ge2$ has
$N\ge2^{n-1}+n-2$.

*Proof.* By Lemma 4, choose distinct $a_0,b_1\in A$ such that every pair
$x\ne y$ in $A$ with $2(x-y)=0$ is $\{a_0,b_1\}$: take the pair itself if
there is one, and any two elements otherwise. Let
$X_1=\{\sigma(S):S\subseteq B\}$ and
$X_2=\{2(b-a_0):b\in A\setminus\{a_0,b_1\}\}$.

- $|X_1|=2^{n-1}$ by Lemma 2.
- $|X_2|=n-2$: if $2(b-a_0)=2(b'-a_0)$, then $2(b-b')=0$, so $b=b'$ or
  $\{b,b'\}=\{a_0,b_1\}$. The second option is impossible here.
- $X_1\cap X_2=\emptyset$: Lemma 5 covers nonempty $T$. For $T=\emptyset$,
  $2(b-a_0)=0$ would make $\{b,a_0\}=\{a_0,b_1\}$, but $b\ne b_1$.

Hence $2^{n-1}+n-2\le N$. $\square$

For $n\ge4$ this improves on the cyclic consequence $N\ge2^{n-1}+1$ of Inal's
equality case. Both are far from the conjectured $2^n-2^{\lfloor\log_2n\rfloor}$.

## 5. Soundness of the exhaustive search

Both programs decide, for each $N$ in a range, whether a valid $n$-set mod
$N$ exists. They enumerate a restricted family of sets. The following facts
show that the family meets every affine orbit of valid sets.

**Invariance and heredity.** For a unit $u$ and any $v$, $A$ is valid iff
$uA+v$ is: when $\sum m=n$, $\sum m(a)(ua+v)=u\sum m(a)a+nv$, and $u$ is
invertible. Subsets of valid sets are valid: a rival on $B\subseteq A$,
extended by $1$ on $A\setminus B$, is a rival on $A$.

**Normal form.** Let $d=\min_{x\ne y\in A}\gcd(x-y,N)$, a divisor of $N$
with $d<N$, attained by a pair $(p,q)$. Since $(q-p)/d$ is a unit modulo $N/d$ and
$(\mathbb Z/N)^\times\to(\mathbb Z/(N/d))^\times$ is onto, some unit $u$ has
$u(q-p)=d$. Call $u(A-p)$ a *normalized image*; it contains $0$ and $d$.
Multiplying by a unit preserves $\gcd(\cdot,N)$, so every nonzero element $z$
of a normalized image has $z\ge\gcd(z,N)\ge d$. Among all normalized images
(over all such $p,q,u$) pick one whose third-smallest element $a_2$ is
least. In sorted order it reads $0<d<a_2<\dots$; all pairwise differences have
$\gcd\ge d$; and no normalized image has an element strictly between $d$ and
$a_2$.

The searches enumerate exactly the sorted sets with these three properties
(for every divisor $d<N$). They prune a prefix $P\supseteq\{0,d,a_2\}$ as soon as
one of its normalized images (built from a pair of $P$) has an element in
$(d,a_2)$. That image is contained in the corresponding image of every
completion, so pruning loses nothing. Every valid set therefore has at least
one enumerated representative. The leaves are tested for validity exactly,
so "found $=0$" for $N$ means that no valid $n$-set mod $N$ exists. Distinct
leaves can lie in one orbit; the reported orbit representatives are the
lexicographically least sorted images $u(A-a)$ over all $a\in A$ and units
$u$.

**Validity tests.**

- `mmsearch.cpp` extends a valid $k$-set $P$ with sum $s$ by $x$. Write
  $jP$ for the set of sums of $j$-element multisets from $P$ (with
  $0P=\{0\}$). Then $P\cup\{x\}$ is valid iff $x+s\notin(k+1)P$ and
  $s-gx\notin(k-g)P$ for $g=1,\dots,k$. Indeed, a rival has multiplicity
  $1+g$ at $x$ with $g\in\{-1,1,2,\dots,k\}$. (For $g=0$, validity of $P$ forces all ones.)
  Its restriction to $P$ is a multiset of size $k-g$ with sum $s-gx$, and
  conversely. The sumsets $jP$ are bitsets updated by cyclic shifts.
- `mmcheck.c` keeps, for the current set, the number of $j$-element multisets
  with each sum, capped at $2$. It declares an extension valid iff exactly
  one multiset of the full size has the target sum. That one is the all-ones
  multiset, which is always counted. This is the definition itself. A
  separate routine counts the last two added elements jointly.

The programs share no code. They traverse the family in opposite orders
after the third element, and `mmcheck.c` recomputes canonicity from scratch at
every node instead of maintaining the list of normalizing maps. `brute.py`
skips the reduction altogether: it tests every subset containing $0$.
`verify_search.py` compares all three on overlapping ranges, and re-checks in
Python the validity of every reported set.
