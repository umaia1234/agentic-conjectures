**English** | [한국어](DETAILS.ko.md)

# CRIM losing-hook stacks: proof details

Both conjectures are from Ina Bašić, Eric Gottlieb and Matjaž Krnc, *CRIM: A Natural Game on
Integer Partitions*, [arXiv:2606.16828](https://arxiv.org/abs/2606.16828).

Everything in Sections 2–7 is kernel-checked in
[`CrimHookStacks.lean`](../../AgenticConjectures/CrimHookStacks.lean) (no `sorry`, no extra
axioms, no `native_decide`). The text gives the same proofs on paper and names the Lean
declaration for each step. Sections 3–5 reduce conj:bloby to conj:main, and Section 7 proves
conj:main by formalizing Zijian Zeng's boundary-word classification. Section 8 describes the
computations, which are evidence only. No human has reviewed this work, and no novelty is
claimed.

## 1. The game, the stack, and the two conjectures

A position of Column–Row Impartial Merge (CRIM) is an integer partition
$\lambda=[\lambda_1,\dots,\lambda_r]$ with $\lambda_1\ge\dots\ge\lambda_r\ge1$, including the
empty partition $[\,]$. Write $\ell(\lambda)=r$ and $\lambda_i=0$ for $i>r$. A move deletes
one row or one column of the Young diagram and reattaches the pieces:

- deleting row $i$ removes the part $\lambda_i$;
- deleting column $j$ ($1\le j\le\lambda_1$) lowers every part $\ge j$ by one and discards
  the parts that become $0$.

Play is normal: $[\,]$ is a $\mathcal P$-position, and a position is $\mathcal P$ exactly
when every move leads to an $\mathcal N$-position. Every move lowers $|\lambda|+\ell(\lambda)$,
so the recursion is well founded.

The paper (arXiv:2606.16828v1) uses the following notions.

- **Rank** (§2.1): $\operatorname{rank}\lambda=|\ell(\lambda)-\lambda_1|$, Dyson's rank.
- **Hook**: $\Gamma_{r,c}=[c,1^{r-1}]$ for $r,c\ge1$. Rows $[c]$ ($r=1$) and columns $[1^r]$
  ($c=1$) are hooks.
- **Durfee length**: $d(\lambda)$ is the greatest $d$ with $d\le\lambda_d$.
- **Stack**: for $\mu=[\mu_1,\dots,\mu_k]$ and $d=d(\lambda)$, the stack $\lambda\lhd\mu$ is
  defined when $\lambda_{d+i}=d$ for $1\le i\le k$ and $\lambda_d\ge d+\mu_1$, and then
  $$\lambda\lhd\mu=[\lambda_1,\dots,\lambda_d,\lambda_{d+1}+\mu_1,\dots,\lambda_{d+k}+\mu_k,
  \lambda_{d+k+1},\dots,\lambda_r].$$

> **conj:main.** Every $\mathcal P$-position is of even rank.
>
> **conj:bloby.** Let $\lambda$ and $\Gamma_{r,c}$ be losing and suppose
> $\lambda^*=\Gamma_{r,c}\lhd\lambda$ is defined. Then $\lambda^*\in\mathcal P$.

### 1.1 Readings

| Point | Reading | Lean |
|---|---|---|
| positions | weakly decreasing lists of positive naturals | `IsPartition` |
| $\lambda_i$ | 1-indexed, $0$ past the end (`part l 0` is never used) | `part` |
| moves | `List.eraseIdx` for rows; `delCol l j`, $1\le j\le\lambda_1$, for columns | `moves` |
| losing | $\mathcal P$-position, normal play, $[\,]$ is $\mathcal P$ | `isP`, `IsP` |
| rank | $\lvert\ell(\lambda)-\lambda_1\rvert$ | `rank` |
| Durfee length | greatest $d\le\ell(\lambda)$ with $d\le\lambda_d$ (larger $d$ fail anyway) | `durfee` |
| stack | the paper's definition term for term; $\mu_1=0$ when $\mu=[\,]$ | `stack` |
| hooks | $r,c\ge1$; rows and columns included | `hook` |
| conj:main | every partition in $\mathcal P$ has even rank | `mainConjecture` |
| conj:bloby | for all partitions $\lambda$ and $r,c\ge1$ | `statement` |

Two boundary cases. $\lambda=[\,]$ is allowed and trivial: $\Gamma_{r,c}\lhd[\,]=\Gamma_{r,c}$.
For a row or a column the stack is defined only when $\lambda=[\,]$ (Proposition 3.1), and rows
and columns are never $\mathcal P$ (Lemma 2.2), so they add nothing.

## 2. Small classifications

**Lemma 2.1** (`not_isP_single`, `not_isP_replicate_one`, `two_le_of_isP`). Rows $[c]$ and
columns $[1^r]$ with $c,r\ge1$ are $\mathcal N$: deleting the row, or column 1, reaches
$[\,]$. Hence a nonempty $\mathcal P$-position has $\ell(\lambda)\ge2$ and $\lambda_1\ge2$.

**Lemma 2.2** (paper `lem:hook`; `isP_hook_iff`). For $r,c\ge1$, $\Gamma_{r,c}\in\mathcal P$ iff
$r,c\ge2$ and $r\equiv c\pmod 2$.

*Proof.* Induction on $r+c$. If $r=1$ or $c=1$ the hook is a row or a column. Let $r,c\ge2$.
The moves of $\Gamma_{r,c}$ reach the column $[1^{r-1}]$ (row 1), the row $[c-1]$ (column 1),
$\Gamma_{r-1,c}$ (a leg row) and $\Gamma_{r,c-1}$ (an arm column). The first two are nonempty,
hence $\mathcal N$. If $r\equiv c$, both $\Gamma_{r-1,c}$ and $\Gamma_{r,c-1}$ have the wrong
parity and are $\mathcal N$ by induction, so $\Gamma_{r,c}\in\mathcal P$. If $r\not\equiv c$,
then $\Gamma_{r-1,c}\in\mathcal P$ when $r\ge3$, and when $r=2$ the number $c\ge3$ is odd and
$\Gamma_{2,c-1}\in\mathcal P$. $\square$

**Lemma 2.3** (paper `thm:2parts`; `isP_pair_iff`). For $a\ge b\ge1$, $[a,b]\in\mathcal P$ iff
$a$ is even.

*Proof.* Induction on $a+b$. The moves reach $[a]$, $[b]$, $[a-1,b-1]$ (a column $j\le b$;
this is the row $[a-1]$ when $b=1$) and, if $a>b$, $[a-1,b]$ (a column $j>b$). If $a$ is even,
all of these are $\mathcal N$ (rows, or two parts with odd first part). If $a$ is odd: for
$a>b$ the move to $[a-1,b]$ wins; for $a=b$ the move to $[a-1,a-1]$ wins (it is $[\,]$ when
$a=1$). $\square$

**Lemma 2.4** (two columns; `isP_twoCol_iff`). For $a\ge1$ and $b\ge0$,
$[2^a,1^b]\in\mathcal P$ iff $a+b$ is even.

*Proof.* Induction on $a+b$ (this is the conjugate of Lemma 2.3, proved directly). The moves
reach $[2^{a-1},1^b]$, $[2^a,1^{b-1}]$ (if $b\ge1$), and the columns $[1^a]$, $[1^{a+b}]$. If
$a+b$ is even, all of these are $\mathcal N$ (by induction, or because $[2^{a-1},1^b]=[1^b]$
is a nonempty column when $a=1$). If $a+b$ is odd: for $b\ge1$, $[2^a,1^{b-1}]$ is
$\mathcal P$; for $b=0$ and $a\ge3$, $[2^{a-1}]$ is $\mathcal P$; and $[2]$ is a row. $\square$

**Lemma 2.5** (`rank_even_iff`). $\operatorname{rank}\lambda$ is even iff
$\ell(\lambda)\equiv\lambda_1\pmod2$.

## 3. The hook-stack reduction

For $r\ge1$, $c\ge1$ and $k=\ell(\mu)$ put
$$H(r,c,\mu)=[c,\,1+\mu_1,\,\dots,\,1+\mu_k,\,1^{r-1-k}]$$
(Lean: `hookStack r c μ = c :: (pad μ (r - 1)).map (· + 1)`, where `pad` appends zeros).

**Proposition 3.1** (`stack_hook`). Let $c\ge1$. The stack $\Gamma_{r,c}\lhd\mu$ is defined iff
$\ell(\mu)\le r-1$ and $\mu_1\le c-1$, and then $\Gamma_{r,c}\lhd\mu=H(r,c,\mu)$.

*Proof.* For $\lambda=\Gamma_{r,c}$ we have $\lambda_1=c\ge1$ and $\lambda_2\le1$, so
$d(\lambda)=1$ (`durfee_hook`). The first condition reads $\lambda_{1+i}=1$ for
$1\le i\le k$; since $\lambda_{1+i}=1$ exactly for $i\le r-1$, it says $k\le r-1$. The second
reads $c\ge1+\mu_1$. The formula is then $[c,1+\mu_1,\dots,1+\mu_k,\lambda_{k+2},\dots,
\lambda_r]=H(r,c,\mu)$. $\square$

For a row ($r=1$) the conditions force $k=0$, and for a column ($c=1$) they force $\mu_1=0$;
in both cases $\mu=[\,]$. Also $H(r,c,[\,])=\Gamma_{r,c}$ (`hookStack_nil`).

## 4. The moves of a hook stack

Let $k=\ell(\mu)\le r-1$, $\mu_1\le c-1$, $c\ge2$, and $X=H(r,c,\mu)$. Call rows
$2,\dots,k+1$ of $X$ *inner rows* and rows $k+2,\dots,r$ *leg rows*; call columns
$j+1$ with $1\le j\le\mu_1$ *inner columns* and columns $j+1$ with $\mu_1<j<c$ *arm columns*.
Write $\mu\setminus i$ for $\mu$ without its $i$-th part and $\mu-j$ for $\mu$ with column $j$
deleted.

**Lemma 4.1** (`mem_moves_hookStack`; the pieces are `eraseIdx_hookStack_zero`,
`eraseIdx_hookStack_succ`, `delCol_hookStack_one`, `delCol_hookStack_succ`,
`delCol_eq_self`). Every move of $X$ is one of:

| | move | result |
|---|---|---|
| R1 | row 1 | $[1+\mu_1,\dots,1+\mu_k,1^{r-1-k}]$; deleting its column 1 gives $\mu$ |
| Rin | inner row $i+1$, $1\le i\le k$ | $H(r-1,c,\mu\setminus i)$ |
| Rleg | a leg row | $H(r-1,c,\mu)$ |
| C1 | column 1 | $[c-1,\mu_1,\dots,\mu_k]$; deleting its row 1 gives $\mu$ |
| Cin | inner column $j+1$, $1\le j\le\mu_1$ | $H(r,c-1,\mu-j)$ |
| Carm | an arm column | $H(r,c-1,\mu)$ |

Conversely (`hookStack_eraseIdx_mem_moves`, `hookStack_delCol_mem_moves`), for
$1\le i\le r-1$ deleting row $i+1$ of $H(r,c,\nu)$ reaches $H(r-1,c,\nu\setminus i)$, and for
$1\le j\le c-1$ deleting column $j+1$ reaches $H(r,c-1,\nu-j)$, where $\nu\setminus i=\nu$ for
$i>\ell(\nu)$ and $\nu-j=\nu$ for $j>\nu_1$. These are the replies used below.

## 5. The main theorem

**Definition 5.1** (`PChain`, `LocalEvenRank`). $\omega$ is *P-chain reachable* from $\mu$ if
$\omega=\mu$, or there are moves $\mu\to\nu\to\nu'$ with $\nu'\in\mathcal P$ and $\omega$ is
P-chain reachable from $\nu'$. $\mu$ satisfies $\mathrm{LER}(\mu)$ if every partition that is
P-chain reachable from $\mu$ (including $\mu$) has even rank.

**Theorem 5.2** (`isP_hookStack`, by `isP_hookStack_aux`). Let $\mu\in\mathcal P$ satisfy
$\mathrm{LER}(\mu)$, and let $r,c\ge2$ with $r\equiv c\pmod2$, $\ell(\mu)\le r-1$ and
$\mu_1\le c-1$. Then $H(r,c,\mu)\in\mathcal P$.

*Proof.* Strong induction on $r+c$, for all $\mu$ at once. If $\mu=[\,]$ then
$H(r,c,\mu)=\Gamma_{r,c}\in\mathcal P$ by Lemma 2.2. Otherwise $k=\ell(\mu)\ge2$ and
$\mu_1\ge2$ (Lemma 2.1), and $k\equiv\mu_1\pmod2$ by $\mathrm{LER}(\mu)$ and Lemma 2.5. We
answer every move from $X=H(r,c,\mu)$ with a move onto a $\mathcal P$-position, following the
cases of Lemma 4.1. Each appeal to the induction hypothesis below lowers $r+c$ by $2$; its side
conditions ($r',c'\ge2$, $r'\equiv c'$, $\ell\le r'-1$, first part $\le c'-1$) follow from
$k\le r-1$, $\mu_1\le c-1$, $k,\mu_1\ge2$, $\ell(\nu')\le\ell(\nu)$ and
$\nu'_1\le\nu_1\le\mu_1$, with $\nu'_1+1\le\nu_1$ after a column deletion
(`part_one_delCol_lt`).

- **R1.** Reply: column 1. This reaches $\mu\in\mathcal P$.
- **C1.** Reply: row 1. This reaches $\mu\in\mathcal P$.
- **Rin.** The position is $Y=H(r-1,c,\nu)$ with $\nu=\mu\setminus i$, a move of $\mu$, so
  $\nu\in\mathcal N$.
  - $r=3$. Then $k=2$ and $\nu=[a]$ with $1\le a\le\mu_1\le c-1$, so $Y=[c,1+a]$. Reply:
    column 1, reaching $[c-1,a]$. Since $c\equiv r$ is odd, $c-1$ is even, and
    $[c-1,a]\in\mathcal P$ by Lemma 2.3.
  - $r\ge4$. Pick a move $\nu\to\nu'$ with $\nu'\in\mathcal P$; then $\mathrm{LER}(\nu')$
    holds, because $\nu'$ is P-chain reachable from $\mu$. If $\nu'=\nu\setminus i'$, reply
    with the matching row of $Y$, reaching $H(r-2,c,\nu')$. If $\nu'=\nu-j'$, reply with
    column $j'+1$ of $Y$, reaching $H(r-1,c-1,\nu')$. Both are $\mathcal P$ by induction.
- **Rleg.** The position is $Y=H(r-1,c,\mu)$, and $r\ge k+2$.
  - $r\ge k+3$. Reply: another leg row, reaching $H(r-2,c,\mu)$.
  - $r=k+2$ and $c\ge\mu_1+2$. Reply: the last column $c$ (an arm column of $Y$), reaching
    $H(r-1,c-1,\mu)$.
  - $r=k+2$ and $c=\mu_1+1$. Then $r\equiv c$ gives $k\not\equiv\mu_1$, so $\mu$ has odd
    rank. This contradicts $\mathrm{LER}(\mu)$, so the case does not occur.
- **Cin.** The position is $Y=H(r,c-1,\nu)$ with $\nu=\mu-j$, so $\nu\in\mathcal N$.
  - $c=3$. Then $\mu_1=2$, so $\nu_1=1$ (`part_one_delCol_eq`) and $\nu=[1^a]$ with
    $1\le a\le k\le r-1$. Reply: row 1, reaching $[2^a,1^{r-1-a}]$. Since $r\equiv c$ is odd,
    $a+(r-1-a)=r-1$ is even, and this is $\mathcal P$ by Lemma 2.4.
  - $c\ge4$. Pick $\nu\to\nu'\in\mathcal P$, so $\mathrm{LER}(\nu')$ holds. If $\nu'=\nu-j'$,
    reply with column $j'+1$, reaching $H(r,c-2,\nu')$. If $\nu'=\nu\setminus i'$, reply with
    the matching row, reaching $H(r-1,c-1,\nu')$. Both are $\mathcal P$ by induction.
- **Carm.** The position is $Y=H(r,c-1,\mu)$, and $c\ge\mu_1+2$.
  - $c\ge\mu_1+3$. Reply: another arm column, reaching $H(r,c-2,\mu)$.
  - $c=\mu_1+2$ and $r\ge k+2$. Reply: a leg row, reaching $H(r-1,c-1,\mu)$.
  - $c=\mu_1+2$ and $r=k+1$. Then $r\equiv c$ gives $k\not\equiv\mu_1$, an odd rank, which
    contradicts $\mathrm{LER}(\mu)$.

Every move has been answered by a move onto a $\mathcal P$-position, so
$X\in\mathcal P$. $\square$

The two corner cases are the only places where the parity of $\operatorname{rank}\mu$ itself
enters. The special replies for $r=3$ and $c=3$ are needed because there $H(r-2,c,\nu')$ or
$H(r,c-2,\nu')$ would have only one row or one column.

**Corollary 5.3** (`isP_stack_of_localEvenRank`). If $\lambda\in\mathcal P$ satisfies
$\mathrm{LER}(\lambda)$, $r,c\ge1$, $\Gamma_{r,c}\in\mathcal P$ and $\Gamma_{r,c}\lhd\lambda$ is
defined, then $\Gamma_{r,c}\lhd\lambda\in\mathcal P$. (Lemma 2.2, Proposition 3.1 and
Theorem 5.2.)

**Corollary 5.4** (`statement_of_mainConjecture`). conj:main implies conj:bloby. Every
partition P-chain reachable from a $\mathcal P$-position is a $\mathcal P$-position
(`PChain.isP`, `PChain.isPartition`), so conj:main gives $\mathrm{LER}$ for every
$\mathcal P$-position (`localEvenRank_of_mainConjecture`).

## 6. How much of conj:main is needed

Section 7 proves conj:main, so conj:bloby no longer depends on this section. It records how
little of conj:main the reduction uses. Corollary 5.3 needs conj:main only along P-chains from
$\lambda$. No move increases the size
$|\lambda|$, the number of rows $\ell(\lambda)$, or the largest part $\lambda_1$, so neither
does a P-chain (`PChain.le_of_moves`). This gives three consequences.

1. **Size-bounded form** (`statement_of_mainConjecture_le`). If every $\mathcal P$-position of
   size at most $N$ has even rank, then conj:bloby holds for every $\lambda$ with
   $|\lambda|\le N$ and every hook, of any size. The computation of Section 8 checks
   conj:main for all partitions of size at most $110$, so conj:bloby holds for all
   $|\lambda|\le110$ and all hooks $\Gamma_{r,c}$. This is an infinite family, but its
   finite input is a computation, not a Lean proof.
2. **Two rows or two columns, unconditionally** (`statement_of_length_le_two`,
   `statement_of_part_one_le_two`). A $\mathcal P$-position with $\ell\le2$ is $[\,]$ or
   $[a,b]$ with $a$ even (Lemmas 2.1, 2.3), so its rank $|2-a|$ is even
   (`even_rank_of_length_le_two`). A $\mathcal P$-position with $\lambda_1\le2$ is $[\,]$ or
   $[2^a,1^b]$ with $a\ge1$ and $a+b$ even (Lemmas 2.1, 2.4), of rank $|a+b-2|$
   (`even_rank_of_part_one_le_two`). These classes are closed under P-chains, so conj:bloby
   holds for every $\lambda$ with $\ell(\lambda)\le2$ or $\lambda_1\le2$, under every hook.
3. **Other move-closed classes.** The same argument applies to any class of partitions closed
   under moves on which $\mathcal P$-positions have even rank. Mehat's artifact (Zenodo
   [10.5281/zenodo.22070744](https://doi.org/10.5281/zenodo.22070744)) classifies the
   $\mathcal P$-positions with at most six parts and, by conjugation, with largest part at most
   six, and states that they all have even rank. With Corollary 5.3 this would give
   conj:bloby whenever $\ell(\lambda)\le6$ or $\lambda_1\le6$. We have not re-verified that
   artifact, so this is a consequence of its claims, not a result of this directory.

## 7. conj:main from the boundary-word classification

Zijian Zeng's preprint (see Section 9) states a classification of all $\mathcal P$-positions
and derives conj:main from it. This section is a Lean formalization of that classification.
The argument is Zeng's: the run-pair encoding, the statistic $M$, the even-followers lemma and
the case analysis of the odd-word domination lemma. The Lean proofs and the arrangement of the
cases are ours. Using the duality $\delta$ below, we prove one case of each mirror pair and get
the other for free. The helper lemmas of this section are in the Lean namespace `RunPairs`.

**Run pairs.** Let $\lambda\ne[\,]$ have distinct parts $v_1>\dots>v_k>0$, where $v_i$ occurs
$a_i$ times, and put $b_i=v_i-v_{i+1}$ with $v_{k+1}=0$. The *run pairs* of $\lambda$ are
$(a_1,b_1),\dots,(a_k,b_k)$; all entries are positive (`ValidPairs`). Walking the boundary of
the Young diagram from the top right corner to the bottom left corner, with $0$ for a step down
and $1$ for a step left, gives the boundary word $0^{a_1}1^{b_1}\cdots0^{a_k}1^{b_k}$.
Conversely, `ofPairs p` is the partition in which $b_i+\dots+b_k$ occurs $a_i$ times. For valid
$p$ it is a partition (`isPartition_ofPairs`), every partition is `ofPairs p` for some valid $p$
(`exists_ofPairs`), and the word length is $\sum_i(a_i+b_i)=\ell(\lambda)+\lambda_1$ (`plen`,
`length_add_part_one_ofPairs`).

**Lemma 7.1** (`mem_moves_ofPairs`). The CRIM moves of `ofPairs p` are exactly the partitions
`ofPairs q` with `PMove p q`, where `PMove` has the following six cases.

| `PMove` | pairs | CRIM move |
|---|---|---|
| `zeroDec` | $a_i\mapsto a_i-1$, if $a_i\ge2$ | delete a row whose length occurs at least twice |
| `zeroFirst` | delete $(1,b_1)$ | delete the only row of length $v_1$ |
| `zeroMerge` | $(a_{i-1},b_{i-1}),(1,b_i)\mapsto(a_{i-1},b_{i-1}+b_i)$ | delete the only row of length $v_i$, $i\ge2$ |
| `oneDec` | $b_i\mapsto b_i-1$, if $b_i\ge2$ | delete a column $j$ with $v_{i+1}<j\le v_i$ |
| `oneLast` | delete $(a_k,1)$ | delete column 1 when $v_k=1$ |
| `oneMerge` | $(a_i,1),(a_{i+1},b_{i+1})\mapsto(a_i+a_{i+1},b_{i+1})$ | delete column $v_i$ when $v_i=v_{i+1}+1$ |

In the word, each case deletes one letter and then strips leading 1s and trailing 0s. Every
case lowers `plen` (`PMove.plen_lt`) and keeps the pairs valid (`PMove.validPairs`). Together
with `isP_iff` this gives `isP_ofPairs_iff_forall`: `ofPairs p` is a $\mathcal P$-position iff
no `PMove` from $p$ reaches a $q$ with `ofPairs q` a $\mathcal P$-position.

**The statistic $M$.** A pair $(a,b)$ is *A-good* if $a=1$ and $b$ is odd, and *B-good* if $a$
is odd and $b=1$; either way $a+b$ is even. Let $L$ (`endL`) be the length of the longest
prefix of A-good pairs, $R$ (`endR`) the length of the longest suffix of B-good pairs, and
$M=\min(k,L+R)$ (`endM`). For example, $[4,2,2,2]$ has pairs $(1,2),(3,2)$, word length $8$
and $M=0$, while $[3,2,1]$ has pairs $(1,1),(1,1),(1,1)$ and $M=3$. The duality $\delta$
(`pdual`) reverses the list and swaps each pair; on partitions it is conjugation, but the proof
does not use that. It maps moves to moves (`PMove.pdual`), exchanges $L$ and $R$, and preserves
the length and $M$ (`plen_pdual`, `endM_pdual`).

**Lemma 7.2** (even followers; `endM_eq_of_even`). If `plen p` and `plen q` are even and
`PMove p q`, then `endM p = endM q + 1`.

*Proof.* A move removes one letter, except `zeroFirst`, which removes $1+b_1$ letters, and
`oneLast`, which removes $a_k+1$. So the length stays even only for `zeroFirst` on an A-good
first pair and `oneLast` on a B-good last pair. Removing an A-good first pair, or a B-good last
pair, lowers $M$ by exactly one (`endM_cons_aGood`, `endM_append_bGood`). $\square$

**Lemma 7.3** (`goodMove_of_even`). If `plen p` is even and `endM p` is odd, some move reaches
a $q$ with `plen q` and `endM q` both even.

*Proof.* $M\ge1$, so $L\ge1$ or $R\ge1$. Remove that end pair. The length stays even, and by
Lemma 7.2 the new $M$ is even. By duality it suffices to treat $L\ge1$
(`goodMove_of_endL`). $\square$

**Lemma 7.4** (odd-word domination; `goodMove_of_odd`). If $p$ is valid and `plen p` is odd,
some move reaches a $q$ with `plen q` and `endM q` both even.

*Proof.* Good pairs have even length, so if every pair lay in the A-good prefix or in the
B-good suffix, `plen p` would be even. Hence $p=P\,C\,S$, where the pairs of $P$ are A-good,
the pairs of $S$ are B-good, and the core $C$ is nonempty, starts with a pair that is not
A-good and ends with a pair that is not B-good (`exists_split`, `Split`). Then $L=|P|$,
$R=|S|$ and $M=L+R$ (`Split.endM_eq`). Each move chosen below deletes one letter, or deletes
a pair $(1,b)$ with $b$ even, so the new length is even; it remains to make the new $M$ even.
Mirror cases follow by $\delta$ (`Split.pdual`, `GoodMove.of_pdual`).

*Case $L+R$ odd.*

- *Reduce A* (`goodMove_reduceA`), when $P\ne[\,]$ and $C$ is not a single pair $(a,1)$ with
  $a$ even. Delete a 1 from the last pair $(1,b')$ of $P$. If $b'\ge3$, the new pair
  $(1,b'-1)$ is neither A-good nor B-good and joins the core. If $b'=1$, deleting its 1 merges
  $(1,1)$ with the first core pair $(a,b)$ into $(1+a,b)$, which is not A-good. If $(1+a,b)$
  is the whole new core, it is not B-good either, because $b=1$ would force $a$ to be odd.
  Either way the new $M$ is $L+R-1$.
- *Reduce B*, when $S\ne[\,]$ and $C$ is not a single pair $(1,b)$ with $b$ even: the mirror
  image.
- Otherwise, since $P$ and $S$ are not both empty, either $P=[\,]$ and $C=[(1,b)]$ with $b$
  even, or the mirror image of this. Delete a 1 from $(1,b)$. The list becomes $(1,b-1)\,S$,
  in which every pair is good, so the new $M$ is $1+R=L+R+1$
  (`goodMove_core_one_odd`).

*Case $L+R$ even, core of one pair $(a,b)$.* The pair is neither A-good nor B-good, and $a+b$
is odd.

- $a=1$ and $b$ even (`goodMove_core_one_even`): delete its 0. If $P=[\,]$, this removes the
  pair and leaves $S$, with $M=R$. Otherwise it merges $(1,b)$ into the last pair $(1,b')$ of
  $P$, which gives the A-good pair $(1,b'+b)$, and the new $M$ is $L+R$.
- $a\ge3$ odd and $b$ even (`goodMove_core_odd_even`): delete a 0. The new core $(a-1,b)$ is
  neither A-good nor B-good, so $M=L+R$.
- $a$ even and $b$ odd: the mirror images of the two cases above.

*Case $L+R$ even, core of at least two pairs* (`goodMove_core_long`). Let $(a,b)$ be the first
core pair and $C_1$ the rest of the core.

- If $a\ge3$, or $a=2$ and $b$ is even, delete a 0. If $a=2$ and $b\ge3$ is odd, delete a 1.
  If $(a,b)=(2,1)$, delete its 1, which merges it with the next core pair $(a',b')$ into
  $(2+a',b')$. The new first core pair is not A-good, and the last core pair is still not
  B-good ($(2+a',b')$ is B-good only if $(a',b')$ is), so $M=L+R$.
- If $a=1$, then $b$ is even. Compare two moves: delete the 0 of $(1,b)$ (as in the one-pair
  case), or delete a 1, which makes it the A-good pair $(1,b-1)$. Both moves leave an A-good
  block followed by $C_1S$, and the second block has one more pair. Since $C_1$ ends with a pair
  that is not B-good, the two values of $M$ differ by exactly one (`endM_prefix_barrier`), so
  one of them is even. $\square$

**Theorem 7.5** (`pairs_classification`). Let $G$ be a predicate on pair lists such that, for
every valid $p$, $G(p)$ holds iff $G(q)$ fails for every $q$ with `PMove p q`. Then for every
valid $p$,
$$G(p)\iff \texttt{plen }p\text{ and }\texttt{endM }p\text{ are both even}.$$

*Proof.* Strong induction on `plen p`. If both are even, every move reaches odd length or, by
Lemma 7.2, even length with odd $M$, so by induction no move reaches a position satisfying
$G$. If the length is even and $M$ is odd, Lemma 7.3 gives a move to a position satisfying $G$;
if the length is odd, Lemma 7.4 does. $\square$

**Corollary 7.6** (`isP_ofPairs_iff`). For valid $p$, `ofPairs p` is a $\mathcal P$-position iff
$\ell+\lambda_1$ and $M$ are both even. (Theorem 7.5 with $G(p)=$ `IsP (ofPairs p)`, using
`isP_ofPairs_iff_forall`.)

**Corollary 7.7** (`mainConjecture_holds`). conj:main holds. A $\mathcal P$-position
$\lambda=$ `ofPairs p` has $\ell(\lambda)+\lambda_1$ even, so its rank is even (Lemma 2.5).

**Corollary 7.8** (`statement_holds`). conj:bloby holds (Corollaries 5.4 and 7.7).

## 8. Computations

All programs are in [`programs/`](programs/) and use only the Python standard library or C99.
They are evidence for the statements above; none is used by the Lean proofs.

- [`crim_check.py`](programs/crim_check.py) computes $\mathcal P/\mathcal N$ for all partitions
  with $|\lambda|\le N$ by trying every row and column move, checks conj:main, and checks
  conj:bloby for every pair ($\mu\in\mathcal P$, $\Gamma_{r,c}\in\mathcal P$) with stack size
  $\le N$. It evaluates the stack with the paper's general definition (Durfee length,
  conditions, formula) and checks that it agrees with Proposition 3.1.
  [`logs/crim_check_py_n60.log`](logs/crim_check_py_n60.log): $N=60$, 6,639,349 partitions,
  1,870,422 $\mathcal P$-positions, 0 of odd rank. Of the 23,194,397 pairs evaluated, 964,855
  stacks are defined, and all are $\mathcal P$.
- [`crim_check.c`](programs/crim_check.c) is an independent implementation. It indexes
  partitions by lexicographic rank, keeps one bit per position, and tries one move per
  distinct result. It checks conj:bloby through the bijection between nonempty $X$ and triples
  $(r,c,\mu)$ with $X=H(r,c,\mu)$. [`logs/crim_check_c_n110.log`](logs/crim_check_c_n110.log):
  $N=110$, 5,465,153,652 partitions, 1,534,701,211 $\mathcal P$-positions, 0 of odd rank,
  783,733,098 defined stacks of two $\mathcal P$-positions, all $\mathcal P$; 333 s. Its
  per-size counts agree with the Python program for every $n\le60$.
- [`strategy_check.py`](programs/strategy_check.py) replays the proof of Theorem 5.2. For every
  stack $X=H(r,c,\mu)$ with $\mu\ne[\,]$ and $|X|\le N$, every move from $X$, and every
  $\mathcal P$-child $\nu'$ in cases Rin and Cin, it plays the prescribed reply and checks that
  the reply is legal, has the stated shape, and reaches a $\mathcal P$-position. The impossible
  cases must never occur. It also checks Lemma 2.2 for all hooks of size $\le N$.
  [`logs/strategy_check_n60.log`](logs/strategy_check_n60.log): $N=60$, 964,014 stacks,
  150,828,030 replies, 0 failures. The case counts are symmetric under transposition, as
  expected (for example, 2,700 replies each in the special cases $r=3$ and $c=3$).
- [`boundary_word_check.py`](programs/boundary_word_check.py) compares the exact
  $\mathcal P/\mathcal N$ table of `crim_check.py` with Zeng's boundary-word rule (Section 7).
  [`logs/boundary_word_check_n60.log`](logs/boundary_word_check_n60.log): $N=60$, all
  6,639,349 partitions, 0 mismatches.

For $|\lambda|\le50$ the programs give 1,295,971 partitions and 365,327 $\mathcal P$-positions;
the paper reports conj:main checked to the same size.

## 9. Related work and an erratum

- **The paper** (Bašić, Gottlieb, Krnc) proves `lem:hook`, `thm:2parts` and `thm:3parts`,
  checks conj:main for $|\lambda|\le50$ and several families, and notes that conj:bloby implies
  its `prop:hooksquare`. The second-player strategy of Section 5 was sketched in an earlier
  scouting run of this project; Sections 4–5 make it complete and machine-checked. We claim no
  novelty.
- **Erratum in `thm:3parts`.** As stated, it says $[\lambda_1,\lambda_2,\lambda_3]\in\mathcal P$
  iff $\lambda_1,\lambda_2$ are odd and either $\lambda$ is a hook or $\lambda_3>1$. This
  includes $[1,1,1]=\Gamma_{3,1}$, which is a column and therefore $\mathcal N$ (`lem:hook`
  needs $c>1$). Nothing here depends on `thm:3parts`.
- **Mehat** (Zenodo [10.5281/zenodo.22070744](https://doi.org/10.5281/zenodo.22070744),
  2026-08-23; Lean files CC0, scripts MIT): certified classification for at most six parts or
  largest part at most six; see Section 6. No code from it is used here.
- **the-omega-institute/trureturing** has Lean certificates refuting two other conjectures of
  the same paper (`CrimRectairSquareBoundaryRefutation`, `CrimGrundyRefutation`); it has
  nothing on conj:main or conj:bloby.
- **Zeng.** Zijian Zeng, *A Boundary-Word Classification of Losing Positions in CRIM* (dated
  2026-08-29; unrefereed; GitHub `ArtificialZeng/AI-Has-Taste`, folder
  `reproducible_source_code/BigWIN2/BW2-B02-P10`), claims a complete classification: encode
  $\lambda$ by its boundary word $0^{a_1}1^{b_1}\cdots0^{a_k}1^{b_k}$ ($a_i$ the multiplicity
  of the $i$-th largest distinct part, $b_i$ the gap to the next one), let $L$ be the length of
  the longest prefix of pairs with $a_i=1$ and $b_i$ odd, $R$ the length of the longest suffix
  of pairs with $a_i$ odd and $b_i=1$, and $M=\min(k,L+R)$. Then $\lambda\in\mathcal P$ iff
  $\ell(\lambda)+\lambda_1$ and $M$ are both even. Zeng derives conj:main from it; the
  preprint does not mention conj:bloby. Section 7 formalizes Zeng's proof, which gives
  conj:main in Lean and, with Corollary 5.4, conj:bloby. We also compared the classification
  with the exact $\mathcal P/\mathcal N$ table for all 6,639,349 partitions of size at most 60
  and found no mismatch (`boundary_word_check.py`).
