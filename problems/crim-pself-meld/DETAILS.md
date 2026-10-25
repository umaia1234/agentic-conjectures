**English** | [한국어](DETAILS.ko.md)

# CRIM melds, parity self-conjugate partitions and misère play: proof details

The conjectures treated here are from Ina Bašić, Eric Gottlieb and Matjaž Krnc, *CRIM: A
Natural Game on Integer Partitions*, [arXiv:2606.16828](https://arxiv.org/abs/2606.16828),
Section 5.

Every theorem in Sections 3 to 5 is kernel-checked in
[`CrimPselfMeld.lean`](../../AgenticConjectures/CrimPselfMeld.lean) (no `sorry`, no extra
axioms, no `native_decide`). The text gives the same proofs on paper and names the Lean
declaration for each step. Both proofs rest on Zijian Zeng's boundary-word classification of
the $\mathcal P$-positions (an unrefereed preprint; Section 2), which
[crim-hook-stacks](../crim-hook-stacks/DETAILS.md#7-conjmain-from-the-boundary-word-classification)
formalizes. Section 5 proves a classification of the misère $\mathcal P$-positions and one
direction of the paper's conj:hookswap, whose other direction is not proved. Section 6
describes the computations, which are evidence only. No human has reviewed this
work, no novelty is claimed, and nothing has been submitted.

## 1. Definitions and statements

A position of CRIM is an integer partition $\lambda=[\lambda_1,\dots,\lambda_r]$ with
$\lambda_1\ge\dots\ge\lambda_r\ge1$, including $[\,]$. Write $\ell(\lambda)=r$ and
$\lambda_i=0$ for $i>r$. A move deletes one row or one column of the Young diagram and
reattaches the pieces. Play is normal, so $[\,]$ is a $\mathcal P$-position ("losing"), and a
position is $\mathcal P$ exactly when every move leads to an $\mathcal N$-position. The Lean
definitions (`IsPartition`, `part`, `moves`, `IsP`) are those of crim-hook-stacks
([its §1.1](../crim-hook-stacks/DETAILS.md#11-readings)).

The paper uses the following notions.

- **Meld** (§2.1, TeX line 334): for $\mu=[\mu_1,\dots,\mu_k]$ and
  $\lambda=[\lambda_1,\dots,\lambda_m]$,
  \[
  \mu\diamond\lambda=[\mu_1+\lambda_1,\dots,\mu_1+\lambda_m,\mu_1,\mu_2,\dots,\mu_k].
  \]
  The paper observes that $\diamond$ is associative with unit $[\,]$.
- **Thick hook** (§2.2, lines 356–357): $\Gamma^{a,b}_{r,c}=[c^a,b^{r-a}]$, where $r>a\ge2$ and
  $c>b\ge2$.
- **Hook**: $\Gamma_{r,c}=[c,1^{r-1}]$. Its conjugate is $\Gamma_{c,r}$.
- **Conjugate**: $\lambda'_k$ is the number of parts $\ge k$.
- **Parity self-conjugate** (line 1141): $\lambda_k\equiv\lambda'_k\pmod 2$ for every $k$.
- **Durfee length and stack** (lines 1095–1105): $d(\lambda)$ is the greatest $d$ with
  $d\le\lambda_d$. For $\mu=[\mu_1,\dots,\mu_k]$ and $d=d(\lambda)$, the stack $\lambda\lhd\mu$
  is defined when $\lambda_{d+i}=d$ for $1\le i\le k$ and $\lambda_d\ge d+\mu_1$, and then
  \[
  \lambda\lhd\mu=[\lambda_1,\dots,\lambda_d,\lambda_{d+1}+\mu_1,\dots,\lambda_{d+k}+\mu_k,
  \lambda_{d+k+1},\dots,\lambda_r].
  \]
  The paper adds that the stack operation "is associative and can be extended to multiple
  partitions".
- **Misère Grundy value and Conway pair** (§2, lines 422–424): $G^-$ is defined like the
  Sprague–Grundy value $\mathrm{sg}$, except that terminal positions have value $1$, and
  $\mathrm{cp}(\lambda)=(\mathrm{sg}(\lambda),G^-(\lambda))$.

The conjectures (lines 1071–1073 and 1143–1146):

> A meld of losing thick hooks is losing.
>
> **conj:pself.** A parity self-conjugate partition is in $\mathcal N$ if and only if it is the
> stack of odd self-conjugate hooks and $[1]$.

### 1.1 Readings

| Point | Reading | Lean |
|---|---|---|
| positions, moves, losing | as in crim-hook-stacks; normal play, $[\,]$ is $\mathcal P$ | `IsPartition`, `moves`, `IsP` |
| meld | the paper's formula; $\mu_1=0$ when $\mu=[\,]$ | `meld` |
| thick hook | $[c^a,b^{r-a}]$ with $r>a\ge2$ and $c>b\ge2$ | `thickHook`, `ThickParams`, `IsThickHook` |
| a meld of losing thick hooks | any finite meld, in any bracketing, of thick hooks in $\mathcal P$; one piece and the empty meld $[\,]$ included | `Melds`, `melds_iff` |
| meld conjecture | every such meld is in $\mathcal P$ | `meldConjecture` |
| $\lambda'_k$ | the number of parts $\ge k$ | `conjPart` |
| parity self-conjugate | $\lambda_k\equiv\lambda'_k\pmod2$ for every $k\ge1$, both sides $0$ past the end | `ParitySelfConj` |
| odd self-conjugate hook | $\Gamma_{r,r}$ with $r$ odd | `hook r r`, `Odd r` |
| the stack of odd self-conjugate hooks and $[1]$ | $\Gamma_{r_1,r_1}\lhd(\Gamma_{r_2,r_2}\lhd(\cdots\lhd(\Gamma_{r_j,r_j}\lhd[1])))$, $j\ge0$, $r_i$ odd, every stack defined; any bracketing gives the same | `OddHookStack`; `HookTree`, `exists_hookTree_iff` |
| stack | the paper's general Durfee-length definition | `stack` (crim-hook-stacks) |
| conj:pself | for every parity self-conjugate partition $\lambda$: $\lambda\in\mathcal N$ iff $\lambda$ is such a stack | `pselfConjecture` |
| misère play | the player to move at $[\,]$ wins, so $[\,]$ is a misère $\mathcal N$-position | `IsMP`, `isMP_iff` |
| Conway pair $(0,1)$ | $\lambda\in\mathcal P$ and $G^-(\lambda)=1$, where $G^-$ is $1$ at $[\,]$ and otherwise the mex of the options' values | `IsP`, `IsMV1`, `isMV1_iff` |
| even-by-even hook | $\Gamma_{r,c}$ with $r,c\ge2$ even | `EEHook` |
| conj:hookswap | for every nonempty partition $\lambda$: $\mathrm{cp}(\lambda)=(0,1)$ iff $\lambda$ is an even-by-even hook | `hookswapConjecture` (not proved) |

The points that needed a decision:

- **The empty meld.** $[\,]$ is the meld of no thick hooks. It is $\mathcal P$, so including it
  in `Melds` changes nothing.
- **Bracketing of melds.** `Melds S` is the closure under the binary meld, so it contains every
  bracketing. `melds_iff` shows that it equals the set of right-nested melds
  $H_1\diamond(H_2\diamond(\cdots\diamond H_n))$ (`meldAll`), using `meld_assoc`.
- **"For every $k$".** Read as every $k\ge1$, with $\lambda_k=\lambda'_k=0$ for large $k$. The
  weaker reading that compares only $k\le\min(\ell(\lambda),\lambda_1)$ makes conj:pself false
  already at $[3]$, which is $\mathcal N$ and not a stack.
- **"Odd self-conjugate hooks".** The self-conjugate hooks are the $\Gamma_{r,r}$, and they all
  have odd size $2r-1$, so "odd" must refer to $r$. The paper's Observation (lines 1123–1134)
  calls $\Gamma_{2m+1,2m'+1}$ "odd hooks".
- **Order and nesting.** By the paper's own definition, $\lambda\lhd\mu$ and $\mu\lhd\lambda$
  are never both defined, and its Observation writes "a stack of odd hooks, with last hook
  being $[1]$". So $[1]$ comes last. `OddHookStack` nests to the right and requires every
  intermediate stack to be defined. The paper asserts associativity, and Corollary 4.11 proves
  the part needed here: every bracketing, with every intermediate stack defined, gives the same
  partitions as right nesting, so conj:pself holds in every bracketing
  (`pselfConjecture_anyBracketing`). The computation of Section 6 agrees for $n\le50$.
- **One piece.** $j=0$ is allowed, so $[1]$ itself is a stack. It is parity self-conjugate and
  in $\mathcal N$, so excluding it would make the conjecture false.
- **conj:hookswap at $[\,]$.** The paper's own $\mathrm{cp}([\,])=(0,1)$ makes the literal
  statement false at $[\,]$, so `hookswapConjecture` requires $\lambda\ne[\,]$ (Remark 5.6).

## 2. The classification used

This section recalls definitions and one theorem of crim-hook-stacks.

**Run pairs.** Let $\lambda\ne[\,]$ have distinct parts $v_1>\dots>v_k>0$, where $v_i$ occurs
$a_i$ times, and put $b_i=v_i-v_{i+1}$ with $v_{k+1}=0$. The run pairs of $\lambda$ are
$(a_1,b_1),\dots,(a_k,b_k)$, all entries positive (`ValidPairs`). Conversely, `ofPairs p` is
the partition in which $b_i+\dots+b_k$ occurs $a_i$ times; every partition is `ofPairs p` for
some valid $p$ (`exists_ofPairs`). The boundary length is
`plen p` $=\sum_i(a_i+b_i)=\ell(\lambda)+\lambda_1$ (`plen_eq`,
`length_add_part_one_ofPairs`).

**The statistic $M$.** A pair $(a,b)$ is *A-good* if $a=1$ and $b$ is odd, and *B-good* if $a$
is odd and $b=1$; in both cases $a+b$ is even. $L$ (`endL`) is the length of the longest
prefix of A-good pairs, $R$ (`endR`) the length of the longest suffix of B-good pairs, and
$M=\min(k,L+R)$ (`endM`). The duality $\delta$ (`pdual`) reverses the list and swaps each pair.
It exchanges $L$ and $R$ (`endL_pdual`).

**Theorem 2.1** (Zeng; `isP_ofPairs_iff`). For valid $p$, `ofPairs p` is a $\mathcal P$-position
iff `plen p` and `endM p` are both even.

## 3. The meld conjecture

**Lemma 3.1** (`meld_assoc`, `meld_nil_left`, `meld_nil_right`, `melds_iff`). The meld is
associative with unit $[\,]$, and `Melds S` is the set of right-nested melds of finite lists of
members of $S$.

*Proof.* $(\mu\diamond\nu)_1=\nu_1+\mu_1$ (`part_one_meld`), so both sides of the associative
law equal $\lambda$ shifted by $\nu_1+\mu_1$, then $\nu$ shifted by $\mu_1$, then $\mu$. For
`melds_iff`, induct on `Melds`: a join of two right-nested melds is the right-nested meld of
the concatenated lists (`meldAll_append`). $\square$

**Lemma 3.2** (`meld_ofPairs`). If $B$ is valid, then
$\texttt{ofPairs}\,B\diamond\texttt{ofPairs}\,A=\texttt{ofPairs}\,(A\mathbin{+\!\!+}B)$.

*Proof.* `ofPairs (A ++ B)` is `ofPairs A` with every part raised by the sum of the $b$-entries
of $B$, followed by `ofPairs B` (`ofPairs_append`). That sum is the first part of
`ofPairs B` (`part_one_ofPairs`). $\square$

So a meld of partitions is the concatenation of their run pairs, in the order of the meld read
from the right: $\mu\diamond\lambda$ has the pairs of $\lambda$ first.

**Lemma 3.3** (`validPairs_thickPairs`, `ofPairs_thickPairs`, `plen_thickPairs`,
`endL_thickPairs`, `endR_thickPairs`). The thick hook $\Gamma^{a,b}_{r,c}$ has run pairs
$(a,c-b),(r-a,b)$. Its boundary length is $r+c$, and $L=R=0$.

*Proof.* The rows are $a$ copies of $c$ and $r-a$ copies of $b$, with $c>b>0$. The first pair
has $a\ge2$, so it is not A-good. The last pair has $b\ge2$, so it is not B-good. $\square$

**Corollary 3.4** (`isP_thickHook_iff`). $\Gamma^{a,b}_{r,c}\in\mathcal P$ iff $r+c$ is even.
This is the $\mathcal P/\mathcal N$ part of the paper's `thm:thick-hook`.

**Lemma 3.5** (`endL_append_eq_zero`, `endR_append_eq_zero`). If $L(A)=L(B)=0$, then
$L(A\mathbin{+\!\!+}B)=0$; if $R(A)=R(B)=0$, then $R(A\mathbin{+\!\!+}B)=0$.

*Proof.* If $A=[\,]$ the first claim is $L(B)=0$. Otherwise the first pair of $A$ is not
A-good, and it is also the first pair of $A\mathbin{+\!\!+}B$. The second claim follows by
$\delta$, which reverses concatenation and exchanges $L$ and $R$. $\square$

**Theorem 3.6** (`exists_pairs_of_melds`, `meldConjecture_holds`). Every meld of losing thick
hooks is a $\mathcal P$-position.

*Proof.* Induct on `Melds`. Every member is `ofPairs p` for a valid $p$ with `plen p` even and
$L(p)=R(p)=0$. For $[\,]$ take $p=[\,]$. For a losing thick hook, Lemma 3.3 gives $L=R=0$, and
Theorem 2.1 gives an even boundary length. For a join, Lemma 3.2 concatenates the pair lists;
the boundary lengths add (`plen_append`), and Lemma 3.5 keeps $L=R=0$. Finally $M=0$ is even,
so Theorem 2.1 gives $\mathcal P$. $\square$

`isP_meldAll` restates the theorem for right-nested melds of a list.

## 4. conj:pself

Fix a partition $\lambda=$ `ofPairs p` with $p$ valid and $k=|p|$ run pairs. Rows are numbered
from $1$, with $\lambda_i=0$ for $i>\ell(\lambda)$.

**Lemma 4.1** (`countP_ofPairs`). $\lambda'_{j+1}$ is row $j+1$ of `ofPairs (pdual p)`. In other
words, $\delta$ is conjugation.

*Proof.* Induct on $p$. For $p=(a,b)::q$, let $B$ be the largest part of `ofPairs q`. Then
`ofPairs p` is `ofPairs q` with $a$ rows of length $b+B$ added on top, and, since
$\delta p=\delta q\mathbin{+\!\!+}[(b,a)]$, `ofPairs (pdual p)` is `ofPairs (pdual q)` with
every row lengthened by $a$, followed by $b$ rows of length $a$ (`ofPairs_append`). The latter
has $B$ rows before the $b$ new ones. So both sides of the claim grow by $a$ when $j<b+B$ and
stay $0$ otherwise. $\square$

Hence $\lambda$ is parity self-conjugate iff $\lambda$ and $\lambda'=$ `ofPairs (pdual p)` have
the same parity sequence $(\lambda_i\bmod 2)_{i\ge1}$ (`parity_eq_of_paritySelfConj`).

**Lemma 4.2** (`endL_drops`). The drops $\lambda_i-\lambda_{i+1}$ are odd for $1\le i\le L$, and
the drop at $i=L+1$ is even.

*Proof.* Induct on $p$. An A-good first pair is a single row with an odd drop, and $L$ moves
on to the rest. If the first pair is not A-good, either $a\ge2$ (the first drop is $0$) or
$a=1$ with an even drop. $\square$

So $L$ depends only on the parity sequence of $\lambda$ (`endL_le_of_parity`).

**Lemma 4.3** (`endL_eq_endR_of_paritySelfConj`, `even_plen_of_paritySelfConj`). If $\lambda$ is
parity self-conjugate, then $L=R$ and $\ell(\lambda)+\lambda_1$ is even.

*Proof.* $R(p)=L(\delta p)$ is the $L$ of $\lambda'$, which has the same parity sequence, so
Lemma 4.2 gives $L=R$. The case $k=1$ of parity self-conjugacy reads
$\lambda_1\equiv\lambda'_1=\ell(\lambda)$. $\square$

**Case $L+R<k$.** Then $M=L+R=2L$ is even, the boundary length is even, and
$\lambda\in\mathcal P$ by Theorem 2.1. So a parity self-conjugate $\mathcal N$-position has
$L+R\ge k$.

**Lemma 4.4** (`forall_good_of_le`). If $L+R\ge k$, every run pair is A-good or B-good, so all
entries $a_i,b_i$ are odd.

*Proof.* The longest A-good prefix and the longest B-good suffix overlap or meet. In Lean: the
part after the A-good prefix has all its pairs B-good (`forall_bGood_of_endR_eq`). $\square$

**Lemma 4.5** (`map_fst_eq_of_parity`, `pdual_eq_self_of_parity`). If every $b$-entry of $p$ and
of $q$ is odd and `ofPairs p`, `ofPairs q` have the same parity sequence, then $p$ and $q$ have
the same $a$-entries. Consequently, if all entries of $p$ are odd and $\lambda$ is parity
self-conjugate, then $\delta p=p$, that is, $\lambda$ is self-conjugate.

*Proof.* Within a block of $a_1$ equal rows the parity is constant, and after the block it
flips, because $b_1$ is odd. So $a_1$ is the position of the first parity change; induct. For
the consequence, apply this to $p$ and $\delta p$: all $b$-entries of $\delta p$ are $a$-entries
of $p$, hence odd. The $a$-entries of $\delta p$ are the reversed $b$-entries of $p$ and vice
versa, so equal $a$-entries force $\delta p=p$. $\square$

**The shape of the stacks.** For a list $os=[o_1,\dots,o_j]$ let `spPairs os` be
\[
(1,o_1),\dots,(1,o_j),(1,1),(o_j,1),\dots,(o_1,1).
\]
If every $o_i$ is odd, it is valid and self-dual (`validPairs_spPairs`, `pdual_spPairs`), its
first $j+1$ pairs are A-good and its last $j+1$ pairs are B-good, so
$M=k=2j+1$ (`endM_spPairs`).

**Lemma 4.6** (`eq_spPairs`). If $|p|=2n+1$, $\delta p=p$ and the first $n+1$ pairs of $p$ are
A-good, then $p=$ `spPairs os` with every $o_i$ odd.

*Proof.* Induct on $n$. For $n=0$, $p=[(a,b)]$ with $(b,a)=(a,b)$ and $a=1$, so $p=[(1,1)]$.
For $n+1$, write $p=x\,q\,y$. Self-duality gives $y=x^{\mathrm{swap}}$ and $\delta q=q$. The
first pair $x=(1,o)$ is A-good, so $o$ is odd and $y=(o,1)$. The first $n+1$ pairs of $q$ are
A-good, so $q=$ `spPairs os` by induction, and $p=$ `spPairs (o :: os)` (`spPairs_cons`).
$\square$

**Proposition 4.7** (`oddHookStack_of_paritySelfConj`). A parity self-conjugate
$\mathcal N$-position has run pairs `spPairs os` with every $o_i$ odd.

*Proof.* By Lemma 4.3 and the case $L+R<k$, we have $L=R$, an even boundary length and
$L+R\ge k$. Then $M=k$, and $\lambda\in\mathcal N$ forces $k$ odd, say $k=2n+1$, so
$L=R\ge n+1$. Lemmas 4.4 and 4.5 give $\delta p=p$, and Lemma 4.6 applies. $\square$

**Lemma 4.8** (`oddHookStack_iff`). A partition is a stack of odd self-conjugate hooks and
$[1]$ (`OddHookStack`) iff it is `ofPairs (spPairs os)` with every $o_i$ odd.

*Proof.* `stack_hook` (crim-hook-stacks) says that $\Gamma_{r,r}\lhd\mu$ is defined iff
$\ell(\mu)\le r-1$ and $\mu_1\le r-1$, and then it is $[r,1+\mu_1,\dots,1+\mu_m,1^{r-1-m}]$.
Let $\mu=$ `ofPairs (spPairs os)`. It is self-conjugate, so $\ell(\mu)=\mu_1=N$, and $N$ is odd
(`odd_pairsBSum_spPairs`). For odd $r$ the stack is therefore defined iff $N\le r-1$, and then
$o=r-1-N$ is odd, hence $o\ge1$, and
$\Gamma_{r,r}\lhd\mu=[o+N+1,(\mu_i+1)_i,1^o]$ has run pairs `spPairs (o :: os)`
(`ofPairs_spPairs_cons`). Conversely, `spPairs (o :: os)` arises in this way from
$r=o+N+1$, which is odd. Induct on the stack, or on $os$. $\square$

**Theorem 4.9** (`paritySelfConj_and_not_isP_iff`, `pselfConjecture_holds`). For every partition
$\lambda$: $\lambda$ is parity self-conjugate and in $\mathcal N$ iff $\lambda$ is a stack of odd
self-conjugate hooks and $[1]$. In particular conj:pself holds.

*Proof.* ($\Rightarrow$) Proposition 4.7 and Lemma 4.8. ($\Leftarrow$) By Lemma 4.8 the run
pairs are `spPairs os`. Self-duality and Lemma 4.1 give $\lambda'=\lambda$
(`conjPart_of_oddHookStack`), so $\lambda$ is parity self-conjugate. All pairs have $a+b$ even,
so the boundary length is even, and $M=2j+1$ is odd, so $\lambda\in\mathcal N$ by Theorem 2.1
(`not_isP_ofPairs_spPairs`). $\square$

In particular every parity self-conjugate $\mathcal N$-position is self-conjugate.

**Lemma 4.10** (`stack_hook_assoc`). Let $c\ge1$, let $\mu$ be a nonempty partition and $\nu$ a
partition. Then $(\Gamma_{r,c}\lhd\mu)\lhd\nu$ is defined iff $\Gamma_{r,c}\lhd(\mu\lhd\nu)$ is,
and then the two are equal.

*Proof.* Let $d=d(\mu)$, so $d\ge1$, and let $m=\ell(\mu)$. When $\mu\lhd\nu$ is defined it has
the same length and first row as $\mu$ (`stack_facts`), so if $\Gamma_{r,c}\lhd\mu$ is
undefined then so is the right side. Otherwise $x=\Gamma_{r,c}\lhd\mu$ has Durfee length $d+1$
(`durfee_hookStack`), $x_{d+1}=\mu_d+1$, and for $i\ge1$ row $d+1+i$ of $x$ is $\mu_{d+i}+1$ if
$d+i\le r-1$ and $0$ otherwise, while $\mu_{d+i}=0$ once $d+i>r-1\ge m$. So
$x_{d+1+i}=d+1$ iff $\mu_{d+i}=d$, and $x_{d+1}\ge d+1+\nu_1$ iff $\mu_d\ge d+\nu_1$: the
stack $x\lhd\nu$ is defined iff $\mu\lhd\nu$ is. When both are, adding $\nu_i$ to row $d+1+i$
of $x$ is the same as adding $\nu_i$ to row $d+i$ of $\mu$ and then stacking under
$\Gamma_{r,c}$ (`hookStack_stack_eq`). $\square$

**Corollary 4.11** (`HookTree.eval_eq_nest`, `exists_hookTree_iff`,
`pselfConjecture_anyBracketing`). Bracket $\Gamma_{r_1,r_1}\lhd\cdots\lhd\Gamma_{r_j,r_j}$, with
every $r_i\ge1$, in any way, and require every intermediate stack to be defined. The result is
defined iff the right-nested stack is, and then the two are equal. Hence conj:pself holds for
every bracketing of the stack of odd self-conjugate hooks and $[1]$.

*Proof.* A bracketing is a binary tree `HookTree` whose leaves, read from left to right, are the
hooks. Write `nest` for right nesting; every right-nested stack of hooks is a nonempty
partition (`nest_isPartition`). Lemma 4.10, applied once per hook, moves a stack on the inside
out of a right nest: $(H_1\lhd(\cdots\lhd H_i))\lhd y=H_1\lhd(\cdots\lhd(H_i\lhd y))$, with the
same definedness (`nest_assoc`). Induct on the tree: at a node $t\lhd u$, both subtrees are
right nests by induction, and `nest_assoc` turns $t\lhd u$ into one right nest. $\square$

## 5. Misère play

In misère play the player who makes the last move loses. So $[\,]$ is an $\mathcal N$-position
(the player to move cannot move, and wins), and a nonempty position is a $\mathcal P$-position
iff no move reaches a $\mathcal P$-position (`isMP`, `IsMP`, `isMP_iff`). For a pair list $p$,
let $Z$ be Zeng's condition "`plen p` and `endM p` are both even" of Theorem 2.1, and call $p$
*covered* ($C$) if $L+R\ge k$, that is, $M=k$ (`cover_iff`). By Lemma 4.4 every pair of a
covered list is good. In terms of Lemma 4.2, $L$ is the number of leading rows with an odd
drop, $R$ is the same number for $\lambda'$, and $k$ is the number of distinct parts. Write
$\mathrm{MisP}(p)$ for "exactly one of $Z$ and $C$ holds" (`MisP`). The sections below use
Section 7 of [crim-hook-stacks](../crim-hook-stacks/DETAILS.md): its Lemma 7.1 lists the moves
on pair lists (`PMove`), and Lemmas 7.2 to 7.4 are the steps of Zeng's proof.

**Theorem 5.1** (`misereP_iff`, `misereP_iff_isP`). For valid $p$, `ofPairs p` is a misère
$\mathcal P$-position iff $\mathrm{MisP}(p)$; by Theorem 2.1, iff exactly one of "`ofPairs p`
is a normal-play $\mathcal P$-position" and "$p$ is covered" holds.

An earlier scouting run of this project proposed this rule. For example, $[1]$ and $[3]$, with
pairs $(1,1)$ and $(1,3)$, are covered with $M=1$, so they are misère $\mathcal P$-positions.
$[2,1]$, with pairs $(1,1),(1,1)$, is covered with even `plen` and $M=2$, so it is a misère
$\mathcal N$-position (it can move to $[1]$). The empty list satisfies both $Z$ and $C$, so
$[\,]$ is a misère $\mathcal N$-position, as it should be.

**Lemma 5.2** (`even_plen_of_cover`, `even_plen_of_misP`, `ne_nil_of_misP`). Covered lists
have even `plen`. Hence $\mathrm{MisP}(p)$ implies that `plen p` is even, and
$\mathrm{MisP}([\,])$ fails.

*Proof.* A list of odd `plen` splits as $P\,C\,S$ with a nonempty core, as in the proof of
Lemma 7.4 (`exists_split`), so $L+R=|P|+|S|<k$. $\square$

**Lemma 5.3** (`length_eq_of_even`, `misP_iff_of_move`). If `PMove p q` and `plen p`,
`plen q` are both even, then $q$ has one pair fewer than $p$, `endM p = endM q + 1`, and
$\mathrm{MisP}(p)\iff\neg\,\mathrm{MisP}(q)$.

*Proof.* By the proof of Lemma 7.2 the move removes an A-good first pair or a B-good last pair,
and it lowers $M$ by one (`endM_eq_of_even`). So $Z$ flips, while $M=k$ holds for $p$ iff it
holds for $q$, so $C$ is kept (`misP_iff_of_succ`). $\square$

**Lemma 5.4** (`not_misP_move`). If $\mathrm{MisP}(p)$ and `PMove p q`, then
$\mathrm{MisP}(q)$ fails.

*Proof.* `plen p` is even by Lemma 5.2. If `plen q` is odd, Lemma 5.2 applies to $q$;
otherwise Lemma 5.3 does. $\square$

**Lemma 5.5** (`exists_misP_move`). If $p$ is valid and nonempty and $\mathrm{MisP}(p)$ fails,
some move reaches a $q$ with $\mathrm{MisP}(q)$.

*Proof.* Suppose `plen p` is even. Then $M\ge1$, since $M=0$ would give $Z$ and, as
$p\ne[\,]$, not $C$. So an end pair can be removed with `plen` staying even
(`exists_peel`, as in Lemma 7.3), and Lemma 5.3 gives $\mathrm{MisP}(q)$.

Suppose `plen p` is odd. Follow the proof of Lemma 7.4 (`mgood_of_odd`), with $p=P\,C\,S$. Every
move chosen there reaches $Z$. In most cases the new list still has a nonempty core, so it is
not covered and $\mathrm{MisP}$ holds (`misP_of_split`). Three cases reach covered lists and
change, together with their mirror images (`misP_pdual`, `MGood.of_pdual`).

- $L+R$ odd, $P=[\,]$ and $C=[(1,b)]$ with $b$ even, so $R$ is odd. Normal play deletes a 1
  and reaches $(1,b-1)\,S$, which is covered with $M=R+1$ even. Instead delete the 0 of
  $(1,b)$ (`zeroFirst`). This leaves $S$, which has even `plen` and is covered with $M=R$ odd
  (`mgood_core_one_odd`, `misP_of_good`).
- $L+R$ even and $C=[(1,b)]$ with $b$ even. Normal play deletes the 0 and reaches a covered list
  with $M=L+R$ even. Instead delete a 1. The pair $(1,b-1)$ is A-good, so $P\,(1,b-1)\,S$ is
  covered with $k=L+R+1$ odd (`mgood_core_one_even`).
- $L+R$ even, $|C|\ge2$ and the first core pair is $(1,b)$. As in normal play, compare the moves
  "delete the 0 of $(1,b)$" and "delete a 1". Both reach even `plen`, and the second list has
  one more pair and an $M$ that is one larger (`endM_prefix_barrier`). By `misP_iff_of_succ`
  exactly one of the two lists satisfies $\mathrm{MisP}$ (`mgood_core_long`). $\square$

*Proof of Theorem 5.1* (`misere_classification`). Let $G$ be a predicate on valid lists such
that $G(p)$ holds iff $p\ne[\,]$ and no move reaches a $q$ with $G(q)$. By strong induction on
`plen p`, $G(p)\iff\mathrm{MisP}(p)$. If $\mathrm{MisP}(p)$, then $p\ne[\,]$ by Lemma 5.2, and
no move reaches $\mathrm{MisP}$ by Lemma 5.4. Otherwise $p=[\,]$, or Lemma 5.5 gives a move to
$\mathrm{MisP}$. By Lemma 7.1 and `ofPairs_ne_nil_iff`, the predicate
$G(p)=$ `IsMP (ofPairs p)` qualifies (`isMP_ofPairs_iff_forall`), which gives `misereP_iff`.
Theorem 2.1 turns $Z$ into "normal-play $\mathcal P$" (`misereP_iff_isP`). $\square$

The program of Section 6 also solves misère CRIM exactly and confirms the classification for
every partition of size at most 50 (365,204 misère $\mathcal P$-positions). The paper asks
about misère play only through Conway pairs, and we found no prior statement of this
classification.

### Conway pairs and conj:hookswap

By induction on the size, $G^-(\lambda)=0$ iff $\lambda$ is a misère $\mathcal P$-position:
$G^-([\,])=1$, and a nonempty position has $G^-=0$ iff no option has $G^-=0$. So
$\mathrm{cp}(\lambda)=(0,1)$ iff $\lambda$ is a normal-play $\mathcal P$-position (`IsP`) and
$G^-(\lambda)=1$ (`IsMV1`). By `isMV1_iff`, $G^-(\lambda)=1$ iff $\lambda=[\,]$, or some option
of $\lambda$ is a misère $\mathcal P$-position and no option has $G^-=1$. The paper conjectures
(lines 1058–1060):

> **conj:hookswap.** A partition $\lambda$ has Conway pair $(0,1)$ if and only if $\lambda$ is
> an even-by-even hook.

An even-by-even hook is $\Gamma_{r,c}$ with $r$ and $c$ positive and even (`EEHook`).

**Remark 5.6** (`nil_conwayPair`). $[\,]$ has Conway pair $(0,1)$, as the paper uses in its
proof of `thm:cgpairrow`, and it is not a hook. So the statement needs $\lambda\ne[\,]$, and
`hookswapConjecture` is the version for nonempty partitions. This is an edge case of the
wording, not a refutation.

**Lemma 5.7** (`misere_column`, `misere_hook`). For $r,c\ge1$, $\Gamma_{r,c}$ is a misère
$\mathcal P$-position iff $r$ and $c$ are odd, and $G^-(\Gamma_{r,c})=1$ iff $r$ and $c$ are
even.

This is the misère part of the paper's `thm:cgpairshooks` (lines 862–870), restricted to the
values $0$ and $1$.

*Proof.* The column $1^n$ has the options $[\,]$ and $1^{n-1}$ (`mem_moves_column`). By
induction on $n$, $1^n$ is misère $\mathcal P$ iff $n$ is odd, and $G^-(1^n)=1$ iff $n=0$,
because for $n\ge1$ the option $[\,]$ has value $1$ (`misere_column`). This settles $c=1$,
since $\Gamma_{r,1}=1^r$.

For $c\ge2$, induct on $r+c$. The options of $\Gamma_{r,c}$ are $1^{r-1}$, $\Gamma_{r-1,c}$
(if $r\ge2$), $[c-1]=\Gamma_{1,c-1}$ and $\Gamma_{r,c-1}$ (`mem_moves_hookStack`). If $r$ is
even, $1^{r-1}$ is misère $\mathcal P$; if $c$ is even, $[c-1]$ is; if $r$ and $c$ are odd, no
option is. This gives the first claim. If $r$ and $c$ are even, $[c-1]$ is misère
$\mathcal P$, and no option has value $1$, because each has an odd side and $1^{r-1}\ne[\,]$.
In the other cases $G^-(\Gamma_{r,c})\ne1$. If $r$ is odd and $c$ even, the option $[\,]$ (when
$r=1$) or $\Gamma_{r-1,c}$ has value $1$; if $r$ is even and $c$ odd, $\Gamma_{r,c-1}$ has
value $1$; if both are odd, $G^-(\Gamma_{r,c})=0$. $\square$

**Theorem 5.8** (`conwayPair_hook_iff`, `conwayPair_of_eeHook`, `hookswapConjecture_iff`). For
$r,c\ge1$, $\Gamma_{r,c}$ has Conway pair $(0,1)$ iff $r$ and $c$ are even. Hence every
even-by-even hook has Conway pair $(0,1)$, and conj:hookswap for nonempty partitions is
equivalent to its $(\Rightarrow)$ direction.

*Proof.* A hook is a normal-play $\mathcal P$-position iff $r,c\ge2$ and $r\equiv c\pmod 2$
(`isP_hook_iff` of crim-hook-stacks). Combine this with Lemma 5.7. $\square$

**Proposition 5.9** (`not_isMP_of_isMV1`, `covered_of_conwayPair`). If $p$ is valid and
`ofPairs p` has Conway pair $(0,1)$, then $p$ is covered and $k$ is even.

*Proof.* $G^-=1$ gives an option with $G^-=0$, so `ofPairs p` is not misère $\mathcal P$. It is
normal-play $\mathcal P$, so by Theorem 5.1 it is covered. Then $M=k$, and $M$ is even by
Theorem 2.1. $\square$

The $(\Rightarrow)$ direction is not proved. By Proposition 5.9 it concerns covered lists with
even $k$, all of whose pairs are good (Lemma 4.4). An even-by-even hook $\Gamma_{r,c}$ has
the pairs $(1,c-1),(r-1,1)$, so $k=2$, and the case $k=2$ would be a natural first step. We
found no description of the positions with $G^-=1$ that would finish the proof. The program of
Section 6 confirms the nonempty statement for every partition of size at most 50.

## 6. Computations

[`pself_meld_check.py`](programs/pself_meld_check.py) works on partitions as tuples, with no
run-pair encoding except where it compares with Zeng's rule.

- It enumerates all partitions of size $\le N$ in order of size, generates the moves directly
  (deleting a row, or deleting a column and dropping zero parts), and computes the normal and
  misère outcomes by the game recursion; moves lower the size.
- It compares the normal outcome with Zeng's rule everywhere, and the misère outcome with the
  classification of Section 5 (with `--misere`).
- With `--hookswap` it computes the Conway pair of every partition by the mex recursion, with
  $\mathrm{cp}([\,])=(0,1)$, checks it against the two outcomes, and checks conj:hookswap for
  nonempty partitions.
- It enumerates every thick hook of size $\le N$, checks the $\mathcal P/\mathcal N$ part of
  `thm:thick-hook`, closes the losing ones under the meld (both orders) up to size $N$, and
  checks that every result is $\mathcal P$. It also checks associativity and the unit on all
  triples of partitions of size $\le6$.
- It computes the parity self-conjugate $\mathcal N$-positions under the paper's reading and
  under the weaker reading of Section 1.1, and compares them with twelve readings of "the stack":
  hooks $\Gamma_{r,r}$ with $r$ odd or with any $r$; $[1]$ required as the last piece or not;
  right nesting
  ($h\lhd x$), left nesting ($x\lhd h$) or arbitrary bracketing ($x\lhd y$). Every intermediate
  stack uses the general Durfee-length definition and must be defined.

Results for $N=50$ ([log](logs/pself_meld_check_n50.log), 26 s, about 470 MB):

| Check | Result |
|---|---|
| partitions, $\mathcal P$-positions | 1,295,971 and 365,327; Zeng's rule agrees everywhere |
| thick hooks | 1,714, of which 844 are $\mathcal P$; `thm:thick-hook` agrees |
| melds of losing thick hooks | 1,732 (888 with at least two pieces), all $\mathcal P$ |
| associativity and unit | 27,000 triples |
| parity self-conjugate | 3,559 partitions, 56 in $\mathcal N$ |
| misère | 365,204 misère $\mathcal P$-positions, 23,447 covered partitions; the classification holds |
| conj:hookswap | $\mathrm{cp}([\,])=(0,1)$; the 300 nonempty partitions with Conway pair $(0,1)$ are exactly the 300 even-by-even hooks |

| Reading of "the stack" | Stacks | Result |
|---|---|---|
| $r$ odd, $[1]$ last; right, left or any nesting | 56 each | exactly the 56 parity self-conjugate $\mathcal N$-positions |
| $r$ odd, $[1]$ not required | 116 | 60 extra stacks, first $[3,1,1]=\Gamma_{3,3}$ |
| all $r$, $[1]$ last | 581 | 525 extra stacks, first $[2,2]=\Gamma_{2,2}\lhd[1]$ |
| all $r$, $[1]$ not required | 1,212 | 1,156 extra stacks, first $[2,1]=\Gamma_{2,2}$ |

Under the weaker parity reading there are 834 parity self-conjugate $\mathcal N$-positions,
and 778 of them are not stacks under any of the twelve readings. With `--max-n 35` the run
takes about 1 s; that is the CI entry.

## 7. Related work and credits

See the [README](README.md#related-work-and-credits). In short: the conjectures are Bašić,
Gottlieb and Krnc's; both proofs are corollaries of Zijian Zeng's classification (an unrefereed
preprint), formalized in crim-hook-stacks, and the misère proof reuses the move analysis of
Zeng's proof; the $(\Leftarrow)$ direction of conj:hookswap follows from the paper's
`thm:cgpairshooks`; an earlier scouting run of this project found both routes and the misère
hypothesis, wrote the first Lean draft of the meld argument, and checked conj:hookswap for
nonempty partitions to size 50.
