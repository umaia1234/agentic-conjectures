**English** | [한국어](README.ko.md)

# CRIM: melds of losing thick hooks, parity self-conjugate partitions and misère play

Ina Bašić, Eric Gottlieb and Matjaž Krnc, *CRIM: A Natural Game on Integer Partitions*,
[arXiv:2606.16828v1](https://arxiv.org/abs/2606.16828) (2026-06-15), study Column–Row
Impartial Merge (CRIM). A position is an integer partition $\lambda$, and a move deletes one row
or one column of its Young diagram and reattaches the pieces. Play is normal, so the empty
partition $[\,]$ is a $\mathcal P$-position ("losing"). The two conjectures proved here are
theirs, from Section 5 (Future Work) of the paper:

> A meld of losing thick hooks is losing.

> **conj:pself.** A parity self-conjugate partition is in $\mathcal N$ if and only if it is the
> stack of odd self-conjugate hooks and $[1]$.

The paper checked conj:pself for $n\le50$. Both conjectures are listed as open (see
[Sources checked](#sources-checked)).

This directory proves both conjectures in Lean. Both proofs are short corollaries of a
classification of all $\mathcal P$-positions by boundary words, which **Zijian Zeng** stated and
proved in an unrefereed preprint (see [Related work and credits](#related-work-and-credits)).
The sibling problem [crim-hook-stacks](../crim-hook-stacks/README.md) formalizes Zeng's
classification in Lean as `isP_ofPairs_iff`, and this directory builds on it. An earlier
scouting run of this project found both routes. No human has reviewed this work yet.

The directory also proves a classification of the misère $\mathcal P$-positions
([Misère play](#misère-play)). The rule was proposed by the same scouting run; the paper asks
about misère play only through Conway pairs, and we found no prior statement of the rule.
Finally, it states the paper's conj:hookswap for nonempty partitions and proves the direction
that follows from the paper's `thm:cgpairshooks`; the converse is not proved
([conj:hookswap](#conjhookswap-not-proved)).

## The statements

For partitions $\mu=[\mu_1,\dots,\mu_k]$ and $\lambda=[\lambda_1,\dots,\lambda_m]$, the paper's
*meld* (§2.1) is

\[
\mu\diamond\lambda=[\mu_1+\lambda_1,\dots,\mu_1+\lambda_m,\mu_1,\dots,\mu_k].
\]

It is associative, with unit $[\,]$. A *thick hook* (§2.2) is
$\Gamma^{a,b}_{r,c}=[c^a,b^{r-a}]$ with $r>a\ge2$ and $c>b\ge2$.

**Meld conjecture.** If $H_1,\dots,H_n$ ($n\ge0$) are thick hooks in $\mathcal P$, then
$H_1\diamond\cdots\diamond H_n\in\mathcal P$.

A partition is *parity self-conjugate* if $\lambda_k\equiv\lambda'_k\pmod 2$ for every $k\ge1$,
where $\lambda'_k$ is the number of parts $\ge k$ (so both sides are $0$ for large $k$). The
self-conjugate hooks are $\Gamma_{r,r}=[r,1^{r-1}]$, and $\lhd$ is the paper's stack, defined
through the Durfee length ([DETAILS §1](DETAILS.md#1-definitions-and-statements)).

**conj:pself.** A parity self-conjugate partition $\lambda$ is an $\mathcal N$-position if and
only if

\[
\lambda=\Gamma_{r_1,r_1}\lhd\Gamma_{r_2,r_2}\lhd\cdots\lhd\Gamma_{r_j,r_j}\lhd[1]
\]

for some $j\ge0$ and odd $r_1,\dots,r_j$, with every stack defined. For example,
$[1]$, $[3,2,1]=\Gamma_{3,3}\lhd[1]$, $[5,2,1^3]=\Gamma_{5,5}\lhd[1]$ and
$[5,4,3,2,1]=\Gamma_{5,5}\lhd\Gamma_{3,3}\lhd[1]$ are such stacks.

## Verified outcomes

The Lean module [`CrimPselfMeld.lean`](../../AgenticConjectures/CrimPselfMeld.lean)
kernel-checks the following, with no `sorry`, no extra axioms and no `native_decide`.

| Theorem | Statement |
|---|---|
| `meldConjecture_holds` | The meld conjecture (`meldConjecture`): every meld of losing thick hooks, of any number of pieces and in any bracketing, is a $\mathcal P$-position. |
| `isP_meldAll` | The same for a right-nested meld $H_1\diamond(H_2\diamond(\cdots\diamond H_n))$ given as a list. |
| `pselfConjecture_holds` | conj:pself (`pselfConjecture`). |
| `paritySelfConj_and_not_isP_iff` | A slightly stronger form: a partition is parity self-conjugate and in $\mathcal N$ iff it is a stack of odd self-conjugate hooks and $[1]$. |
| `oddHookStack_iff` | These stacks are exactly the partitions whose run pairs are $(1,o_1),\dots,(1,o_j),(1,1),(o_j,1),\dots,(o_1,1)$ with every $o_i$ odd; in particular they are self-conjugate (`conjPart_of_oddHookStack`). |
| `pselfConjecture_anyBracketing` | conj:pself with the stack bracketed in any way. By `stack_hook_assoc`, $(\Gamma_{r,c}\lhd\mu)\lhd\nu=\Gamma_{r,c}\lhd(\mu\lhd\nu)$ for every nonempty partition $\mu$, with either side defined iff the other is, so every bracketing gives the right-nested stack (`exists_hookTree_iff`). |
| `meld_assoc`, `melds_iff` | The meld is associative with unit $[\,]$, so the bracketing of a meld does not matter. |
| `misereP_iff`, `misereP_iff_isP` | Misère play: a partition is a misère $\mathcal P$-position iff exactly one of "it is a normal-play $\mathcal P$-position" and "it is covered" holds (see [Misère play](#misère-play)). |
| `isP_thickHook_iff` | A thick hook is in $\mathcal P$ iff $r\equiv c\pmod 2$, the $\mathcal P/\mathcal N$ part of the paper's `thm:thick-hook`. |
| `conwayPair_of_eeHook` | The $(\Leftarrow)$ direction of conj:hookswap: every even-by-even hook has Conway pair $(0,1)$. It rests on `misere_hook`: a hook $\Gamma_{r,c}$ has misère Grundy value $0$ iff $r$ and $c$ are odd, and $1$ iff they are even, as the paper's `thm:cgpairshooks` says. |
| `hookswapConjecture_iff`, `covered_of_conwayPair` | conj:hookswap for nonempty partitions (`hookswapConjecture`, not proved) is equivalent to its $(\Rightarrow)$ direction, and a position with Conway pair $(0,1)$ is covered and has an even number of distinct parts. |
| `nil_conwayPair` | $[\,]$ has Conway pair $(0,1)$ and is not a hook, so conj:hookswap needs $\lambda\ne[\,]$. |

**How the proofs go.** Encode a partition by the run lengths of its boundary word: run pairs
$(a_1,b_1),\dots,(a_k,b_k)$, where $a_i$ is the number of rows of the $i$-th largest part size
and $b_i$ is the drop to the next size. Zeng's classification says that $\lambda\in\mathcal P$
iff the boundary length $\ell(\lambda)+\lambda_1$ and an end-peeling statistic $M=\min(k,L+R)$
are both even. Here $L$ counts the leading pairs $(1,\text{odd})$ and $R$ the trailing pairs
$(\text{odd},1)$.

- *Meld.* A meld concatenates run pairs, and a thick hook has run pairs $(a,c-b),(r-a,b)$ with
  $a,b\ge2$. So in a meld of thick hooks $L=R=0$, hence $M=0$, and the boundary lengths add up.
- *conj:pself.* Conjugation reverses the run pairs and swaps each pair. $L$ is the number of
  leading rows with an odd drop $\lambda_i-\lambda_{i+1}$, so for a parity self-conjugate
  partition $L=R$ and the boundary length is even. If $L+R<k$, then $M=2L$ is even and
  $\lambda\in\mathcal P$. Otherwise every run pair has odd entries, parity self-conjugacy forces
  self-conjugacy, $M=k$, and the run pairs have the shape above with $k=2j+1$ odd, so
  $\lambda\in\mathcal N$. These are exactly the stacks.

[DETAILS.md](DETAILS.md) gives both proofs on paper, with the Lean name of every step.

## Computational evidence

[`programs/pself_meld_check.py`](programs/pself_meld_check.py) is an independent exhaustive
check. It solves CRIM directly by the game recursion, and does not use the Lean proofs or the
run-pair encoding except to compare against Zeng's rule.

| What it checks, for all partitions of size $\le N$ | Result for $N=50$ ([log](logs/pself_meld_check_n50.log)) |
|---|---|
| exact $\mathcal P/\mathcal N$ table; Zeng's rule | 1,295,971 partitions, 365,327 in $\mathcal P$; Zeng's rule agrees everywhere |
| `thm:thick-hook`'s $\mathcal P/\mathcal N$ part | 1,714 thick hooks, 844 in $\mathcal P$; agrees |
| the meld conjecture: every meld of losing thick hooks | 1,732 melds (888 with at least two pieces), all in $\mathcal P$ |
| the meld is associative with unit $[\,]$ | all 27,000 triples of partitions of size $\le6$ |
| conj:pself under 12 readings of "the stack" | 3,559 parity self-conjugate partitions, 56 in $\mathcal N$; the reading used here matches exactly, under right, left and arbitrary nesting |
| the misère classification below | 365,204 misère $\mathcal P$-positions, 23,447 covered partitions; 0 failures |
| conj:hookswap for nonempty partitions | $\mathrm{cp}([\,])=(0,1)$; the 300 nonempty partitions with Conway pair $(0,1)$ are exactly the 300 even-by-even hooks |

The run takes 26 s and about 470 MB. The readings that fail are listed under
[Statement faithfulness](#statement-faithfulness).

## Misère play

In misère play the player who makes the last move loses, so $[\,]$ is an $\mathcal N$-position.
Let $k$ be the number of distinct parts of $\lambda$, let $L$ be the number of leading rows with
an odd drop $\lambda_i-\lambda_{i+1}$ (where $\lambda_{\ell+1}=0$), and let $R$ be the same
number for $\lambda'$. Call $\lambda$ *covered* if $L+R\ge k$. An earlier scouting run of this
project proposed the following rule, and the module proves it (`misereP_iff`,
`misereP_iff_isP`):

> $\lambda$ is a misère $\mathcal P$-position iff exactly one of "$\lambda$ is a normal-play
> $\mathcal P$-position" and "$\lambda$ is covered" holds.

For example, $[1]$ and $[3]$ are covered normal-play $\mathcal N$-positions, so they are misère
$\mathcal P$-positions, while $[2,1]$ is covered and normal-play $\mathcal P$, so it is a misère
$\mathcal N$-position. The proof ([DETAILS.md §5](DETAILS.md#5-misère-play)) uses two facts:
covered partitions have even boundary length, and a move between two positions of even
boundary length removes an end run pair. Positions of odd boundary length reuse the moves of
Zeng's proof, changed in three cases. The paper asks about misère play only through Conway
pairs, and we found no prior statement of this rule. The program above also confirms it for
every partition of size at most 50.

## conj:hookswap (not proved)

The paper (§2) defines the misère Grundy value $G^-$ by the Sprague–Grundy recursion with value
$1$ at the terminal position $[\,]$, and the *Conway pair*
$\mathrm{cp}(\lambda)=(\mathrm{sg}(\lambda),G^-(\lambda))$. So $G^-(\lambda)=0$ means that
$\lambda$ is a misère $\mathcal P$-position, and $\mathrm{cp}(\lambda)=(0,1)$ means that
$\lambda\in\mathcal P$ and $G^-(\lambda)=1$. Section 5 of the paper conjectures:

> **conj:hookswap.** A partition $\lambda$ has Conway pair $(0,1)$ if and only if $\lambda$ is
> an even-by-even hook.

An even-by-even hook is $\Gamma_{r,c}=[c,1^{r-1}]$ with $r$ and $c$ even and positive. As
written, the statement fails at $[\,]$: the paper itself computes $\mathrm{cp}([\,])=(0,1)$,
and $[\,]$ is not a hook (`nil_conwayPair`). This is an edge case of the wording, not a
refutation, and the module states the conjecture for nonempty partitions
(`hookswapConjecture`). What is proved:

- $(\Leftarrow)$ follows from the paper's `thm:cgpairshooks`, which computes the Conway pair of
  every hook. The module proves the part it needs: by induction on $r+c$ over the four kinds of
  options of a hook, $G^-(\Gamma_{r,c})=0$ iff $r$ and $c$ are odd, and $G^-(\Gamma_{r,c})=1$
  iff $r$ and $c$ are even (`misere_hook`). With the normal-play status of hooks this gives
  `conwayPair_of_eeHook`, so the conjecture is equivalent to $(\Rightarrow)$
  (`hookswapConjecture_iff`).
- Towards $(\Rightarrow)$: a position with Conway pair $(0,1)$ is covered and has an even
  number $k$ of distinct parts (`covered_of_conwayPair`). It has an option with $G^-=0$, so it
  is not a misère $\mathcal P$-position, and by the misère rule an uncovered normal-play
  $\mathcal P$-position would be one. So it is covered, which gives $M=k$ in Zeng's rule, and
  $M$ is even because it is in $\mathcal P$.

The $(\Rightarrow)$ direction is not proved: we found no description of the positions of
misère value $1$ that would close it. The program above confirms the nonempty statement for
every partition of size at most 50.

## Reproduction

Run these from this directory. The first is the CI entry in [`status.yaml`](status.yaml); the
runtimes were measured on 2026-10-25 on a shared Apple silicon machine.

```bash
python3 programs/pself_meld_check.py --max-n 35 --misere --hookswap
```

```bash
python3 programs/pself_meld_check.py --max-n 50 --misere --hookswap
```

These take about 1 s and 26 s. The second produced
[`logs/pself_meld_check_n50.log`](logs/pself_meld_check_n50.log); the first produced
[`logs/pself_meld_check_n35.log`](logs/pself_meld_check_n35.log).

## Statement faithfulness

There is no Formal Conjectures statement, so both formal statements (`meldConjecture` and
`pselfConjecture`) are ours. Each definition was checked against the TeX source;
[DETAILS.md §1.1](DETAILS.md#11-readings) lists every reading.

- Positions, moves and $\mathcal P$ are those of crim-hook-stacks: partitions are weakly
  decreasing lists of positive naturals (`IsPartition`), `part l i` is $\lambda_i$ (1-indexed,
  $0$ past the end), and `IsP` is the normal-play $\mathcal P$-status, with $[\,]$ losing.
- `meld μ lam` is the paper's formula, with $\mu_1=0$ when $\mu=[\,]$. `thickHook r c a b` is
  $[c^a,b^{r-a}]$, and `ThickParams` is exactly the paper's $r>a\ge2$, $c>b\ge2$.
- "A meld of losing thick hooks" is any member of `Melds S`, the closure of the losing thick
  hooks under the binary meld, in any bracketing. It includes a single thick hook and the empty
  meld $[\,]$, which is $\mathcal P$, so including it costs nothing. By `melds_iff` this is the
  same as the right-nested melds of finite lists.
- Parity self-conjugacy compares $\lambda_k$ and $\lambda'_k$ for every $k\ge1$, with $0$ past
  the end on both sides, as the paper's "for every $k$" says. Comparing only
  $k\le\min(\ell(\lambda),\lambda_1)$ would make conj:pself false at $[3]$.
- "Odd self-conjugate hooks" are $\Gamma_{r,r}$ with $r$ odd. A hook $\Gamma_{r,c}$ has
  conjugate $\Gamma_{c,r}$, so the self-conjugate hooks are the $\Gamma_{r,r}$; all of them have
  odd size $2r-1$, so "odd" must refer to $r$, as in the paper's Observation on "odd hooks"
  $\Gamma_{2m+1,2m'+1}$.
- "The stack of odd self-conjugate hooks and $[1]$" is read as
  $\Gamma_{r_1,r_1}\lhd(\Gamma_{r_2,r_2}\lhd(\cdots\lhd(\Gamma_{r_j,r_j}\lhd[1])))$, $j\ge0$,
  with $[1]$ last and every intermediate stack defined (`OddHookStack`). The stack is the
  paper's general Durfee-length definition (`stack` in crim-hook-stacks), not a hook formula.
  The paper writes such stacks without brackets, says that the stack operation is associative,
  and puts $[1]$ last in its Observation. The Lean statement uses right nesting, and
  `pselfConjecture_anyBracketing` proves the conjecture for every bracketing, so the choice
  does not matter.
- Alternative readings fail for $n\le50$: allowing every self-conjugate hook $\Gamma_{r,r}$
  fails at $[2,2]=\Gamma_{2,2}\lhd[1]$, which is $\mathcal P$; not requiring $[1]$ last fails
  at $[3,1,1]=\Gamma_{3,3}$, which is $\mathcal P$.
- $j=0$ is allowed: $[1]$ alone is a stack, and it is parity self-conjugate and in
  $\mathcal N$.
- conj:hookswap is stated for nonempty partitions (`hookswapConjecture`), because of $[\,]$.
  `IsMV1` is "misère Grundy value $1$" by the paper's recursion: $[\,]$, or a position with an
  option of value $0$ (a misère $\mathcal P$-position) and no option of value $1$
  (`isMV1_iff`). `EEHook` is `hook r c` with $r,c\ge2$ even. The program computes Conway pairs
  by the mex recursion and checks them against these definitions.

## Related work and credits

- **The paper** proves `thm:thick-hook` (Sprague–Grundy values of thick hooks) and the meld
  results `thm:rectairs` and `thm:ltrl` that motivate the meld conjecture. Its Observation
  derives, from conj:bloby, that a stack of odd hooks ending in $[1]$ is winning. Its
  `thm:cgpairshooks` computes the Conway pairs of all hooks, which gives the $(\Leftarrow)$
  direction of conj:hookswap.
- **Zijian Zeng**, *A Boundary-Word Classification of Losing Positions in CRIM* (dated
  2026-08-29, unrefereed; GitHub `ArtificialZeng/AI-Has-Taste`, folder
  `reproducible_source_code/BigWIN2/BW2-B02-P10`), states and proves the classification of the
  $\mathcal P$-positions on which both proofs here rest. The misère proof also reuses the move
  analysis of Zeng's proof. The preprint settles the paper's conj:main and does not mention the
  meld conjecture, conj:pself or misère play. The Lean formalization of the classification is
  in [crim-hook-stacks](../crim-hook-stacks/README.md).
- **The routes.** An earlier scouting run of this project found both arguments and the misère
  hypothesis, and wrote a first Lean draft of the meld argument for right-nested melds. It also
  checked conj:hookswap for nonempty partitions to size 50. The meld part of the module reuses
  that draft's definitions (`meld`, `thickHook`, `ThickParams`, `thickPairs`) and its lemma
  `meld_ofPairs`, and covers every bracketing. The conj:pself part, including the reading of
  "the stack" and the proof that its bracketing does not matter, the proof of the misère rule
  and the conj:hookswap part are worked out here.
- **S. S. Mehat**, Zenodo
  [10.5281/zenodo.22070744](https://doi.org/10.5281/zenodo.22070744) (2026-08-23), classifies
  the $\mathcal P$-positions with at most six parts or largest part at most six. It is not used
  here.
- **the-omega-institute/trureturing** has Lean refutations of two other conjectures of the same
  paper (`CrimRectairSquareBoundaryRefutation`, `CrimGrundyRefutation`). On these two it has
  only an open issue (#8292, 2026-09-16) that registers a bounded counterexample search for the
  meld conjecture; that run stopped before evaluating any case, and the issue records the
  conjecture as open.

No novelty is claimed. No human has reviewed this work, and nothing has been submitted
anywhere.

## Sources checked

Checked on 2026-10-25, between 16:20 and 16:25 UTC:

- arXiv lists only v1 of 2606.16828, and OpenAlex lists no work citing it.
- MathDB posts 375374 (the meld conjecture) and 375373 (conj:hookswap) are open, with no
  solutions; MathDB has no post for conj:pself.
- OpenConjecture lists the meld conjecture (3664), conj:pself (3666) and conj:hookswap (3663)
  as open conjectures.
- Formal Conjectures has no file, issue or PR about CRIM.
- GitHub code search for "2606.16828", "Impartial Merge" and "parity self-conjugate" finds
  Zeng's repository, the trureturing files, teaching material that poses CRIM as an exercise,
  and catalogue entries; none settles either conjecture. Zeng's repository has no commit since
  2026-09-16. Zenodo has Mehat's artifact and nothing newer.
- None of these sources states the misère rule proved here, and none settles conj:hookswap.
