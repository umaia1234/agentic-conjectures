**English** | [한국어](README.ko.md)

# CRIM: stacking a losing partition under a losing hook

Ina Bašić, Eric Gottlieb and Matjaž Krnc, *CRIM: A Natural Game on Integer Partitions*,
[arXiv:2606.16828v1](https://arxiv.org/abs/2606.16828) (2026-06-15), study Column–Row
Impartial Merge (CRIM). A position is an integer partition $\lambda$, and a move deletes one row
or one column of its Young diagram and reattaches the pieces. Play is normal, so the empty
partition $[\,]$ is a $\mathcal P$-position. Their stacking conjecture (TeX label `conj:bloby`)
reads:

> Let $\lambda$ and $\Gamma_{r,c}$ be losing and suppose $\lambda^*=\Gamma_{r,c}\lhd\lambda$ is
> defined. Then $\lambda^*\in\mathcal P$.

Here $\Gamma_{r,c}=[c,1^{r-1}]$ is a hook and $\lhd$ is the paper's stack, which is defined
through the Durfee length ([details](DETAILS.md#1-the-game-the-stack-and-the-two-conjectures)).
The paper's main conjecture (`conj:main`) reads:

> Every $\mathcal P$-position is of even rank.

Here the rank of $\lambda=[\lambda_1,\dots,\lambda_r]$ is $|r-\lambda_1|$. Both conjectures are
listed as open (see [Sources checked](#sources-checked)).

This directory proves both conjectures in Lean. conj:main follows from a classification of all
$\mathcal P$-positions by boundary words, which Zijian Zeng stated and proved in an unrefereed
preprint; we formalize Zeng's proof. conj:bloby follows from conj:main by a second-player
strategy, which we prove. No human has reviewed this work yet.

## Verified outcomes

The Lean module [`CrimHookStacks.lean`](../../AgenticConjectures/CrimHookStacks.lean)
kernel-checks the following, with no `sorry`, no extra axioms and no `native_decide`.

| Theorem | Statement |
|---|---|
| `statement_holds` | conj:bloby (`statement`). |
| `mainConjecture_holds` | conj:main (`mainConjecture`). |
| `isP_ofPairs_iff` | Zeng's classification: for a partition with run pairs $p=((a_1,b_1),\dots,(a_k,b_k))$, it is a $\mathcal P$-position iff $\ell(\lambda)+\lambda_1$ and the end-peeling statistic $M$ are both even. |
| `statement_of_mainConjecture` | conj:main implies conj:bloby (`mainConjecture → statement`). |
| `isP_stack_of_localEvenRank` | The local form. Let $\lambda\in\mathcal P$, and suppose every partition reached from $\lambda$ by repeating "a move, then a move onto a $\mathcal P$-position" ($\lambda$ itself included) has even rank. Then $\Gamma_{r,c}\lhd\lambda\in\mathcal P$ for every losing hook for which the stack is defined. |
| `stack_hook` | The paper's general stack, specialised to a hook: $\Gamma_{r,c}\lhd\mu$ is defined iff $\ell(\mu)\le r-1$ and $\mu_1\le c-1$, and then it is $[c,1+\mu_1,\dots,1+\mu_k,1^{r-1-k}]$. |
| `isP_hook_iff`, `isP_pair_iff`, `isP_twoCol_iff` | The paper's `lem:hook` and `thm:2parts`, and the two-column case: $\Gamma_{r,c}\in\mathcal P$ iff $r,c\ge2$ and $r\equiv c\pmod 2$; $[a,b]\in\mathcal P$ iff $a$ is even; $[2^a,1^b]\in\mathcal P$ iff $a+b$ is even. |

The reduction is a second-player strategy on $\Gamma_{r,c}\lhd\lambda$. It needs the parity of
$\operatorname{rank}\lambda$ only at two corner shapes, and its induction stays among positions
reachable from $\lambda$. The classification encodes a partition by the run lengths of its
boundary word, identifies CRIM with a game on these run pairs, and shows that the claimed
$\mathcal P$-positions satisfy the game recursion. [DETAILS.md](DETAILS.md) gives both proofs
on paper, with the Lean names. The module also proves a size-bounded form of the reduction
(`statement_of_mainConjecture_le`) and direct proofs for at most two parts or largest part at
most two (`statement_of_length_le_two`, `statement_of_part_one_le_two`), which do not use the
classification.

## Computational evidence

All programs are in [`programs/`](programs/). None of them is used by the Lean proofs.

| Program | What it checks | Log | Result |
|---|---|---|---|
| [`crim_check.py`](programs/crim_check.py) | $\mathcal P/\mathcal N$ for all $\lvert\lambda\rvert\le N$; conj:main; conj:bloby for every pair of $\mathcal P$-positions, with the paper's general stack | [`crim_check_py_n60.log`](logs/crim_check_py_n60.log) | $N=60$: 6,639,349 partitions, 1,870,422 $\mathcal P$, 964,855 defined stacks, 0 failures; 61 s |
| [`crim_check.c`](programs/crim_check.c) | the same, implemented independently (ranked bit table) | [`crim_check_c_n110.log`](logs/crim_check_c_n110.log) | $N=110$: 5,465,153,652 partitions, 1,534,701,211 $\mathcal P$, 783,733,098 defined stacks, 0 failures; 333 s |
| [`strategy_check.py`](programs/strategy_check.py) | replays every case of the proof: each move, the prescribed reply, its shape and its $\mathcal P$-status | [`strategy_check_n60.log`](logs/strategy_check_n60.log) | $N=60$: 964,014 stacks, 150,828,030 replies, 0 failures; 291 s |
| [`boundary_word_check.py`](programs/boundary_word_check.py) | Zeng's boundary-word classification (see below) against the exact table | [`boundary_word_check_n60.log`](logs/boundary_word_check_n60.log) | $N=60$: 0 mismatches; 43 s |

The two solvers agree on the number of partitions and of $\mathcal P$-positions for every
$n\le60$.

## Reproduction

Run these from this directory. The first four are the CI entries in
[`status.yaml`](status.yaml); the runtimes were measured on 2026-10-25 on a shared Apple
silicon machine.

```bash
python3 programs/crim_check.py --max-n 45
```

```bash
mkdir -p /tmp/crim_hook_stacks_build && cc -O2 -std=c99 -o /tmp/crim_hook_stacks_build/crim_check programs/crim_check.c && /tmp/crim_hook_stacks_build/crim_check 70
```

```bash
python3 programs/strategy_check.py --max-n 40
```

```bash
python3 programs/boundary_word_check.py --max-n 45
```

These take about 4 s, 2 s, 5 s and 3 s. The logged runs use `--max-n 60` for the Python
programs and `110` for the C program. The C run at 110 takes about 5.5 minutes and needs about
0.7 GB for its bit table.

## Statement faithfulness

There is no Formal Conjectures statement, so both formal statements (`statement` for conj:bloby,
`mainConjecture` for conj:main) are ours. Each definition was checked against the TeX source;
[DETAILS.md §1.1](DETAILS.md#11-readings) lists every reading.

- Partitions are weakly decreasing lists of positive naturals (`IsPartition`), and $[\,]$ is
  allowed. `part l i` is $\lambda_i$, 1-indexed, and $0$ past the last part.
- Deleting row $i$ is `List.eraseIdx`. Deleting column $j$, for $1\le j\le\lambda_1$, lowers
  every part $\ge j$ by one and drops the zeros (`delCol`).
- `isP` is defined by well-founded recursion on $|\lambda|+\ell(\lambda)$, with $[\,]$ losing.
  "Losing" means $\mathcal P$-position (`IsP`).
- `rank` is $|\ell(\lambda)-\lambda_1|$, as in §2.1 of the paper. The signed difference
  $\lambda_1-\ell(\lambda)$ has the same parity.
- `durfee` is the greatest $d\le\ell(\lambda)$ with $d\le\lambda_d$. No larger $d$ qualifies,
  because $\lambda_d=0$ there.
- `stack` follows the paper's general definition term for term and returns `none` when the
  stack is undefined; $\mu_1=0$ when $\mu=[\,]$. The hook formula is the theorem `stack_hook`,
  not a definition.
- `statement` quantifies over all partitions $\lambda$ and all $r,c\ge1$. Rows ($r=1$) and
  columns ($c=1$) count as hooks, but they are never $\mathcal P$, and for them the stack is
  defined only when $\lambda=[\,]$. $\lambda=[\,]$ is allowed and trivial, because
  $\Gamma_{r,c}\lhd[\,]=\Gamma_{r,c}$.
- The run pairs (`ofPairs`, `PMove`, `endM`) are a device inside the proof. `statement_holds`
  and `mainConjecture_holds` are stated with the definitions above.

## Related work and credits

- **The paper** proves `lem:hook`, `thm:2parts` and `thm:3parts`, checks conj:main for
  $|\lambda|\le50$ and for several families, and observes that conj:bloby implies its
  `prop:hooksquare`. As stated, `thm:3parts` also covers the column $[1,1,1]$, which is
  $\mathcal N$ (see [DETAILS §9](DETAILS.md#9-related-work-and-an-erratum)). Nothing here
  depends on `thm:3parts`.
- **The strategy.** An earlier scouting run of this project sketched the second-player strategy
  and tested it to $n\le40$. This directory completes it and checks it in Lean.
- **S. S. Mehat**, Zenodo
  [10.5281/zenodo.22070744](https://doi.org/10.5281/zenodo.22070744) (2026-08-23; Lean files
  CC0, scripts MIT), classifies the $\mathcal P$-positions with at most six parts and, by
  conjugation, with largest part at most six, and states that all of them have even rank,
  which is conj:main in that range. We have not re-verified the artifact and use no code
  from it.
- **the-omega-institute/trureturing** has Lean refutations of two other conjectures of the
  same paper (`CrimRectairSquareBoundaryRefutation`, `CrimGrundyRefutation`). It has nothing
  on conj:main or conj:bloby.
- **Zijian Zeng**, *A Boundary-Word Classification of Losing Positions in CRIM* (dated
  2026-08-29, unrefereed; GitHub `ArtificialZeng/AI-Has-Taste`, folder
  `reproducible_source_code/BigWIN2/BW2-B02-P10`), states and proves the classification of
  the $\mathcal P$-positions that `isP_ofPairs_iff` formalizes, and derives conj:main from it.
  It does not mention conj:bloby. [DETAILS §7](DETAILS.md#7-conjmain-from-the-boundary-word-classification)
  follows Zeng's lemmas; the Lean proof is ours. `boundary_word_check.py` also compares the
  classification with the exact table for every partition of size at most 60.

No novelty is claimed. No human has reviewed this work, and nothing has been submitted
anywhere.

## Sources checked

Checked on 2026-10-25:

- arXiv lists only v1 of 2606.16828, and OpenAlex lists no work citing it.
- MathDB posts 375370 (conj:main) and 375375 (conj:bloby) are open, with no solutions.
- OpenConjecture lists both conjectures.
- Formal Conjectures has no file, issue or PR about CRIM.
- GitHub code search for "2606.16828" and "Impartial Merge" finds the trureturing files, Zeng's
  repository, teaching material that poses CRIM as an exercise, and catalogue entries that list
  conj:main as open. Zenodo has Mehat's artifact and nothing newer.
