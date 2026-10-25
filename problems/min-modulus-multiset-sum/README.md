**English** | [한국어](README.ko.md)

# Fonollosa's Conjecture 1: the minimum modulus for unique multiset sums

A set $A=\{a_0,\dots,a_{n-1}\}$ of $n$ distinct residues mod $N$ is **valid**
if the all-ones vector is the only $k\in\mathbb Z_{\ge0}^n$ with

$$\sum_i k_i=n,\qquad \sum_i k_ia_i\equiv\sum_i a_i\pmod N .$$

In other words, the all-ones multiset is the only multiset of size $n$ drawn
from $A$ whose sum is $\sum A$ mod $N$. Validity is unchanged by
translations and by multiplication by units (affine maps $x\mapsto ux+v$),
and subsets of valid sets are valid.

J. A. R. Fonollosa,
[*Minimum modulus for the unique multiset-sum problem*](https://arxiv.org/abs/2607.08366)
(arXiv:2607.08366v2, 14 Jul 2026), proves that the super-increasing set
$\{2^k-1:0\le k\le n-1\}$ is valid mod $N=2^n-2^{\lfloor\log_2n\rfloor}$
and at no smaller modulus. The author also formalized this in Lean. The paper
conjectures that no set does better (Conjecture 1, §1):

$$n\ge2,\quad N<2^n-2^{\lfloor\log_2n\rfloor}\ \Longrightarrow\ \text{no } n\text{-subset of }\mathbb Z_N\text{ is valid.}$$

The values $2^n-2^{\lfloor\log_2n\rfloor}$ for $n=2,\dots,13$ are
$2,6,12,28,60,124,248,504,1016,2040,4088,8184$. The
[formal-conjectures statement](upstream/README.md) (Apache-2.0), which we
copy, phrases it as:

> For every $n \geq 2$ and every $N < 2^n - 2^{\lfloor \log_2 n\rfloor}$, no
> set of $n$ residues mod $N$ is valid.

The conjecture remains **open**. This directory records partial results,
labelled `partial`.

## Results

### Lean (kernel-checked; no `sorry`, extra axioms or `native_decide`)

[`MinModulusMultisetSum.lean`](../../AgenticConjectures/MinModulusMultisetSum.lean)
proves, for every valid $A\subseteq$ `ZMod N` with $N>0$ and $|A|=n$:

| Declaration | Statement | Remark |
|---|---|---|
| `IsValidMod.two_pow_le` | $2^{n-1}\le N$ | the translated subset sums are distinct; cyclic case of Inal's theorem |
| `IsValidMod.card_mul_card_sub_one_le` | $n(n-1)\le N$ | Sidon-type: $x+w=y+z$, $x\ne w$ forces $\{x,w\}=\{y,z\}$ |
| `IsValidMod.two_pow_add_le` | $2^{n-1}+n-2\le N$ for $n\ge2$ | the doubled differences $2(b-a_0)$ avoid the nonempty translated subset sums |
| `statement_of_le_four` | Conjecture 1 for $n\le4$ | there $2^n-2^{\lfloor\log_2n\rfloor}=n(n-1)$ |

The proofs are written out in [DETAILS.md](DETAILS.md). `statement` itself
is not proved.

### Exhaustive search for $n\le9$ (two independent implementations)

For every $3\le n\le9$ and every modulus $n\le N\le2^n+8$, both programs
listed all valid $n$-sets mod $N$ up to affine maps, and they agree on every
modulus:

| $n$ | conjectured minimum | moduli $N\le2^n+8$ with a valid $n$-set (number of affine orbits if $>1$) | run time `mmsearch` / `mmcheck` |
|---|---|---|---|
| 3 | 6 | 6, 7, 8 (2), 9, 10 (2), 11, 12 (5), 13 (2), 14 (4), 15 (4), 16 (6) | < 0.1 s / < 0.1 s |
| 4 | 12 | 12, 14 (2), 15 (2), 16 (3), 17, 18 (8), 19 (2), 20 (10), 21 (8), 22 (11), 23 (5), 24 (31) | < 0.1 s / < 0.1 s |
| 5 | 28 | 28, 30 (5), 31, 32 (4), 34 (7), 35, 36 (29), 37 (2), 38 (22), 39 (11), 40 (45) | < 0.1 s / < 0.1 s |
| 6 | 60 | 60, 62 (2), 63, 64 (2), 68 (6), 70 (6), 72 (61) | < 0.1 s / < 0.1 s |
| 7 | 124 | 124, 126, 127, 128 | 0.2 s / 0.2 s |
| 8 | 248 | 248, 252, 254 (2), 255, 256 | 18.7 s / 37.6 s |
| 9 | 504 | 504, 508, 510, 511, 512 | 6519 s / 15753 s |

Run times are summed over the moduli. `mmsearch` times each modulus by wall
clock, and `mmcheck` by process CPU time.

Consequences, for every $n\le9$:

- **Conjecture 1 holds**: no valid $n$-set exists mod $N$ for any
  $N<2^n-2^{\lfloor\log_2n\rfloor}$.
- **At the conjectured minimum the extremal set is unique**: mod
  $N=2^n-2^{\lfloor\log_2n\rfloor}$ every valid $n$-set is an affine image
  of $\{2^k-1\}$. This is the paper's Open Problem 2 for $n\le9$.
- **The set of valid moduli has gaps.** For example, no 4-set is valid mod
  13, no 5-set mod 29 or 33, and for $n=7,8,9$ only four or five moduli up to
  $2^n+8$ admit a valid set. The second orbit mod 254 for $n=8$ is
  $\{0,1,64,96,112,120,124,126\}$.

### What goes beyond the sources, and what reproduces them

- The paper certifies Conjecture 1 for $n\le7$ with CP-SAT (one
  infeasibility certificate per modulus). For $n\le13$ it reports solver and
  GPU searches that found no valid set below the conjectured minimum, and
  that every minimal solution they found reduces to the super-increasing
  set. Our cases $n\le7$ reproduce the certified range. Our cases $n=8,9$,
  and the uniqueness at the minimum for $n\le9$, are exhaustive where the
  paper's evidence is a search.
- $2^{n-1}\le N$ reproduces M. Inal's bound (below) for cyclic groups.
  Lemma 5 of [DETAILS.md](DETAILS.md) is the argument Inal uses for the
  equality case. Theorem 3 ($2^{n-1}+n-2$) adds a count of the doubled
  differences to it. The Sidon-type bound $n(n-1)$ is elementary. We did not
  find these two bounds in the sources below, but claim no novelty.
- Conjecture 1 for $n\le4$ is inside the CP-SAT range. What is new for these
  cases is a kernel-checked proof for the upstream definition.

## Lower bounds on record, and the remark that one "appears to be open"

Open Problem 1 of v2 remarks that even an exponential lower bound
$N_{\min}\ge c^n$ valid for all sets appears to be open. Under the paper's
definition, a valid $n$-set satisfies $N\ge2^{n-1}$. That definition is
encoded by the upstream Lean definition, which we use unchanged, and
`IsValidMod.two_pow_le` above is a kernel-checked proof. The translated
differences $a-a_0$ have pairwise distinct subset sums: a coincidence
$\sigma(S)=\sigma(T)$ between disjoint $S,T$ is turned into a rival
multiset.

This is the argument of M. Inal,
[*The Exact Minimum Order for Unique Multiset Sums in Finite Abelian Groups*](https://doi.org/10.17605/OSF.IO/C58Q9)
(OSF preprint dated 21 Jul 2026, a week after v2). Inal proves
$|G|\ge2^{n-1}$ for every finite abelian group $G$, with equality only for
$(\mathbb Z/2)^{n-1}$, which settles Problem 4 of the paper. For cyclic $G$
and $n\ge3$ this gives $N\ge2^{n-1}+1$. Problem 4 of v2 itself already quotes
another exponential bound, $\binom{2n}{n}/2^n\sim2^n/\sqrt{\pi n}$, from the
paper's companion work. The author's repository
[jarfo/min-modulus](https://github.com/jarfo/min-modulus) formalizes Inal's
theorem in `MinModulus/AbelianMin.lean` (commits of 22 Jul 2026). Its README
describes Problem 4 as settled and Conjecture 1 as open.

So our reading of validity agrees with the paper's, and the remark predates
Inal's preprint. All bounds known to us are far below the conjectured
$2^n-2^{\lfloor\log_2n\rfloor}$.

## Search method

Both programs enumerate, for each divisor $d<N$, sorted sets
$\{0<d<a_2<\dots\}$ in which $d$ is the smallest $\gcd(x-y,N)$ over pairs,
every pairwise difference has $\gcd\ge d$, and no *normalized image*
$u(A-p)$ has an element strictly between $d$ and $a_2$. Here $p,q\in A$,
$\gcd(q-p,N)=d$, and $u$ is a unit with $u(q-p)=d$. Every affine orbit of
valid sets meets this family (§5 of [DETAILS.md](DETAILS.md)). Validity is
hereditary, so the depth-first searches extend only valid prefixes, and they
prune a prefix once one of its normalized images violates the condition on
$a_2$.

- [`mmsearch.cpp`](mmsearch.cpp) (C++, threads) adds elements in increasing
  order. It keeps the $j$-fold multiset sumsets of the prefix as bitsets and
  tests an extension $P\cup\{x\}$ by $x+s\notin(k+1)P$ and
  $s-gx\notin(k-g)P$ for $1\le g\le k$. It also keeps the list of
  normalizing maps.
- [`mmcheck.c`](mmcheck.c) (C) was written separately. It counts multisets
  directly (capped tables of the number of size-$j$ multisets with each
  sum), adds elements after $a_2$ in decreasing order, and recomputes
  canonicity from scratch at every node.
- [`brute.py`](brute.py) tests every subset containing $0$, with no
  reduction, and collapses the valid ones into affine orbits.
- [`verify_search.py`](verify_search.py) parses the committed logs of both
  programs for $n=3,\dots,9$. It requires both to cover every modulus and to
  report the same orbits. It re-checks in Python that every reported set is
  valid, and checks Conjecture 1 and the uniqueness at the minimum. By
  default it also recompiles both programs, reruns $n\le7$ against the
  logs, and runs the brute force for $n\le5$ ($N\le16,24,30$).

The logs for $n\le8$ come from the committed sources compiled with
`g++ -O3 -std=c++17 -pthread` and `gcc -O3 -std=c11`. The $n=9$ runs used
binaries that are byte-identical to `clang++ -O3 -march=native -std=c++17`
and `clang -O3 -march=native -Wall -Wextra` builds of the committed sources.
`mmsearch` ran on 2 threads (54 min wall, $4.1\cdot10^9$ nodes). `mmcheck`
ran as three single-threaded processes over the consecutive ranges
$9..473$, $474..501$ and $502..520$ (1 h 53 min wall), and their outputs are
concatenated in [`logs/mmcheck_n9.txt`](logs/mmcheck_n9.txt). The first
process started on $9..504$ and was stopped after $N=473$ to rebalance the
load. The machine was an Apple M5 Max, shared with other jobs.

## Reproduction

From the repository root:

```bash
python3 problems/min-modulus-multiset-sum/verify_search.py
```

This is the CI check: all logs, a fresh run of both programs for $n\le7$,
and the brute force for $n\le5$. It took about 4 s locally.

```bash
python3 problems/min-modulus-multiset-sum/verify_search.py --recompute 8 --no-brute
```

This reruns $n=8$ with both programs, in about 1 minute (53 s locally).

```bash
python3 problems/min-modulus-multiset-sum/verify_search.py --recompute 9 --threads 3 --no-brute
```

This reruns $n=9$. It needs about 1.8 single-thread hours for `mmsearch`
and 4.4 for `mmcheck`, spread over the requested threads (roughly 2 hours
wall with 3 threads).

```bash
lake build AgenticConjectures.MinModulusMultisetSum
```

This builds the Lean module, in about 5 s once mathlib is built.

## Statement faithfulness

- `IsValidMod` and `minModulus` are the upstream definitions term for term.
  `statement` is the proposition of the upstream theorem `min_modulus` word
  for word. The adaptations needed to build without `FormalConjecturesUtil`
  (namespace, attributes, module header, `def statement` instead of a
  sorry-backed theorem) are listed in the module docstring.
- `A : Finset (ZMod N)` with `#A = n` is a set of $n$ distinct residues, as
  in the paper. The multiplicity function `m : ZMod N → ℕ` matters only on
  `A`.
- `Nat.log 2 n` is $\lfloor\log_2n\rfloor$ for $n\ge1$. The natural-number
  subtraction in `minModulus` is exact, since $2^{\lfloor\log_2n\rfloor}\le n<2^n$.
- `0 < N` excludes `ZMod 0 = ℤ`, as upstream. $N=1$ is vacuous, because
  `ZMod 1` has no 2-element subset.
- The bounds hold for every $N>0$ and every valid `A`. The searches work with
  residues $0,\dots,N-1$, and their correctness rests on the argument in
  [DETAILS.md](DETAILS.md) §5 and on the cross-checks. The programs are not
  formally verified, and the search results are not imported into Lean.

## Not claimed

- No proof of Conjecture 1 for $n\ge10$, or in general.
- No novelty or priority. Nothing has been reported to the author or
  submitted to formal-conjectures; external submissions need human approval.

## Sources checked (2026-10-24)

- arXiv:2607.08366v2, §1 (Conjecture 1), §7 (machine certification) and §8
  (open problems).
- M. Inal, OSF preprint, doi:10.17605/OSF.IO/C58Q9.
- [jarfo/min-modulus](https://github.com/jarfo/min-modulus) at
  `e7c78dd63955092b5f8d8a5fa826476337c0f4be` (README and
  `MinModulus/AbelianMin.lean`).
- arXiv API and OpenAlex searches for the problem and for works citing
  arXiv:2607.08366. They found no citing work and no other paper on the
  conjecture.
- formal-conjectures at `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`, where
  `min_modulus` is tagged `research open`.
