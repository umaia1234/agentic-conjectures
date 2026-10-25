**English** | [한국어](DETAILS.ko.md)

# OOOOOOB, Version C: details of the refutation

This file supports [README.md](README.md). It lists the prior art, the
choices behind the formal statement, the Lean proof step by step, the
computations and their runtimes, and a related check of Version B.

## Prior art

1. **The paper.** Alon Danai, Paul Ellis and Thotsaporn "Aek" Thanatipanonda,
   *Generalizing OOOOOOB*,
   [arXiv:2605.23213v1](https://arxiv.org/abs/2605.23213v1) (math.CO,
   2026-05-22). The conjecture is Conjecture 3.1, at lines 761–765 of the v1
   TeX source; the authors report that they checked it for \(a_i\le5\) and
   \(n\le5\). The arXiv API lists v1 as the only version, and OpenAlex (work
   W7162311448) lists no citing work (both on 2026-10-25).
2. **MathDB post 374893.**
   [Version C's subtract-three conjecture](https://mathdb.com/p/374893/version-c-s-subtract-three-conjecture)
   was created on 2026-08-11. Its only reply, a counterexample by user
   `shivampatel`, was posted on 2026-08-20 at 15:58 UTC and edited at 16:05
   UTC. It gives \(X=(2,2,2,2,2,2,3)\) with the move to \((0,2,2,2,2,2,3)\),
   and \(Y=(2,2,2,2,2,2,4)\), with a Python backward-induction program (35,528
   states for \(X\), 71,835 for both). On 2026-10-25 MathDB showed the post as
   "claimed solved, unverified", with no review and no Lean formalization. The
   refutation is therefore not new; this entry checks it in Lean and adds the
   robustness counts below. No human has reviewed this refutation yet, and
   nothing has been submitted to MathDB, OpenConjecture, the authors or
   anywhere else.
3. **Searches for formal artifacts**, on 2026-10-25 between 15:12 and 15:16
   UTC:

   | Where | Query | Result |
   | --- | --- | --- |
   | Formal Conjectures issues and pull requests | `2605.23213`, `OOOOOOB`, `Thanatipanonda` | none |
   | Formal Conjectures issues and pull requests | `Version C` | one unrelated pull request (#6493, on Erdős problem 559) |
   | Formal Conjectures files at `c094b97` | the three words above | none |
   | GitHub code | `OOOOOOB` | unrelated text only |
   | GitHub code | `2605.23213`, `Generalizing OOOOOOB`, `OOOOOOB conjecture` | nothing relevant |
   | GitHub repositories | `OOOOOOB`, `Generalizing OOOOOOB` | achrafpy/oooooob-conjecture-counterexample (2026-07-29, Version B only) and an unrelated repository |
   | the-omega-institute/trureturing, branch `dev` | its game certificates, and its pull requests that mention 2605.23213, `OOOOOOB` or `Version C` | three Lean files and pull requests #6612, #6846 and #6855 (2026-09-09 and 10), all on Version B |
   | Zenodo | `OOOOOOB`, `"Generalizing OOOOOOB"`, `2605.23213` | none |
   | OpenConjecture | the conjectures of 2605.23213 | conj 2622 (Version C) listed, with no attempt |
   | MathDB search | `OOOOOOB`, `Generalizing OOOOOOB`, `Version C`, `subtract-three` | posts 374891, 374892 and 374893 on this paper; the other hits are about other problems |

   No formal statement or refutation of Version C turned up.

## Faithfulness of the formal statement

There is no Formal Conjectures statement, so the statement in
[`OooooobVersionC.lean`](../../AgenticConjectures/OooooobVersionC.lean) is
ours. Each choice:

- **Positions.** A position is a `Multiset ℕ` of pile sizes, so piles are
  unordered and piles of equal size are interchangeable. `position n a` is
  \(\sum_{i=1}^n\) `Multiset.replicate (a i) i`: exactly `a i` piles of size
  `i` for \(1\le i\le n\), and no pile larger than \(n\) (the paper's "\(a_1,\dots,a_n\)
  piles of size \(1,\dots,n\)"). Values of `a` outside \([1,n]\) are ignored.
- **Moves.** `Move s t` holds when
  \(s=(a+1)::r\) and \(t=a::r\) (one token from one pile of positive size),
  or \(s=(a+1)::(b+1)::r\) and \(t=a::b::r\) (one token from each of two
  piles of positive size). The two piles are two different elements of the
  multiset, and \(a=b\) is allowed, so two piles of the same size can be
  used together.
- **Empty piles.** An emptied pile stays as an element 0, which no move can
  use. `isP_zero_cons : IsP (0 ::ₘ s) ↔ IsP s` proves that such piles change
  no outcome, so the outcomes agree with the game in which empty piles
  disappear. The positions of `statement` have no pile of size 0.
- **Outcomes.** `IsP s` is defined by well-founded recursion on `s.sum`:
  `IsP s ↔ ∀ t, Move s t → ¬ IsP t` (`isP_iff`). Every move lowers the
  number of tokens by one or two (`Move.sum_lt`). A position without moves,
  such as the empty one, is a P-position: normal play.
- **The exception** is the single position `{1, 1, 2, 2, 3, 3, 3}`; the
  hypothesis is `position n a ≠ exception`.
- **The claim** is `IsP (position n a) ↔ 3 ∣ (position n a).sum`, where the
  sum of the multiset is the number of tokens.
- **\(n\ge3\).** Read literally, the conjecture covers every \(n\). For
  \(n=0\) and \(n=1\) it holds: the empty position is a P-position with 0
  tokens, and with piles of size 1 only, a move removes one or two piles, so
  \(a_1\) such piles form a P-position exactly when \(3\mid a_1\). For \(n=2\) it
  fails: in \((2,a_2)\), taking one token from each pile of size 1 leaves only
  piles of size 2, a P-position, so \((2,a_2)\) is an N-position, while
  \(2+2a_2\) is divisible by 3 when \(a_2\equiv2\pmod3\).
  `two_counterexample` proves this for \((2,2)\), the position
  \(1,1,2,2\). The paper's lemma on piles of size at most 3 (TeX line 626)
  lists exactly these positions, \((a_1,a_2,a_3)=(2,3k+2,0)\), among its
  exceptions, so the authors presumably mean \(n\ge3\); their own exception
  \((2,2,3)\) has \(n=3\). `statement` assumes \(3\le n\). This only weakens
  it, so `not_statement` refutes the literal reading as well.
- **Gaps.** The paper's last lemma notes that the pattern fails when
  \(a_2=\dots=a_{n-1}=0\). Such positions do not satisfy \(a_i\ge2\); \(X\) and
  \(Y\) satisfy every hypothesis.

## The Lean proof

All declarations are in the namespace `AgenticConjectures.OooooobVersionC`.

### Even piles

`isP_of_even` is the paper's proposition: a position whose piles all have
even size is a P-position. After a move, one or two piles have odd size,
hence positive size, and taking one token from each of them gives a position
with even piles again, which is a P-position by induction on the number of
tokens. The proof follows this argument, with the two move shapes as two
cases.

### Packed positions and move codes

The kernel checker in
[`Checker.lean`](../../AgenticConjectures/OooooobVersionC/Checker.lean) uses no
imports and works on natural numbers.

- `wt x` is 0 for \(x=0\) and \(32^{x-1}\) otherwise, and the packed form of a
  position is `enc s = (s.map wt).sum`.
- `cnt k x` is the base-32 digit \(x-1\) of \(k\), that is
  \(\lfloor k/32^{x-1}\rfloor \bmod 32\).
- A move code is \(c=8x+y\) with \(x=\lfloor c/8\rfloor\) and \(y=c\bmod 8\).
  `legal k c` requires \(8\le c<64\) and: `cnt k x ≥ 1` if \(y=0\) (one pile of
  size \(x\)); `cnt k x ≥ 2` if \(x=y\); `cnt k x ≥ 1` and `cnt k y ≥ 1`
  otherwise (two different piles of sizes \(x\) and \(y\)).
- `app k c = k + wt (x-1) + wt (y-1) - wt x - wt y` replaces the piles of
  sizes \(x\) and \(y\) by piles of sizes \(x-1\) and \(y-1\). Since `wt 0 = 0`,
  the code \(y=0\) touches one pile only.
- `moveCodes` lists the 35 codes \(8x\) and \(8x+y\) with \(1\le x\le y\le7\).
- `allEven k` says that the digits of the sizes 1, 3, 5 and 7 are 0.

`Small s` says that every pile has size at most 7 and that there are fewer
than 32 piles; every move keeps a position small (`Move.small`). The bridge
lemmas are:

- `enc_eq`: for piles of size at most 7, `enc s` is
  \(\sum_{x=1}^7 32^{x-1}\cdot\) `s.count x`;
- `cnt_enc`: for a small `s` and \(1\le x\le7\), `cnt (enc s) x = s.count x`.
  Each count is below 32 because the number of piles is, so the base-32
  digits do not overflow;
- `Move.code`: every move `s → t` of a small `s` has a code \(c\) in
  `moveCodes` with `legal (enc s) c` and `enc t = app (enc s) c`;
- `move_of_legal`: for every code \(c\) with `legal (enc s) c` there is a move
  `s → t` with `enc t = app (enc s) c`. This direction allows any legal
  \(c<64\), including codes with \(y<x\), which replies may use;
- `even_of_allEven`: if `allEven (enc s)` holds for a small `s`, every pile
  of `s` has even size.

### Certificates and their soundness

A certificate is a binary search tree `Tree` whose node stores a packed
position `key` and a number `reps`. `checkMoves root y moveCodes R` runs
through the codes \(m\) of `moveCodes` in order. For each \(m\) legal in
\(y\), it reads the next base-64 digit \(r\) of \(R\) and requires that \(r\)
is legal in `app y m` and that `app (app y m) r` is all-even or a key of
`root`. `allOk root t` checks every node of `t` in this way against the whole
tree `root`.

`isP_of_cert` states: if `allOk root root = true`, every small `s` whose
packed form is a key of `root` is a P-position. The proof is by strong
induction on the number of tokens. Let `s → t` be a move and suppose `t` is
a P-position.

1. `Move.code` gives a code \(c\in\) `moveCodes` that is legal in `enc s`,
   with `enc t = app (enc s) c`.
2. `exists_of_mem` finds the node of `enc s`, and `checkMoves_spec` gives a
   reply \(r\) legal in `enc t` that leads to an all-even packed position or
   to a key.
3. `move_of_legal` turns \(r\) into a move `t → u`.
4. If the result is all-even, `u` is a P-position by `even_of_allEven` and
   `isP_of_even`. Otherwise `enc u` is a key, `u` is small, and `u` has fewer
   tokens than `s`, so `u` is a P-position by induction.

Either way `t` has a move to a P-position, which contradicts `IsP t`. So
every move from `s` leads to an N-position, and `s` is a P-position. Since
`moveCodes` covers every move of a small position (`Move.code`), the checker
cannot skip a move.

### The counterexamples

- \(X\) is `position 7 countsX`, which `decide` evaluates to the multiset
  `{1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 7}`. `move_X` takes one token
  from each pile of size 1 and reaches `X0 = {0, 0, 2, 2, 3, 3, …, 7, 7, 7}`,
  whose packed form is 3290499136 (by `decide`), a key of `certX`
  (`certX_mem`). So `X0` is a P-position (`isP_X0`), and \(X\) is not
  (`not_isP_X`).
- \(Y\) is `position 7 countsY`, with packed form 4364240962, a key of
  `certY` (`certY_mem`), so it is a P-position (`isP_Y`).
- `X_counterexample` and `Y_counterexample` also check the hypotheses
  \(a_i\ge2\) for \(1\le i\le7\), the inequality with the exception, and the
  numbers of tokens, 63 and 70. `not_statement` applies the statement to
  \(X\) with \(n=7\); `not_statement_of_Y` applies it to \(Y\).

### The kernel check

The checker functions use `Bool.rec` (through `pick`), `List.rec`, `Tree.rec`
and the `Nat` primitives, which the kernel evaluates with GMP, instead of
`if`, `match` and arithmetic notation. On `CertX` this made `decide +kernel`
about 2.6 times faster (53.5 s against 20.2 s in a benchmark). Each
certificate is split at a fixed depth of the search tree into subtrees, 8 for
`CertX` and 16 for `CertY`. Each subtree is a separate definition with its
own `decide +kernel` theorem, and `allOk_node` assembles the top of the
tree, where each node's `checkMoves` is also checked by `decide +kernel`.

| Module | Size | Positions | Replies | Compile time |
| --- | ---: | ---: | ---: | ---: |
| `Checker` | 5 kB | | | 0.2 s |
| `CertX` | 246 kB | 4,410 | 72,523 | 18–20 s |
| `CertY` | 562 kB | 9,461 | 170,442 | 44–48 s |
| `OooooobVersionC` | 25 kB | | | 4–6 s |

The times are for an Apple M5 Max shared with other jobs. `CertX` and
`CertY` build in parallel, so `lake build AgenticConjectures.OooooobVersionC`
takes about 1 minute of wall time once mathlib is built. `#print axioms`
gives `propext`, `Classical.choice` and `Quot.sound` for the main theorems
and no axiom for `certX_ok` and `certY_ok`.

### How the certificates are built

[`gen_certificate.py`](gen_certificate.py) (standard library only) computes
outcomes with its own memoized solver over packed keys, then builds the set
\(S\) of keys and their replies.

1. **Greedy closure.** Starting from the root (`X0` or \(Y\)), it processes
   the positions of \(S\) in breadth-first order. For each move \(y\to z\), it
   looks at the replies of \(z\) that lead to P-positions. If one of them
   leads to an all-even position or into \(S\), nothing is added. Otherwise
   it adds the P-position that comes first in a fixed order: most tokens
   first for `X0`, fewest piles first for \(Y\).
2. **Shrinking.** It then fixes a reply rule: an all-even target if there is
   one; otherwise the member of \(S\) that the most replies could use;
   otherwise the target with the fewest moves. It recomputes \(S\) as the set
   of positions reached from the root under this rule. This repeats until
   \(S\) no longer changes (at most 50 rounds).
3. **Output.** Every reply is checked to be legal and to lead to a
   P-position in \(S\) or to an all-even position. The keys are written as a
   balanced search tree, and the replies of each key are packed in base 64 in
   the order of `moveCodes`.

The kernel check does not trust any of this: it re-checks every reply.
`python3 gen_certificate.py --check` (about 8 s) rebuilds both modules and
compares them with the committed files character for character; `--write`
overwrites them.

## Computational cross-checks

These checks are supporting evidence; the Lean proof does not depend on them.
The two solvers share no code.

- [`oooc_counts.cpp`](oooc_counts.cpp) (C++17) packs the counts
  \(a_1,\dots,a_N\) into 6 bits each (\(N\le10\), at most 63 piles of each
  size), and memoizes outcomes in an open-addressing hash table. A position
  is P when no option is P; the search stops at the first P option.
- [`oooc_tuples.py`](oooc_tuples.py) (standard library) represents a position
  as the sorted tuple of its non-empty pile sizes and memoizes outcomes in a
  dictionary.

| Check | `oooc_counts.cpp` | `oooc_tuples.py` |
| --- | --- | --- |
| \(X\), \(Y\), \((2,2,2,2,2,3,3)\), \((2,2,2,2,2,3,4)\), \((0,2,2,2,2,2,3)\) | N, P, N, P, P | N, P, N, P, P |
| \(n=7\), \(a_i\in[2,4]\): failures among 2,187 | 15 | 15 (same list) |
| \(n=6\), \(a_i\in[2,8]\): failures among 117,649 | 0 | 0 |
| \(n=9\), \(a_i=3\): outcome (135 tokens) | N | N |
| Runtime | CI mode 0.4 s | CI mode 22 s; `--full` 152 s; \(n=9\), \(a_i=3\): 391 s |

The CI mode of the C++ solver includes the \(n=6\) box; the Python solver
adds it with `--full`. The Python solver also reports that \(X\) has 10
different moves to P-positions. The C++ solver finds no failure for
\(n=3,4,5\) with every \(a_i\in[2,8]\), and 3 failures for \(n=2\) in that
range, \((2,2)\), \((2,5)\) and \((2,8)\), the positions discussed in the
faithfulness section.

## Robustness of the failure

The paper motivates the conjecture by "sufficient piles of each size".
To see whether a larger lower bound on the \(a_i\) rescues it, we counted the
failures among the positions with every \(a_i\) in a box \([lo,hi]\), with
`oooc_counts box n lo hi`. The threshold is \(t=lo\). This is
computer-assisted and not formalized; one row is also confirmed by the
Python solver, as marked.

| \(n\) | \(t\) | Box | Positions | Failures | N with \(3\mid\) tokens | P with \(3\nmid\) tokens | Time |
| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 7 | 2 | \([2,4]\) | 2,187 | 15 | 12 | 3 | < 0.5 s |
| 7 | 2 | \([2,5]\) | 16,384 | 48 | 36 | 12 | 0.4 s |
| 7 | 3 | \([3,5]\) | 2,187 | 0 | | | 0.4 s |
| 7 | 3 | \([3,6]\) | 16,384 | 0 | | | 1.1 s |
| 7 | 4 | \([4,7]\) | 16,384 | 0 | | | 3.1 s |
| 7 | 5 | \([5,8]\) | 16,384 | 0 | | | 7.1 s |
| 8 | 2 | \([2,4]\) | 6,561 | 711 | 442 | 269 | 1.4 s |
| 8 | 3 | \([3,5]\) | 6,561 | 0 | | | 6.1 s |
| 8 | 4 | \([4,6]\) | 6,561 | 0 | | | 21 s |
| 8 | 5 | \([5,7]\) | 6,561 | 0 | | | 69 s |
| 9 | 2 | \([2,3]\) | 512 | 333 | 173 | 160 | 2.2 s |
| 9 | 3 | \([3,4]\) | 512 | 20 | 16 | 4 | 18 s |
| 9 | 3 | \([3,3]\) | 1 | 1 (also Python) | 1 | 0 | in \([2,3]\) |
| 9 | 4 | \([4,5]\) | 512 | 0 | | | 81 s |
| 9 | 5 | \([5,5]\) | 1 | 0 | | | in \([4,5]\) |
| 10 | 3 | \([3,3]\) | 1 | 1 | 1 | 0 | 13 s |
| 10 | 3 | \([3,4]\) | 1,024 | 593 | 318 | 275 | 378 s |
| 10 | 4 | \([4,4]\) | 1 | 0 | | | in \([3,4]\) |

Rows marked "in \([lo,hi]\)" are read off the failure list of that larger
box. Every failure in the \(n=9\) and \(n=10\) boxes with \(lo=3\) has some
\(a_i=3\). The largest runs need a lot of memory: the \(n=10\), \([3,4]\) box
memoized \(1.25\times10^9\) positions in a hash table of about 34 GB, and the
\(n=8\), \([5,7]\) and \(n=9\), \([4,5]\) boxes about \(3\times10^8\) each.

What the table shows, and no more:

- With \(t=2\), the conjecture fails for every \(n\) from 7 to 10 that we
  tried, and the share of failures grows with \(n\).
- With \(t=3\), the boxes for \(n=7\) and \(n=8\) have no failure, but
  \(n=9\) and \(n=10\) do, including the position with every \(a_i=3\).
- With \(t=4\) and \(t=5\), no box we finished has a failure, but these
  boxes stop at \(n=9\) (one position for \(t=5\)) and at the single position
  \(a_i=4\) for \(n=10\).

So a threshold that works for small \(n\) fails for larger \(n\) in the one
case we could test, and we found no evidence of a fixed threshold that rescues
the conjecture. We do not claim that the conjecture fails for every \(t\).

## Related: Version B, Conjecture 2.2 (computer-checked only)

In Version B a move takes one token from one pile, or one token from every
non-empty pile. Conjecture 2.2 of the paper (TeX lines 534–536) says that for
\(n\ge3\) and \(a_n\ge2n-4\), the outcome depends only on the parities of
\(a_1,\dots,a_{n-1}\). The reply of user `shivampatel` (2026-08-22) to
[MathDB post 374892](https://mathdb.com/p/374892/the-eventual-parity-conjecture-for-positions-with-many-large)
refutes it with \(n=7\) and \(a_7=10=2\cdot7-4\):
\((0,1,0,0,0,0,10)\) is a P-position and \((0,1,0,0,0,4,10)\) an N-position,
although \(a_1,\dots,a_6\) have the same parities. The reply also gives
\((0,1,0,0,0,4,11)\), again a P-position: with \(a_1,\dots,a_6\) fixed, the
outcome still changes with \(a_7\) above the threshold. MathDB lists the post
as "partial progress", with an unverified reply and no review (2026-10-25).

With `--version-b`, both solvers here compute the outcomes of these three
positions under the Version B rules and find P, N and P (each in under 1 s).
This is a computer check only. It is not formalized, it is not part of the
claim of this entry, and the credit for the counterexample belongs to the
MathDB reply.
