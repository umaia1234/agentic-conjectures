**English** | [한국어](README.ko.md)

# OOOOOOB, Version C: the subtract-three conjecture

The conjecture is due to Alon Danai, Paul Ellis and Thotsaporn "Aek"
Thanatipanonda: it is Conjecture 3.1, about Version C, of *Generalizing
OOOOOOB* ([arXiv:2605.23213v1](https://arxiv.org/abs/2605.23213v1)). The first
public counterexample we know of is the reply of MathDB user `shivampatel`
(2026-08-20) to
[MathDB post 374893](https://mathdb.com/p/374893/version-c-s-subtract-three-conjecture),
which MathDB marks as unverified. This entry adds a Lean-checked refutation
and independent computational checks. It claims no novelty.

## The game

OOOOOOB ("one or one or one of both") is a classic two-pile game: a move takes
a token from one pile, or one token from each pile, and the player who makes
the last move wins. The paper generalizes it to any number of piles in three
ways. In **Version C** a move does one of the following:

- take one token from one pile;
- choose two different non-empty piles and take one token from each.

The two piles may have the same size. The player who cannot move loses (normal
play). A *P-position* is a position that the player to move loses with perfect
play; every other position is an *N-position*. The paper shows that a position
whose piles all have an even number of tokens is a P-position.

We write \((a_1,\dots,a_n)\) for the position with exactly \(a_i\) piles of
size \(i\), for \(1\le i\le n\), and no other piles.

## The conjecture

**Conjecture 3.1** (lines 761–765 of the v1 TeX source, paraphrased). Let
\((a_1,\dots,a_n)\) be a position with \(a_i\ge2\) for every \(1\le i\le n\),
other than \(1,1,2,2,3,3,3\), that is \((a_1,a_2,a_3)=(2,2,3)\). Then it is a
P-position if and only if its number of tokens \(\sum_i i\,a_i\) is divisible
by 3.

The paper explains the conjecture by a lemma on positions whose piles have at
most 3 tokens: with enough piles of every size, Version C should behave like
the subtraction game in which a move removes 1 or 2 tokens. The authors report
that they checked the conjecture for \(a_i\le5\) and \(n\le5\).

Read literally, the statement also covers \(n=2\), where it fails for a simple
reason that the paper's own lemma records; so we read it with \(n\ge3\) (see
[Statement faithfulness](#statement-faithfulness)).

## Result

**Theorem (Lean).** The conjecture is false, in both directions.

| Position \((a_1,\dots,a_7)\) | Tokens | Mod 3 | Conjecture | Actual |
| --- | ---: | ---: | :---: | :---: |
| \(X=(2,2,2,2,2,2,3)\) | 63 | 0 | P | **N** |
| \(Y=(2,2,2,2,2,2,4)\) | 70 | 1 | N | **P** |

Both positions satisfy every hypothesis. \(X\) is an N-position because taking
one token from each of its two piles of size 1 leads to \((0,2,2,2,2,2,3)\),
which is a P-position. That position has no pile of size 1, so the conjecture
says nothing about it.

These are the two counterexamples of the MathDB reply; see
[Prior art and status](#prior-art-and-status). No human has reviewed this
refutation yet.

## Proof idea

The Lean file defines the game itself, on multisets of pile sizes, and proves
the two outcomes with two finite certificates checked by the kernel.

1. **Certificates.** Let \(S\) be a finite set of positions. Suppose that for
   every \(y\in S\) and every move \(y\to z\) there is a reply \(z\to w\) with
   \(w\in S\) or with all piles of \(w\) even. Then every position of \(S\) is a
   P-position: by induction on the number of tokens, every move from \(y\)
   allows a reply to a P-position. This is `isP_of_cert`.
2. **Packed positions.** Every position that occurs has piles of size at most 7
   and fewer than 32 piles. Such a position is stored as the number whose
   base-32 digit \(x-1\) is the number of piles of size \(x\), and a move as a
   code \(8x+y\). The certificate is a binary search tree of packed positions;
   each node stores one reply code for each legal move.
3. **The bridge.** `cnt_enc`, `Move.code` and `move_of_legal` prove that the
   moves of a position are exactly the legal move codes of its packed form, so
   the kernel's check of the tree transfers to the game.
4. **The two certificates.** `CertX` has 4,410 positions with 72,523 replies
   and contains \((0,2,2,2,2,2,3)\). `CertY` has 9,461 positions with 170,442
   replies and contains \(Y\). Each is checked by `decide +kernel`, one subtree
   per theorem.

[DETAILS.md](DETAILS.md) gives the definitions, the bridge lemmas and the
construction of the certificates.

## Lean formal proof

[`AgenticConjectures/OooooobVersionC.lean`](../../AgenticConjectures/OooooobVersionC.lean)
proves `not_statement : ¬ statement`. The kernel checker is in
[`OooooobVersionC/Checker.lean`](../../AgenticConjectures/OooooobVersionC/Checker.lean),
and the certificates are in
[`OooooobVersionC/CertX.lean`](../../AgenticConjectures/OooooobVersionC/CertX.lean)
and
[`OooooobVersionC/CertY.lean`](../../AgenticConjectures/OooooobVersionC/CertY.lean),
which [`gen_certificate.py`](gen_certificate.py) generates. There is no
`sorry`, no extra axiom and no `native_decide`, `decide +native`,
`ofReduceBool` or `ofReduceNat`. `#print axioms` lists only `propext`,
`Classical.choice` and `Quot.sound` for the theorems below, and no axiom at
all for `certX_ok` and `certY_ok`.

| Declaration | Content |
| --- | --- |
| `Move`, `IsP`, `isP_iff` | The moves of Version C on a multiset of pile sizes, and the P-positions, by well-founded recursion on the number of tokens (`Move.sum_lt`). |
| `isP_zero`, `isP_zero_cons` | The empty position is a P-position; a pile of size 0 changes no outcome. |
| `isP_of_even` | A position whose piles all have even size is a P-position. |
| `position`, `exception`, `statement` | The position \((a_1,\dots,a_n)\), the excluded position, and Conjecture 3.1. |
| `not_statement`, `not_statement_of_Y` | The conjecture is false; the first proof uses \(X\), the second \(Y\). |
| `two_counterexample` | Read literally with \(n=2\), the conjecture fails at \((a_1,a_2)=(2,2)\). |
| `X_counterexample`, `Y_counterexample` | \(X\) and \(Y\) meet every hypothesis; \(X\) has 63 tokens and is an N-position; \(Y\) has 70 tokens and is a P-position. |
| `move_X`, `isP_X0`, `not_isP_X`, `isP_Y` | \(X\to(0,2,2,2,2,2,3)\) is a move to a P-position, and \(Y\) is a P-position. |
| `enc`, `Small`, `cnt_enc` | The packed form of a position with piles of size at most 7 and fewer than 32 piles; its base-32 digits are the numbers of piles of each size. |
| `Move.code`, `move_of_legal`, `even_of_allEven` | The moves of a small position are the legal move codes of its packed form; `allEven` means that every pile has even size. |
| `isP_of_cert` | Soundness: if every node of a certificate passes `allOk`, every small position whose packed form is a key is a P-position. |
| `certX_ok`, `certX_mem`, `certY_ok`, `certY_mem` | Both certificates pass `allOk`, and they contain \((0,2,2,2,2,2,3)\) and \(Y\). |

## Statement faithfulness

There is no Formal Conjectures statement of this conjecture, so the statement
is ours. The choices, also listed in the module docstring:

- **Positions.** A position is the multiset of its pile sizes
  (`Multiset ℕ`). `position n a` has `a i` piles of size `i` for each
  \(1\le i\le n\) and no other piles, so no pile is larger than \(n\). The
  values of `a` outside \(1\le i\le n\) are ignored.
- **Empty piles.** A pile emptied by a move stays in the multiset with size 0
  and takes part in no move. `isP_zero_cons` proves that adding or removing
  such a pile changes no outcome, so the outcomes are those of the game in
  which empty piles disappear.
- **Moves.** `Move s t` takes one token from one pile of positive size, or one
  token from each of two different piles of positive size. The two piles are
  two elements of the multiset, so they may have the same size.
- **Outcomes.** `IsP s` says that no move from `s` leads to a P-position. It is
  defined by well-founded recursion on the number of tokens, which every move
  lowers, so a position without moves is a P-position (normal play).
- **Exception.** Exactly one position is excluded, `exception =
  {1, 1, 2, 2, 3, 3, 3}`.
- **\(n\ge3\).** `statement` assumes \(n\ge3\), which only weakens it, so
  `not_statement` also refutes the literal reading. Read literally, the
  conjecture covers \(n\le2\) as well, and it fails at \(n=2\) for a simple
  reason: \(1,1,2,2\) has 6 tokens, but taking one token from each pile of
  size 1 leaves \(2,2\), whose piles are even (`two_counterexample`). The same
  move shows that every \((2,a_2)\) is an N-position, and the paper's lemma on
  piles of size at most 3 lists \((a_1,a_2)=(2,3k+2)\) among its exceptions. So
  the authors presumably mean \(n\ge3\). For \(n\le1\) the claim holds: the
  empty position is a P-position, and with piles of size 1 only, a move removes
  one or two piles.
- **Hypotheses of the counterexamples.** `X_counterexample` and
  `Y_counterexample` prove \(a_i\ge2\) for \(1\le i\le7\), the inequality with
  the exception, and the number of tokens, from the definitions.

## Computational cross-checks

The Lean proof is the certificate. Two solvers that share no code recompute
the outcomes, with the Python standard library and a C++17 compiler only:

- [`oooc_counts.cpp`](oooc_counts.cpp) works on pile counts packed 6 bits per
  size, with a memo in an open-addressing hash table;
- [`oooc_tuples.py`](oooc_tuples.py) works on sorted tuples of pile sizes, with
  a dictionary memo.

Both reproduce \(X\) (N), \(Y\) (P), \((2,2,2,2,2,3,3)\) (69 tokens, N),
\((2,2,2,2,2,3,4)\) (76 tokens, P) and \((0,2,2,2,2,2,3)\) (P). With \(n=7\)
and every \(a_i\in[2,4]\), both find the same 15 failures among 2,187
positions. With \(n=6\) and every \(a_i\in[2,8]\), there is no failure among
117,649 positions. The C++ solver finds no failure for \(n=3,4,5\) with every
\(a_i\in[2,8]\) either, so among positions with every \(a_i\le8\), \(n=7\) is
the smallest \(n\ge3\) with a failure.

[`gen_certificate.py`](gen_certificate.py) rebuilds both certificate modules
from its own memoized solver and, with `--check`, compares them with the
committed files.

**How robust is the failure?** The paper motivates the conjecture by
"sufficient piles of each size". We counted failures among positions
with every \(a_i\ge t\) for small boxes (computer-assisted, not formalized;
the table is in [DETAILS.md](DETAILS.md#robustness-of-the-failure)). Raising
the threshold to \(t=3\) leaves no failure in the boxes we checked for \(n=7\)
and \(n=8\), but there are
failures again for \(n=9\) (20 of 512 positions with \(a_i\in[3,4]\), among them
\(a_i=3\) for all \(i\), which both solvers find) and \(n=10\) (593 of 1,024). The
boxes we checked with \(t\ge4\) have no failure, but they stop at \(n=9\) (and
the single position \(a_i=4\) for \(n=10\)). The data do not show a threshold
that rescues the conjecture.

## Prior art and status

- **The paper.** Conjecture 3.1 of arXiv:2605.23213v1 (2026-05-22), the only
  version as of 2026-10-25. OpenAlex lists no work citing it.
- **MathDB.** [Post 374893](https://mathdb.com/p/374893/version-c-s-subtract-three-conjecture)
  (created 2026-08-11) states the conjecture. The reply by user `shivampatel`
  (2026-08-20) gives \(X\), the move to \((0,2,2,2,2,2,3)\), and \(Y\), with a
  backward-induction program. MathDB lists the post as "claimed solved,
  unverified", with no review and no Lean formalization (2026-10-25).
  **The refutation is therefore not new.** This entry checks it in Lean.
- **Formal artifacts.** On 2026-10-25 (about 15:15 UTC) we found no formal
  statement or refutation of Version C: none in Formal Conjectures (issues,
  pull requests and files), in GitHub code and repository searches, or on
  Zenodo. The Lean files of the-omega-institute/trureturing and the repository
  achrafpy/oooooob-conjecture-counterexample are about Version B only, and
  OpenConjecture lists the Version C conjecture (conj 2622) with no attempt.
  [DETAILS.md](DETAILS.md#prior-art) lists the searches.

Nothing has been submitted to MathDB, OpenConjecture, the authors or anywhere
else; any external submission needs human approval.

## Reproduction

From the repository root:

```bash
lake build AgenticConjectures.OooooobVersionC
python3 scripts/check_axioms.py
```

Once mathlib is built, the four modules take about 1 minute of wall time on
an Apple M5 Max: `CertY` 44–48 s and `CertX` 18–20 s, built in parallel, then
4–6 s for the main module.

From this directory:

```bash
g++ -O3 -std=c++17 oooc_counts.cpp -o /tmp/oooc_counts && /tmp/oooc_counts --ci
python3 oooc_tuples.py
python3 gen_certificate.py --check
/tmp/oooc_counts --version-b
python3 oooc_tuples.py --version-b
python3 oooc_tuples.py --full
/tmp/oooc_counts box 9 3 4
```

The first five commands are the CI checks; they take about 1 s, 22 s, 8 s,
1 s and 1 s. With `--version-b`, both solvers recompute three positions of
the paper's Version B, for the related note at the end of
[DETAILS.md](DETAILS.md). `--full` adds the \(n=6\) box to the Python solver
(about 2.5 minutes).
`box n lo hi` prints every failure with all \(a_i\in[lo,hi]\); the runtimes of
the robustness boxes are in [DETAILS.md](DETAILS.md#robustness-of-the-failure).
