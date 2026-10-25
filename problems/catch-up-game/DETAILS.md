**English** | [한국어](DETAILS.ko.md)

# Catch-Up: mathematical details

This file collects the arguments behind the solvers and the Lean lemmas in this
directory. Statements marked *(Lean)* are kernel-checked in
[`CatchUpGame.lean`](../../AgenticConjectures/CatchUpGame.lean); the others are
informal proofs written for this repository. Nothing here proves the conjecture.
Section 5 reduces it to a stronger statement that could only be tested.

Throughout, `R` is a finite set of positive integers (Section 5 also allows
multisets), `ΣR` is its sum, and outcomes are ordered `loss < draw < win`.
`Outcome.best` is the maximum of a list in this order *(Lean: `best_eq`)*, so a
nested `best` over a tree of choices is the maximum over its leaves.

## 1. Positions are (remaining numbers, gap)

`valueAux R s_me s_opp isFirstMove` is the upstream evaluator.

1. Adding the same amount to both scores changes nothing:
   `valueAux R (a + k) (b + k) f = valueAux R a b f` *(Lean: `valueAux_add`)*.
2. After the very first call the player to move is never ahead. A recursive call
   that keeps the same player is made with `s_me + x < s_opp`. A call that swaps
   roles is made after `s_me + x ≥ s_opp`, so the new mover's score is not the
   larger one; the first move swaps roles after a pick of `x ≥ 0` from level
   scores. Every later call is therefore `valueAux R s (s + D) false` with a gap
   `D ≥ 0`, and it equals `P(R, D) := valueAux R 0 D false`
   *(Lean: `gapValue`, `valueAux_eq_gapValue`)*.
3. `P` satisfies the following recursion *(Lean: `gapValue_eq`)*:
   - `P(∅, D)` is a draw if `D = 0` and a loss if `D > 0`;
   - `P(R, D)` is a loss if `ΣR < D`;
   - otherwise `P(R, D)` is the best, over `x ∈ R`, of `−P(R∖{x}, x − D)` when
     `x ≥ D` (the turn ends and the roles swap) and of `P(R∖{x}, D − x)` when
     `x < D` (the same player must keep picking).
4. The first move is a single pick followed by a role swap. For nonempty `S`,
   `value S` is the best over `x ∈ S` of `−P(S∖{x}, x)`
   *(Lean: `value_eq_gapValue`)*. By item 3 with `D = 0` this is `P(S, 0)`, and
   both sides are a draw for `S = ∅`. So a fresh game is the position with
   gap 0 *(Lean: `value_eq_gapValue_zero`)*.

[`catchup_pick.cpp`](catchup_pick.cpp) implements items 3 and 4 with
memoization and nothing else. [`valueaux_transliteration.py`](valueaux_transliteration.py)
transliterates `valueAux` itself.

## 2. Turns

**Lemma 2.1 (nobody gets stuck in the middle of a turn).** If `ΣR ≥ D > x` with
`x ∈ R`, then `Σ(R∖{x}) = ΣR − x ≥ D − x`. So the rule "`ΣR < D` gives a loss"
can fire only at the start of a turn.

**Lemma 2.2 (legal turns).** Let `D ≥ 1`. A sequence of distinct picks
`x_1, …, x_k` from `R` is a complete turn exactly when every proper prefix sums
to less than `D` and the whole sequence sums to at least `D`. A set `A ⊆ R` can
be taken as one turn, in some order, exactly when `ΣA ≥ D` and
`ΣA − max A < D`; the order "largest number last" then works. For `D = 0` a turn
is a single pick, because the first pick already closes the gap. A legal turn
exists exactly when `R ≠ ∅` and `ΣR ≥ D`.

*Proof.* Suppose `ΣA − max A < D ≤ ΣA`. Every proper prefix of an order that
ends with `max A` is a subset of `A∖{max A}`, so it sums to less than `D`, and
the full turn reaches `D`. Conversely, in a legal turn the prefix of length
`k − 1` is `A∖{x_k}`, so `ΣA − max A ≤ ΣA − x_k < D`. For existence, take the
numbers of `R` in increasing order until the running sum first reaches `D`.

**Turn recursion.** Write `V(R, D)` for `P(R, D)` read at the start of a turn
(the mover trails by `D`). Unfold item 3 of Section 1 along a turn. Lemma 2.1
says no branch gets stuck inside the turn, and nested maxima flatten. This gives:

- `V(∅, D)` is a draw if `D = 0` and a loss otherwise;
- `V(R, D)` is a loss if `ΣR < D`;
- otherwise `V(R, D)` is the best, over legal turns `A`, of
  `−V(R∖A, ΣA − D)`.

The opponent's new gap `ΣA − D` is the amount by which the mover overtook. Since
`ΣA − D < max A`, every gap after the first move is smaller than the largest
number taken. The first gap is the first pick itself. So on `{1, …, N}` all gaps
are at most `N`. [`catchup_turn.cpp`](catchup_turn.cpp) searches this
recursion, starting from the position `(S, 0)` (Section 1, item 4).

## 3. Final shares: when one turn already decides the game

Take a turn-start position `(R, D)`: the mover `M` trails the opponent `O` by
`D`, and the numbers of `R` are still to be taken. When the game ends, every
number of `R` has gone to one of the players. In the "cannot catch up" case the
rules give the remaining numbers to the stuck player, who still finishes behind.
So `valueAux`'s verdict "loss" there agrees with comparing final scores. If `m`
is `M`'s final share of `R`, then `M`'s final margin is
`m − (ΣR − m) − D = 2m − ΣR − D`, and the outcome for `M` is the sign of that
margin.

**Lemma 3.1 (half-sum).** If `M` has a legal turn `A` with `2ΣA ≥ ΣR + D`, then
`V(R, D) ≥ draw`. If `2ΣA > ΣR + D`, then `V(R, D) = win`.

*Proof.* After `A` is played, `M`'s final share is at least `ΣA` whatever
happens later. So the final margin is at least `2ΣA − ΣR − D`.

**Lemma 3.2 (exact half).** If `2ΣA = ΣR + D` for a legal turn `A`, then playing
`A` gives exactly a draw.

*Proof.* `O` now trails by `ΣA − D = ΣR − ΣA = Σ(R∖A)`. If `R∖A = ∅` that gap
is 0 and the game is drawn. Otherwise `O` may take all of `R∖A` in one legal
turn, since its sum equals the gap and its sum minus its maximum is smaller.
That ends the game with margin 0. Lemma 3.1 gives the other inequality.

**Lemma 3.3 (largest legal turn).** Let `D ≥ 1` and `ΣR ≥ D`. Let `M_R = max R`,
and let `b` be the largest subset sum of `R∖{M_R}` that is at most `D − 1`.
Then the largest sum of a legal turn is `M_R + b`. It is attained by
`{M_R} ∪ B` for any `B ⊆ R∖{M_R}` with sum `b`. For `D = 0` it is `M_R`.

*Proof.* Let `A` be legal with largest element `m`, and let `B = A∖{m}`, so that
`ΣB ≤ D − 1`. If `m = M_R`, then `B ⊆ R∖{M_R}` and `ΣA ≤ M_R + b`. If
`m < M_R`, then `M_R ∉ A`, so again `B ⊆ R∖{M_R}`, and
`ΣA = m + ΣB < M_R + b`. Conversely, `{M_R} ∪ B` has sum minus maximum equal to
`b < D`. Its sum `M_R + b` is at least the sum of any legal turn, and one exists
by Lemma 2.2, so it is at least `D`. Hence `{M_R} ∪ B` is legal.

**How `catchup_turn.cpp` uses this.** It computes two Booleans:

- `NL(R, D)`, "the mover can secure at least a draw":
  `NL(R, D) = ∃ legal A: ¬W(R∖A, ΣA − D)`;
- `W(R, D)`, "the mover can force a win":
  `W(R, D) = ∃ legal A: ¬NL(R∖A, ΣA − D)`.

Before expanding a node it compares `2(M_R + b)` with `ΣR + D`, using
Lemmas 3.1 and 3.3: `≥` settles `NL` and `>` settles `W`. Inside `W` it skips
turns with `2ΣA = ΣR + D`, which cannot win by Lemma 3.2. The move order
affects only the running time. It tries ties that leave a complete set first,
then smaller new gaps first.

## 4. The root and parity

Let `S = {1, …, N}` and `T = N(N + 1)/2`.

- **Parity.** Final scores add up to `T`, and a draw needs equal scores, so an
  odd `T` admits no draw. In Lean, `valueAux_ne_draw` proves by induction that a
  position whose two scores and remaining numbers add up to an odd total is
  never a draw. `value_Icc_ne_draw` specializes it, and `statement_iff` concludes
  that the conjecture says exactly `value (Icc 1 N) = draw ↔ T` is even.
- **Even `T`.** Since `value(S)` is the best over `x` of `−V(S∖{x}, x)`:
  - the game is a draw exactly when `NL(S, 0)` holds and `NL(S∖{x}, x)` holds
    for every `x`. The first condition is "some first pick after which the
    second player cannot win". The second is "after every first pick the second
    player can still draw";
  - it is a first-player win exactly when some `x` has `¬NL(S∖{x}, x)`;
  - it is a loss exactly when `¬NL(S, 0)`.
- **Odd `T`.** `value(S)` is a win if `W(S, 0)` holds and a loss otherwise.

## 5. A stronger conjecture that implies the statement

Call a finite multiset `Q` of positive integers **complete** if, listed in
increasing order `q_1 ≤ … ≤ q_k`, it satisfies `q_i ≤ 1 + q_1 + … + q_{i−1}`
for every `i`. Equivalently, every integer from 0 to `ΣQ` is the sum of a
sub-multiset. `{1, …, N}` is complete. Catch-Up on a multiset is defined like
on a set: a pick removes one copy of a number.

**Conjecture L.** Let `R` be a finite multiset of positive integers and `D ≥ 0`.
Suppose `R + {D}` is complete (for `D = 0` read `R`) and `ΣR − D` is even. Then
`V(R, D) ≥ draw`: the player to move can at least draw.

**L implies the statement.** Let `T` be even. With `D = 0`, `R = S` is complete
with an even sum, so `NL(S, 0)`. For a first pick `x`, take `R = S∖{x}` and
`D = x`. Then `R + {D} = S` is complete and `ΣR − D = T − 2x` is even, so
`NL(S∖{x}, x)`. By Section 4 the game is a draw.

**L is equivalent to "Catch-Up on every complete multiset with even sum is a
draw".** The forward direction is the argument above with `S` replaced by the
multiset. For the converse, take `(R, D)` as in L.

- If `D ≥ 1`, the game on `Q = R + {D}` is a draw, and the first player may open
  with `D`, which leaves the second player at `(R, D)`. Since the first player
  cannot win, `V(R, D) ≥ draw`.
- If `D = 0`, `V(R, 0)` is the value of the game on `R` itself (Section 1,
  item 4), which is a draw.

The completeness hypothesis cannot simply be dropped. `{1, 3}` has an even sum,
but the first player takes 3 and the second player can no longer catch up.

**Evidence.**

- [`generalization_check.py 12 9`](generalization_check.py) evaluates every
  multiset with entries in `1..12` and at most 9 elements
  ([log](logs/generalization_check_12_9.log)). Its solver is a third
  implementation of the turn recursion of Section 2, without the pruning of
  Section 3. All 26,767 complete multisets with an even sum are draws.
  Conjecture L holds at all 1,272,753 positions `(R, D)` of this range that
  satisfy its hypothesis:
  - 26,767 with `D = 0`, all draws;
  - 314,659 draws and 931,327 wins with `D ≥ 1`.
- [`closure_check.cpp 1 16`](closure_check.cpp) evaluates the exact value of
  every position `(R, D)` with `R ⊆ {1, …, 16}` that satisfies the hypothesis
  of L: 442,699 positions, 95,430 draws, 347,269 wins and no loss
  ([log](logs/closure_check_1_16.log)).

## 6. Attempts that did not give a proof

Let `X` be the class of positions in the hypothesis of Conjecture L. A proof of L
by induction on the number of remaining numbers would need, at every `X`
position, either a turn that settles the game at once (Lemma 3.1) or a turn
after which the game provably stays inside `X`.
[`closure_check.cpp`](closure_check.cpp) measures how often simple versions of
this plan apply. The figures below are for all `X` positions with
`R ⊆ {1, …, 16}`; the log has every `n ≤ 16`.

- **Immediate positions.** At 172,196 of the 442,699 positions some legal turn
  `A` has `2ΣA ≥ ΣR + D`.
- **Two-ply closure.** Call a non-immediate position *closed* if the mover has a
  turn after which every reply of the opponent either is an exact draw
  (Lemma 3.2) or returns the mover to an `X` position. The parity condition of
  `X` is preserved automatically: only completeness can fail. If every `X`
  position were immediate or closed, L for sets would follow. Of the 270,503
  non-immediate positions, 183,326 are closed and 87,177 are not. The first
  failures already occur at `n = 4`, including the full game
  `({1, 2, 3, 4}, 0)`. So `X` is not an inductive invariant at depth two. A
  proof needs a larger class of positions, or a different argument.
- **"Tie and leave a complete set".** At `D ≥ 1`, a turn with `ΣA = D` that
  leaves a complete set puts the opponent in `X` with gap 0. At 81,463 of the
  264,789 non-immediate positions with `D ≥ 1`, no such turn exists.
- **Simple first picks.** At the 5,714 non-immediate `X` positions with `D = 0`:
  - taking the largest number lets the opponent win at 4,964 of them;
  - taking the smallest number lets the opponent win at 221 of them.

  Neither rule is a drawing strategy.

These experiments are recorded as negative results. They do not refute
Conjecture L.

## 7. Cost of kernel evaluation

`decide` evaluates the unmemoized list copy `valueList` in the kernel.
`Outcome.best` is a left fold whose step function returns at once only when the
accumulator is already `win`. So almost the whole game tree is visited.

A call-count model of that evaluation, run during development (not committed),
gives:

| `N` | recursive calls |
|---|---|
| 8 | 43,341 |
| 11 | 14,797,797 |
| 12 | 159,714,703 |

This is why the kernel-checked range stops at `N ≤ 10`, where the even cases are
`N = 0, 3, 4, 7, 8`. Going further in Lean would need a verified memoized or
pruned evaluator. One example would be a formal proof of Lemmas 3.1–3.3 together
with a certificate format for the search of `catchup_turn.cpp`.
