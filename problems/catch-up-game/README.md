**English** | [한국어](README.ko.md)

# Catch-Up on {1, …, N}: is the game a draw whenever T_N is even?

**Status: partial.** The conjecture is open. This directory contains:

- a Lean proof of the statement for `N ≤ 10`;
- Lean lemmas about the upstream evaluator `valueAux`;
- exact values of Catch-Up({1, …, N}) for every `N ≤ 28`, computed by two
  independent C++ programs. In particular the game is a draw for every even
  `T_N` with `N ≤ 28`;
- a stronger conjecture that implies the statement, tested on small cases
  ([DETAILS.md](DETAILS.md)).

## The problem

Catch-Up was introduced by A. Isaksen, M. Ismail, S. J. Brams and A. Nealen,
*Catch-Up: A Game in Which the Lead Alternates*, Game & Puzzle Design 1(2),
38–49 (2015) ([MPRA preprint 108784](https://mpra.ub.uni-muenchen.de/108784/)).
Two players take numbers from a finite set `S` of positive integers, and each
number taken is added to the taker's score. The upstream formalization fixes
the rules as follows:

- the first player starts by taking **exactly one** number;
- afterwards, a player keeps taking numbers one at a time until their score is
  **at least** the opponent's, and before the last pick of the turn they must
  still be **strictly behind**;
- a player who cannot catch up even with all the remaining numbers **loses
  immediately**;
- when `S` is exhausted, the higher score wins and equal scores draw.

The paper conjectures that Catch-Up on `{1, …, N}` ends in a draw under optimal
play whenever `T_N = N(N + 1)/2` is even, that is, when `N ≡ 0` or `3 (mod 4)`.

### Upstream statement

The statement is taken from
[`FormalConjectures/Paper/CatchUpConjecture.lean`](upstream/CatchUpConjecture.lean)
in google-deepmind/formal-conjectures (Apache-2.0; provenance in
[upstream/README.md](upstream/README.md)):

> Let $T_N = \sum_{k=1}^{N} k = \frac{N(N+1)}{2}$.
> If $T_N$ is even (equivalently $N \equiv 0 \pmod 4$ or $N \equiv 3 \pmod 4$),
> then under optimal play the game `Catch-Up($\{1, \ldots, N\}$)` ends in a draw.

```lean
theorem value_of_even_mul_succ_self_div_two
    (N : ℕ) (h_even : Even (N * (N + 1) / 2)) :
    value (.Icc 1 N) = .draw := by
  sorry
```

## Results

Values are given for the first player under optimal play.

| N | T_N | value | | N | T_N | value |
|---:|---:|:---|---|---:|---:|:---|
| 1 | 1 | win | | 15 | 120 | **draw** |
| 2 | 3 | win | | 16 | 136 | **draw** |
| 3 | 6 | **draw** | | 17 | 153 | win |
| 4 | 10 | **draw** | | 18 | 171 | loss |
| 5 | 15 | win | | 19 | 190 | **draw** |
| 6 | 21 | win | | 20 | 210 | **draw** |
| 7 | 28 | **draw** | | 21 | 231 | win |
| 8 | 36 | **draw** | | 22 | 253 | win |
| 9 | 45 | loss | | 23 | 276 | **draw** |
| 10 | 55 | loss | | 24 | 300 | **draw** |
| 11 | 66 | **draw** | | 25 | 325 | win |
| 12 | 78 | **draw** | | 26 | 351 | win |
| 13 | 91 | win | | 27 | 378 | **draw** |
| 14 | 105 | loss | | 28 | 406 | **draw** |

The table has three kinds of support:

- **Lean (kernel-checked):** the rows with `N ≤ 10`. `statement_of_le_ten`
  covers the even cases `N = 0, 3, 4, 7, 8`, and `value_Icc_ne_draw` shows that
  the odd cases are not draws.
- **Computer-assisted:** every row is computed by both
  [`catchup_turn.cpp`](catchup_turn.cpp) and [`catchup_pick.cpp`](catchup_pick.cpp),
  which agree. The conjecture therefore holds for all `N ≤ 28`, subject to the
  correctness of these programs and of the compiler.
- **OEIS:** the rows `3 ≤ N ≤ 20` agree with [OEIS A278587](https://oeis.org/A278587),
  which encodes them as 1 / 0 / −1.

The odd-`T_N` rows show no simple pattern. `N = 22` is a first-player win,
whereas `N = 14` and `N = 18` are second-player wins.

## Prior work and what this adds

- The paper reports optimal-play results for `N ≤ 20`. For `N = 23, 24, 27, 28`
  it also reports Monte Carlo tree search experiments, which found no
  contradiction with the conjecture.
- OEIS A278587 lists the values for `N = 3..20`. It is marked "more" (more
  terms wanted).
- The formal-conjectures file states the conjecture with `sorry`.
- arXiv has no version of the paper. OpenAlex lists seven works that cite it
  (checked on 2026-10-24). Judging by their titles, they are about game
  heuristics, drawing without replacement as a game mechanic, catch-up rules in
  sports, and a game-theoretic model of AI. They were not read in full.

The exact values for `N = 21..28` here go beyond the values listed in the
paper, A278587 and the formal-conjectures file. They include the four cases
that the paper only tested with MCTS. The search covered only the sources
above. This is not a priority or novelty claim, and nothing has been submitted
to the OEIS or upstream.

## How the values are computed

The model and every pruning rule are justified in [DETAILS.md](DETAILS.md).

- **[`catchup_turn.cpp`](catchup_turn.cpp)** searches whole turns. A turn at
  gap `D ≥ 1` removes a set `A` with `ΣA ≥ D` and `ΣA − max A < D`; at gap 0 it
  removes one number. The program decides two Booleans for each position: "the
  mover can secure at least a draw" and "the mover can force a win". It uses a
  hash table and the half-sum cutoffs of DETAILS §3.
- **[`catchup_pick.cpp`](catchup_pick.cpp)** follows `valueAux` one pick at a
  time. It uses the gap recursion that the Lean theorem `gapValue_eq` derives
  from the upstream definition. It shares no code with the turn-level program,
  and it has no pruning beyond memoization and short-circuiting.
- **[`valueaux_transliteration.py`](valueaux_transliteration.py)** is a literal
  Python copy of the upstream `valueAux`, including the fold of `Outcome.best`.
  It is too slow for large `N` and serves as the reference on small inputs.

[`verify_values.py`](verify_values.py) compiles both C++ programs and checks
three things against the table above:

- the C++ values for `N ≤ 22`;
- the Python values for `N ≤ 12`;
- a three-way comparison of all 11,264 positions `(R, D)` with
  `R ⊆ {1, …, 10}` and `D ≤ 10`.

`python3 verify_values.py --nmax 12 --positions 12` extends the three-way
comparison to all 53,248 positions with `R ⊆ {1, …, 12}` and `D ≤ 12`. It
passes in 7 s with 0.8 GB of memory, and CI runs it too.

### Reproduction

From this directory (single-threaded; the times were measured on an Apple
silicon Mac with Apple clang 21 and `-O3`):

```bash
python3 verify_values.py
```

```bash
python3 verify_values.py --nmax 28
```

```bash
g++ -O3 -std=c++17 catchup_turn.cpp -o build_turn && ./build_turn 1 28 && rm -f build_turn
```

```bash
g++ -O3 -std=c++17 catchup_pick.cpp -o build_pick && ./build_pick 1 28 && rm -f build_pick
```

| run | time | peak memory | log |
|---|---|---|---|
| `verify_values.py` (CI default) | 25 s | 0.5 GB | — |
| `catchup_turn 1 28` | 1,282 s | 6.4 GB | [log](logs/catchup_turn_1_28.log) |
| `catchup_pick 1 28` | 454 s | 15.0 GB | [log](logs/catchup_pick_1_28.log) |

`verify_values.py --nmax 28` runs both full computations, so it needs the sum
of the two times and the larger memory peak. Per-`N` times are in the logs. The
largest cases are:

| N | turn-level | pick-level |
|---:|---:|---:|
| 25 | 136 s | 71 s |
| 26 | 277 s | 157 s |
| 27 | 246 s | 64 s |
| 28 | 568 s | 140 s |

The next cases with even `T_N` are `N = 31` and `N = 32`. From `N = 24` to
`N = 28` the turn-level table grew about 14.5-fold and the running time about
22-fold. Extrapolating, the turn-level program alone would need about 50 GB and
1.5 hours for `N = 31`, and about 100 GB and 3.5 hours for `N = 32`. The
pick-level cross-check would need well over 100 GB. These runs were not
attempted on the shared machine.

## Toward a proof

[DETAILS.md](DETAILS.md) §5 reduces the conjecture to **Conjecture L**: if the
multiset `R + {D}` is complete and `ΣR − D` is even, the player to move at
`(R, D)` can at least draw. L is equivalent to "Catch-Up on every complete
multiset with even sum is a draw". It was tested in two ranges:

- 1,272,753 positions over multisets with entries `≤ 12` and at most 9
  elements, checked by [`generalization_check.py`](generalization_check.py);
- all 442,699 set positions with `R ⊆ {1, …, 16}`, checked by
  [`closure_check.cpp`](closure_check.cpp).

No counterexample was found. DETAILS §6 records why the simplest inductive
proofs of L fail. The class of positions in L is not closed under two plies,
and neither "tie and leave a complete set" nor "take the largest number" nor
"take the smallest number" is a drawing strategy.

```bash
python3 generalization_check.py 12 9
```

```bash
g++ -O3 -std=c++17 closure_check.cpp -o build_closure && ./build_closure 1 16 && rm -f build_closure
```

The first command takes about 8 minutes (497 s, 0.37 GB; [log](logs/generalization_check_12_9.log)).
The second takes 7 seconds ([log](logs/closure_check_1_16.log)).

## Lean formalization

Module: [`AgenticConjectures/CatchUpGame.lean`](../../AgenticConjectures/CatchUpGame.lean).

| declaration | content |
|---|---|
| `Player` … `valueAux`, `value` | upstream definitions, copied verbatim (checked by [`check_upstream_copy.py`](check_upstream_copy.py)) |
| `statement` | the upstream open theorem as a `Prop` |
| `statement_of_le_ten` | `statement` restricted to `N ≤ 10` |
| `value_Icc_three`, `_four`, `_seven`, `_eight` | the draws for `N = 3, 4, 7, 8` by `decide +kernel` |
| `valueList`, `valueAux_toFinset` | a computable list version of `valueAux` with fuel, proved equal to it |
| `valueAux_ne_draw`, `value_Icc_ne_draw` | a position with an odd total of scores and remaining numbers is never a draw |
| `statement_iff` | `statement ↔ ∀ N, value (Icc 1 N) = draw ↔ Even (N (N + 1) / 2)` |
| `valueAux_add`, `valueAux_eq_gapValue` | only the score gap matters |
| `gapValue_eq`, `value_eq_gapValue`, `value_eq_gapValue_zero` | the gap recursion used by `catchup_pick.cpp`; a fresh game is the gap-0 position |
| `best_eq`, `best_congr` | `Outcome.best` is the maximum for `loss < draw < win` |

`decide` evaluates the unmemoized recursion in the kernel, so it stops being
practical after `N = 8` (DETAILS §7). No `native_decide` is used. The axioms
are `propext`, `Classical.choice` and `Quot.sound`.

### Statement faithfulness

- **Definitions.** `Player`, `Outcome`, `Outcome.neg`, `Outcome.best`,
  `valueAux` and `value` are byte-identical to the upstream snapshot, docstrings
  and comments included. Only the module header (`import Mathlib` instead of
  FormalConjectures' utilities) and the namespace differ.
- **Statement.** `statement` keeps the upstream binder, hypothesis and
  conclusion. `N * (N + 1) / 2` is exact natural division. `N = 0` is included
  and is the trivial draw on `∅`.
- **Rule conventions.** The three conventions that could differ from informal
  descriptions of the game are those of `valueAux`:
  - the first move is exactly one pick;
  - a player who cannot catch up loses at once;
  - a turn ends as soon as the score reaches at least the opponent's.
- **Solvers.** Both C++ programs and the Python transliteration implement these
  conventions. The turn model is derived from `valueAux` in DETAILS §1–2, and
  the three programs agree position by position on small inputs.
- **Numbers.** Upstream `Finset ℕ` allows `0`. The solvers assume positive
  numbers, which is all that `Icc 1 N` contains.

## Files

| file | role |
|---|---|
| `catchup_turn.cpp` | turn-level exact solver (main computation) |
| `catchup_pick.cpp` | pick-level exact solver (independent check) |
| `valueaux_transliteration.py` | literal Python copy of `valueAux` (reference on small inputs) |
| `verify_values.py` | compiles and cross-checks the three implementations |
| `check_upstream_copy.py` | checks that the Lean definitions match the upstream snapshot byte for byte |
| `generalization_check.py` | Conjecture L and complete multisets |
| `closure_check.cpp` | Conjecture L on set positions; failed-induction statistics |
| `logs/` | output, time and memory of the full runs |
| `DETAILS.md` | proofs of the model and pruning rules; Conjecture L; failed attempts |
| `upstream/` | formal-conjectures snapshot and provenance |

## What is not claimed

- No proof of the conjecture for all `N`, and no claim about any `N > 28`.
- The values for `11 ≤ N ≤ 28` are not Lean-checked. They rest on two
  independent C++ programs, which agree with each other and, on small inputs,
  with a literal transliteration of the upstream definition.
- Conjecture L is a conjecture. The searches in DETAILS §5–6 are evidence, not
  proof.
- No novelty or priority claim.
