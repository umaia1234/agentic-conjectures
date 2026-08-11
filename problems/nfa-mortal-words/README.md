# Mortal words in small image-bounded NFAs

This directory contains a reproducible exploratory computation for an open
question posed by Stefan Kiefer and Andrew Ryzhikov in MFCS 2025.

The results here are deliberately narrow:

- an exhaustive enumeration of **ordered binary** NFAs with at most four
  labelled states;
- independently checked three- and four-state witnesses; and
- a deterministic random search that rediscovers the four-state witness.

No claim is made that the small extremal values are new to the literature.
Exact-title and exact-phrase web searches performed on 2026-08-11 found the
posing paper but no later paper resolving its general tightness question. That
search is evidence about the literature checked, not a proof that the small
values below have never appeared elsewhere.

## Problem and source

For an NFA semi-automaton \(\mathcal A=(Q,\Sigma,\Delta)\), write
\(q\cdot w\) for the set of states reachable from \(q\) along a word \(w\).
The NFA is `k-image-bounded` when

\[
  |q\cdot w|\le k
  \quad\text{for every }q\in Q\text{ and }w\in\Sigma^*.
\]

A word is `mortal` when it maps every state to the empty set. An NFA is
`incomplete` when it has a mortal word.

Kiefer and Ryzhikov show that an incomplete, \(n\)-state, \(k\)-image-bounded
NFA always has a mortal word of length at most \(n^{k+1}\), and explicitly ask
whether this bound is tight. They also prove that completeness for binary,
strongly connected, 2-image-bounded, unambiguous NFAs is NL-complete.

Primary source:

- Stefan Kiefer and Andrew Ryzhikov, “The Complexity of Reachability Problems
  in Strongly Connected Finite Automata,” MFCS 2025, especially Sections 7 and
  9: <https://doi.org/10.4230/LIPIcs.MFCS.2025.62>

## Exhaustive results for binary NFAs

Each alphabet symbol is an arbitrary Boolean relation on \(n\) states. Thus one
letter has \(2^{n^2}\) possibilities and the ordered pair `(a,b)` has
\(2^{2n^2}\) possibilities. Missing transitions are allowed.

| \(n\) | raw binary NFAs | 2-image-bounded | incomplete among them | maximum shortest mortal length | labelled maximizers |
|---:|---:|---:|---:|---:|---:|
| 1 | 4 | 4 | 3 | 1 | 3 |
| 2 | 256 | 256 | 109 | 3 | 8 |
| 3 | 262,144 | 42,451 | 16,957 | 7 | 24 |
| 4 | 4,294,967,296 | 15,167,209 | 6,573,243 | 10 | 576 |

The filter and distance calculation are exact:

1. From every singleton \(\{q\}\), breadth/depth-first search explores its
   reachable subsets in the powerset automaton. The candidate is retained iff
   every such subset has cardinality at most two. These reachable subsets are
   exactly the sets \(q\cdot w\), so this tests the global definition, not merely
   the one-letter transitions.
2. A second breadth-first search starts from the full set \(Q\). Reaching the
   empty set decides incompleteness, and its BFS distance is the shortest mortal
   word length.

Run the complete enumeration with:

```bash
python problems/nfa-mortal-words/enumerate_binary.py
```

Use `--json` for machine-readable output. The complete shortest-length
histograms are emitted as part of the output.

The Python enumerator is intentionally limited by default to `n <= 3`. The
four-state exhaustive pass uses the optimized C++ implementation:

```bash
g++ -O3 -march=native -fopenmp -std=c++17 \
  problems/nfa-mortal-words/enumerate_binary_n4.cpp \
  -o /tmp/nfa_mortal_n4
OMP_NUM_THREADS=16 /tmp/nfa_mortal_n4
```

For four states there are \(2^{32}\) unrestricted ordered binary NFAs. Global
2-image-boundedness immediately implies that each one-letter row has size at
most two, leaving exactly \(11^8=214{,}358{,}881\) candidates that can possibly
pass. The C++ search examines the \(107{,}186{,}761\) unordered letter pairs and
weights off-diagonal pairs by two, because swapping `a` and `b` preserves both
the filter and the shortest mortal distance. Its ordered shortest-length
histogram is

```text
{1: 10657, 2: 1037030, 3: 2854956, 4: 1884216, 5: 553800,
 6: 179160, 7: 39024, 8: 10704, 9: 3120, 10: 576}
```

For a cross-check of the optimized implementation against the independent
Python counts, compile with `-DNFA_STATES=3`; its bounded count, incomplete
count, and histogram must match the `n=3` Python output exactly.

## Witnesses

The three-state exhaustive maximizer has transitions

```text
a: 0 -> {0,2},  1 -> {0},  2 -> {}
b: 0 -> {1},    1 -> {2},  2 -> {0}
```

and shortest mortal word `abbabba`, with the full-set path

```text
{0,1,2} -> {0,2} -> {0,1} -> {1,2} -> {0} -> {1} -> {2} -> {}
```

The four-state exhaustive maximizer has transitions

```text
a: 0 -> {1},  1 -> {0},    2 -> {},   3 -> {0,2}
b: 0 -> {3},  1 -> {0,2},  2 -> {1},  3 -> {2}
```

and shortest mortal word `aabbaaabba` of length 10. It was first found here by
the seeded random search and subsequently certified optimal in the stated
binary four-state scope by the exhaustive C++ pass.

A separate one-billion-candidate run at five states found the lower-bound
witness

```text
a: 0 -> {1},   1 -> {4}, 2 -> {},  3 -> {0,4}, 4 -> {1,3}
b: 0 -> {0,4}, 1 -> {3}, 2 -> {1}, 3 -> {2},   4 -> {0}
```

with shortest mortal word `abbababbabbababba` of length 17.  The independent
transformation-monoid verifier accepts it, so the binary 2-image-bounded
five-state extremum is at least 17.  This is only a lower bound, not an exact
five-state value.  It is reproducible at zero-based SplitMix64 candidate index
746,229,884 with:

```bash
g++ -O3 -march=native -std=c++17 \
  problems/nfa-mortal-words/search_random_n5.cpp \
  -o /tmp/nfa_random5
/tmp/nfa_random5 1000000000 718281828
```

The data is in `witnesses.json`. Verify all three witnesses with a separate
implementation:

```bash
python problems/nfa-mortal-words/verify_witnesses.py
```

The verifier closes the letter relations under relational composition and
checks every row of every generated transformation. This is independent of the
singleton-subset filter used by the exhaustive enumerator. It then performs a
full powerset BFS to certify the shortest mortal distance and prints the claimed
word's subset path.

To replay the deterministic random search (one million candidates, normally a
few seconds), run:

```bash
python problems/nfa-mortal-words/search_random_n4.py
```

With Python's `random.Random` implementation and the recorded default seed, the
length-10 witness appears at zero-based candidate index 466,977. The random
generator first limits each one-letter row to size at most two, then applies the
full word-closure test; the former alone would not establish 2-image-boundedness.

## Claim boundary and next experiment

The exact extremal claim made here is for labelled, ordered-alphabet, binary
NFAs on at most four states. State relabelling is not quotiented out. The
four-state implementation quotients letter swapping during the scan but restores
ordered counts by weights, so the table's maximizer count is for ordered letters.

For \(n=5\), the analogous direct row restriction already leaves
\(16^{10}=2^{40}\) ordered candidates. A useful next step is state-isomorphism
reduction or a SAT encoding asking for shortest mortality at least \(L\). The
general proof's \(n^3\) upper bound for \(k=2\) comes from concatenating \(n\)
pair-killing words of quadratic length; the exact values \(1,3,7,10\) motivate
testing whether that extra factor can be removed by amortization.
