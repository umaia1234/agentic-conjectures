# Mortal words in small image-bounded NFAs

This directory contains a reproducible exploratory computation for an open
question posed by Stefan Kiefer and Andrew Ryzhikov in MFCS 2025.

The results here are deliberately narrow:

- an exhaustive enumeration of **ordered binary** NFAs with at most four
  labelled states;
- exhaustive enumerations for five and six labelled states, each confirmed by
  a separately written second enumerator: the exact maxima are **17** and
  **24** (see [the five- and six-state section](#exhaustive-results-for-five-and-six-states));
- independently checked witnesses, including one representative of every
  maximizer class up to state relabelling for one to six states; and
- deterministic random and seeded local searches; the latter gives only a
  lower bound for seven states.

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
| 5 | 1,125,899,906,842,624 | 9,216,856,696 | 4,469,395,126 | 17 | 960 |
| 6 | 4,722,366,482,869,645,213,696 | 8,696,091,964,576 | 4,706,072,918,662 | 24 | 20,160 |

The rows for \(n=5,6\) come from the two enumerators described in
[the five- and six-state section](#exhaustive-results-for-five-and-six-states);
both also reproduce every row above them exactly.

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

## Exhaustive results for five and six states

Added 2026-10-24. **Claim:** among ordered binary NFAs on \(n\) labelled states
that are 2-image-bounded and incomplete, the largest shortest-mortal-word length
is exactly **17 for \(n=5\)** and exactly **24 for \(n=6\)**. Renaming states and
swapping the two letters preserve both properties and the shortest mortal
length, so the same values hold up to isomorphism. With the earlier rows the
exact binary maxima for \(n=1,\dots,6\) are

\[
  1,\ 3,\ 7,\ 10,\ 17,\ 24 .
\]

In particular the seeded random five-state witness of length 17 below is
optimal; it lies in one of the eight maximizer classes listed in
`exhaustive_maximizers.json`.

### Reduction

Two necessary conditions follow from the definition applied to special words:
every one-letter row has size at most two (the word is one letter), and each
letter is 2-image-bounded on its own (words over that letter alone). Call such
letters *self-bounded*. Of the \(R^n\) row-restricted letters,
\(R=1+n+\binom n2\), there are 174,616 self-bounded letters out of 1,048,576
for \(n=5\) and 7,446,394 out of 113,379,904 for \(n=6\). A pair containing any
other letter is not 2-image-bounded, so only pairs of self-bounded letters
need to be examined; everything else contributes zero to every count.

The symmetric group \(S_n\) acts on letter pairs by renaming states, preserving
2-image-boundedness and shortest mortal lengths. If a letter \(a'\) lies in the
orbit of a chosen representative \(a\), pick \(\sigma\) with \(\sigma(a')=a\);
then \(b'\mapsto\sigma(b')\) is a bijection between second letters that maps
each pair \((a',b')\) to an isomorphic pair \((a,\sigma(b'))\). Hence examining
only representative first letters against *all* second letters, and weighting
by the orbit size of the first letter, reproduces exact labelled ordered counts.

### Two enumerators

- `enumerate_binary_canonical.cpp` (primary). The first letter runs over the
  minimum-code representative of each \(S_n\)-orbit of self-bounded letters
  (1,840 for \(n=5\), 13,070 for \(n=6\)); the second letter runs over all
  self-bounded letters (321,293,440 and 97,324,369,580 examined pairs). The
  global filter is a worklist closure of the subsets reachable from singletons;
  the shortest mortal length is a forward BFS from the full set. The program
  also canonicalizes every maximizer under \(S_n\) and under \(S_n\) plus
  letter swap.
- `enumerate_binary_crosscheck.cpp` (independent re-implementation, no shared
  code). Letters are packed Boolean matrices generated row by row; for
  \(n\le 5\) the number of self-bounded letters is confirmed by brute force over
  all \(2^{n^2}\) matrices. A single letter is tested by iterating the orbit of
  each singleton, a pair by a set-at-a-time closure, and the shortest mortal
  length is a *backward* fixpoint: \(K_0=\{\emptyset\}\),
  \(K_t=K_{t-1}\cup\{S: S\cdot a\in K_{t-1}\text{ or }S\cdot b\in K_{t-1}\}\)
  restricted to subsets reachable from the full set, and the answer is the least
  \(t\) with the full set in \(K_t\). Mode `full` examines every ordered pair
  with no symmetry reduction at all (30,490,747,456 pairs for \(n=5\)). Mode
  `orbit` instead reduces the *second* letter to the maximum-matrix
  representative of its orbit and weights by an orbit size obtained by listing
  the orbit.

For every \(n\le 6\) all runs report identical bounded and incomplete counts
and identical histograms; for \(n\le4\) these equal the Python and
`enumerate_binary_n4.cpp` results above. For \(n=5\) the canonical run, the
unreduced `full` run, and the `orbit` run agree; for \(n=6\) the canonical and
`orbit` runs agree. Ordered labelled histograms of shortest mortal lengths:

```text
n=5: {1: 349231, 2: 240841345, 3: 1419363730, 4: 1657101820, 5: 754842780,
      6: 268169340, 7: 89933400, 8: 26796840, 9: 8868960, 10: 2400720,
      11: 459360, 12: 130560, 13: 101520, 14: 19680, 15: 14400, 16: 480,
      17: 960}
n=6: {1: 14892787, 2: 82299111405, 3: 1009569452790, 4: 1761562446000,
      5: 1115628961260, 6: 465182293500, 7: 174900813960, 8: 63542838960,
      9: 22311447120, 10: 7510644720, 11: 2266094880, 12: 801053280,
      13: 316814400, 14: 106312320, 15: 35527680, 16: 12785760, 17: 6649920,
      18: 2612160, 19: 977760, 20: 643680, 21: 374400, 22: 105120,
      23: 44640, 24: 20160}
```

### Maximizers up to isomorphism

| \(n\) | maximum | labelled ordered maximizers | classes under relabelling | classes under relabelling and letter swap |
|---:|---:|---:|---:|---:|
| 1 | 1 | 3 | 3 | 2 |
| 2 | 3 | 8 | 4 | 2 |
| 3 | 7 | 24 | 4 | 2 |
| 4 | 10 | 576 | 24 | 12 |
| 5 | 17 | 960 | 8 | 4 |
| 6 | 24 | 20,160 | 28 | 14 |

Every class has exactly \(n!\) labelled members (no maximizer has a
nontrivial state automorphism), and for \(2\le n\le 6\) swapping the letters
never maps a class to itself. `exhaustive_maximizers.json` lists the
minimum-code representative of every relabelling class for \(n=1,\dots,6\)
(71 automata) with a shortest mortal word, together with the recorded counts
and histograms. For example, one
six-state maximizer is

```text
a: 0 -> {1,4}, 1 -> {3}, 2 -> {2}, 3 -> {1}, 4 -> {0}, 5 -> {}
b: 0 -> {2},   1 -> {4}, 2 -> {0}, 3 -> {2}, 4 -> {5}, 5 -> {1}
```

with shortest mortal word `abbaabbababbaabbabbaabba` of length 24.

### Reproduction and checks

```bash
cd problems/nfa-mortal-words
# CI check: both enumerators for n = 1..5 (canonical + orbit mode), 2 threads
python3 run_exhaustive_enumerations.py
# local: add the unreduced n <= 5 runs, and the n = 6 runs
python3 run_exhaustive_enumerations.py --full --threads 6 --native --log-dir logs
python3 run_exhaustive_enumerations.py --n 6 --threads 6 --native --log-dir logs
# monoid-closure verification of all 71 listed maximizer classes
python3 check_exhaustive_maximizers.py
```

`run_exhaustive_enumerations.py` compiles both programs into a temporary
directory, compares every reported count and histogram with
`exhaustive_maximizers.json`, and checks with its own Python orbit computation
that the maximizers printed by each run fall into exactly the listed classes
(in `full` mode: that the printed pairs are exactly all labelled maximizers).
`check_exhaustive_maximizers.py` re-verifies each listed representative with the
transformation-monoid verifier of `verify_witnesses.py`, checks that the
representatives are pairwise non-isomorphic, that their orbit sizes add up to
the recorded labelled counts, and that the earlier witnesses are consistent
with the recorded maxima. The raw outputs are in [`logs/`](logs/).

Measured wall times with 6 threads on an 18-core Apple M5 Max shared with
other jobs; the machine load differed between the exploratory runs and the
logged runs, so the ranges below span both: canonical enumerator 0.8–2.1 s
(\(n=5\)) and 207–452 s (\(n=6\)); cross-check `orbit` mode 1.7–4.0 s
(\(n=5\)) and 535–730 s (\(n=6\)); unreduced `full` mode 116–247 s (\(n=5\)).
The whole `--n 6` command took about 20 minutes under heavy load, the
`--full` command about 4.5 minutes. Each log ends with its own
`elapsed_seconds`.

### Comparison with the paper's bound

For \(k=2\) the general upper bound is \(n^{k+1}=n^3\), i.e. 125 for \(n=5\) and
216 for \(n=6\). The exact binary maxima 17 and 24 are far below it (about
\(0.14n^3\) and \(0.11n^3\), or about \(0.68n^2\) and \(0.67n^2\)). These are
finitely many small values for binary alphabets; they neither confirm nor
refute tightness of \(n^{k+1}\), which is a question about growth in \(n\)
over all alphabets.

### What is not claimed

- Nothing beyond binary alphabets, \(k=2\), and \(n\le 6\) is decided here.
- No novelty claim; the literature search recorded above was not repeated.
- Both new enumerators were written by the same agent in one session. Their
  independence is in code, data representation, algorithms, and symmetry
  reduction, not in authorship; neither is formally verified.

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
five-state extremum is at least 17.  When it was found this was only a lower
bound; the exhaustive five-state enumeration above later showed that 17 is the
exact maximum.  It is reproducible at zero-based SplitMix64 candidate index
746,229,884 with:

```bash
g++ -O3 -march=native -std=c++17 \
  problems/nfa-mortal-words/search_random_n5.cpp \
  -o /tmp/nfa_random5
/tmp/nfa_random5 1000000000 718281828
```

The data is in `witnesses.json` (which also holds the seven-state lower-bound
witness described below). Verify all witnesses with a separate
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

## Seven-state lower bound from seeded local search

`search_local.cpp` is a simulated-annealing search over ordered pairs of
row-restricted letters. A move replaces one row of one letter; the score is the
exact shortest mortal length (BFS from the full set), and moves to pairs that
are not 2-image-bounded or have no mortal word are rejected. Seeds are smaller
automata padded with dead states. Restart \(r\) uses its own generator seeded
from \((\text{seed}, r)\), so each restart is reproducible independently of the
thread count (given the same floating-point `exp`, which the Metropolis test
uses; Apple clang and GCC 16 on macOS replay restart 25 below identically). The
witness itself does not depend on this: it is verified independently.

Calibration against the exact values: at \(n=6\), seeded with the eight
five-state maximizer classes, 31 of 48 restarts of \(2\cdot10^6\) steps reach
the exact maximum 24 (27 of 48 from random starts); at \(n=5\) all 48 random
restarts reach 17.

At \(n=7\), seeded with the 28 six-state maximizer classes, 168 restarts of
\(5\cdot10^6\) steps (95 s wall with 6 threads) reach 35 in 13 restarts and
never more (per-restart bests 30 to 35); 48 restarts from random starts reach
35 in 5 restarts. An exploratory run with \(2\cdot10^7\) steps per restart
(stopped after 54 restarts because of machine load; not logged) also never
exceeded 35. The automaton found by restart 25 of the seeded run,

```text
a: 0 -> {4}, 1 -> {2}, 2 -> {},  3 -> {5}, 4 -> {3}, 5 -> {1,3}, 6 -> {6}
b: 0 -> {6}, 1 -> {6}, 2 -> {3}, 3 -> {6}, 4 -> {1}, 5 -> {0},   6 -> {2,5}
```

has shortest mortal word `bbabaaababaababaaababaabbabaaababaa` of length 35;
`verify_witnesses.py` checks it (record `binary-k2-n7-local-search-lower-bound`
in `witnesses.json`). So the seven-state binary maximum is **at least 35**. This
is only a lower bound: the search is heuristic and nothing excludes longer
seven-state examples. Reproduce the seeded run and the single restart that
found the witness with

```bash
cd problems/nfa-mortal-words
python3 - > /tmp/seeds_n6.txt <<'EOF'
import json
for r in json.load(open("exhaustive_maximizers.json"))["automata"]:
    if r["n"] == 6:  # one line of 2n row masks: rows of a, then rows of b
        print(" ".join(str(sum(1 << t for t in row))
                       for x in "ab" for row in r["transitions"][x]))
EOF
g++ -O3 -std=c++17 -pthread -DNFA_STATES=7 search_local.cpp -o /tmp/nfa_local7
/tmp/nfa_local7 /tmp/seeds_n6.txt 6 168 5000000 1     # full seeded run
/tmp/nfa_local7 /tmp/seeds_n6.txt 1 1 5000000 1 25    # restart 25 only
```

All logged local-search runs, with their exact commands, are in
[`logs/search_local_runs.txt`](logs/search_local_runs.txt).

## Claim boundary and next experiment

The exact extremal claims made here are for labelled, ordered-alphabet, binary
NFAs on at most six states. The original \(n\le4\) enumerators do not quotient
out state relabelling; the four-state implementation quotients letter swapping
during the scan but restores ordered counts by weights. The five- and six-state
enumerators quotient state relabelling during the scan and likewise restore
labelled ordered counts by orbit weights, so every maximizer count in the main
table is for labelled states and ordered letters; classes up to isomorphism are
reported separately.

For \(n=7\) only the local-search lower bound 35 is known here. The same scan
is out of reach as written: a scratch sample (not committed) of \(10^7\) random
row-restricted letters suggests roughly \(4\cdot10^8\) self-bounded letters
(2.3% of \(29^7\approx1.7\cdot10^{10}\)), hence about \(3\cdot10^{13}\)
pairs even after the \(S_7\) reduction, roughly 300 times the six-state scan
with more work per pair, and about 50 GB of subset tables. Pruning inside the
letter enumeration, a reduction over both letters, or a SAT encoding asking for
shortest mortality at least 36 would be needed. The general proof's \(n^3\)
upper bound for \(k=2\) comes from concatenating \(n\) pair-killing words of
quadratic length; the exact values \(1,3,7,10,17,24\) motivate testing whether
that extra factor can be removed by amortization.
