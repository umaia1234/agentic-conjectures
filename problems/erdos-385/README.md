**English** | [한국어](README.ko.md)

# Erdős problem #385: odd indices and an exact billion-term verification

Let $p(m)$ be the least prime factor of a composite integer $m$, and put

\[
F(n)=\max_{\substack{m<n\\m\text{ composite}}}\bigl(m+p(m)\bigr).
\]

The 1979 paper asks the original question (printed p. 73):

> “Is it true that $F(n)\le n$ for infinitely many $n$?”

It immediately notes that plausible prime conjectures predict only finitely
many such values. Accordingly, the [current canonical problem
page](https://www.erdosproblems.com/385) asks the logically opposite eventual
form, together with a stronger divergence question:

> Is it true that $F(n)>n$ for all sufficiently large $n$? Does
> $F(n)-n\to\infty$ as $n\to\infty$?

Both questions remain open. This directory records one infinite elementary
subfamily and an exact finite classification; it does not claim a solution of
either asymptotic question or claim novelty.

## Verified outcomes

The Lean module [`Erdos385.lean`](../../AgenticConjectures/Erdos385.lean)
kernel-checks, without `sorry`, extra axioms, or `native_decide`, that

\[
n\ge5\Longrightarrow F(n)\ge n
\]

and the stronger odd-index result

\[
n\ge5,\quad n\text{ odd}\Longrightarrow F(n)>n.
\]

The exact computation then proves the bounded statement

\[
\boxed{267681\le n\le10^9\Longrightarrow F(n)>n.}
\]

There are exactly 100 equality cases $F(n)=n$ for
$6\le n\le10^9$; the last three are
$8742,267672,267680$. The full sorted list and the checked slack-threshold
records are in [`billion_result.json`](billion_result.json).

## Independent verification

[`verify_billion.py`](verify_billion.py) compiles and cross-checks two
algorithmically distinct programs over the full interval:

- [`ep430_experiment.cpp`](ep430_experiment.cpp) constructs a dense linear
  least-prime-factor sieve.
- [`ep430_segmented.cpp`](ep430_segmented.cpp) keeps only an odd segmented
  sieve and derives the coverage recurrence independently.

The wrapper requires both complete equality-case lists and all recorded
thresholds to agree before comparing them with the committed JSON result.
Run it from the repository root:

```bash
python3 problems/erdos-385/verify_billion.py
```

On 2026-08-12 the dense and segmented runs took 8.87 s and 6.67 s,
respectively; the wrapper took 16.31 s and peaked at 4,108,120 KiB because of
the deliberately memory-heavy dense cross-check. The segmented implementation
alone used about 20 MiB. Both are below the local two-hour budget, and the
combined verifier is registered as CI-feasible.

The proof and the exact reduction implemented by both programs are given in
the bilingual [mathematical details](DETAILS.md).

## Statement faithfulness and upstream status

The local Lean definition takes the supremum of the finite range $m<n$ and
spells out “composite” as $1<m$ and $m$ nonprime. It therefore equals the
canonical maximum whenever the range is nonempty, and differs only by being
definitionally zero at the empty small-index boundary. Every theorem here
starts at $n=5$, so the boundary convention cannot affect it. There is no
index-base or natural-subtraction ambiguity; the occurrences of $n-1$ and
$n-2$ are protected by lower bounds.

The exact FormalConjectures declarations are preserved in the local
[upstream snapshot](upstream/README.md). Their research statements contain
`sorry`; only the elementary upper bound in that snapshot is proved. The
historical `ep430_*` filenames were retained because part (i) is equivalent
to the first question of Erdős #430.

Google DeepMind's AlphaProof Nexus `science-submission` snapshot commit
[`0647711a71183c1ea492ad60860776617ce1ea88`](https://github.com/google-deepmind/alphaproof-nexus-results/tree/0647711a71183c1ea492ad60860776617ce1ea88)
lists all three FormalConjectures declarations as attempted, but contains no
successful #385 result. This is attempt provenance only.

## Sources checked

- [Erdős Problems #385](https://www.erdosproblems.com/385), checked
  2026-08-12; it still labels the asymptotic questions open.
- P. Erdős, [*Some unconventional problems in number
  theory*](https://users.renyi.hu/~p_erdos/1979-23.pdf), *Acta Math. Acad.
  Sci. Hungar.* 33 (1979), 71--80; the original question is on printed p. 73.
- P. Erdős and R. L. Graham, [*Old and New Problems and Results in
  Combinatorial Number
  Theory*](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf),
  1980, p. 74.
- [OEIS A322292](https://oeis.org/A322292), the sequence $F(n)$; its linked
  table previously covered $n\le10000$.
