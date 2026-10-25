**English** | [한국어](README.ko.md)

# Erdős problem #385: elementary subfamilies and exact verification through $10^{11}$

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

Both questions remain open. This directory records infinite elementary
subfamilies and an exact finite classification; it does not claim a solution
of either asymptotic question or claim novelty.

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

The same module proves $F(n)>n$ whenever $n\ge5$ and $n-1$ is not prime, in
particular for every $n\ge5$ with $n\equiv4\pmod 6$. Hence every equality
case has a restricted form:

\[
n\ge5,\ F(n)=n\Longrightarrow n\text{ even and }n-1\text{ prime}.
\]

The exact computation then proves the bounded statement

\[
\boxed{267681\le n\le10^{11}\Longrightarrow F(n)>n.}
\]

There are exactly 100 equality cases $F(n)=n$ for
$6\le n\le10^{11}$, all below $10^9$; the last three are
$8742,267672,267680$. The full sorted list and the checked slack-threshold
records are in [`billion_result.json`](billion_result.json) and
[`extended_result.json`](extended_result.json).

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
alone used about 20 MiB. The combined verifier is registered as CI-feasible.

The proof and the exact reduction implemented by both programs are given in
the bilingual [mathematical details](DETAILS.md).

## Extension through $10^{11}$ (2026-10-24)

Two new multithreaded programs classify every index $6\le n\le10^{11}$:

- [`allint_segments.cpp`](allint_segments.cpp) sieves all integers. It
  writes primes in decreasing order, so the smallest prime overwrites last,
  and evaluates $F(n)$ directly over all composites. Each $10^9$ index
  segment is handled independently after an explicit warm-up.
- [`odd_carry.cpp`](odd_carry.cpp) sieves odd integers only. It keeps the
  first (smallest) prime reaching each entry and uses the parity reduction.
  One exact scan carries the running maximum from $m=3$ through $10^{11}$.

The programs share only the output format. Each writes one record per index
segment $(k\cdot10^9,(k+1)\cdot10^9]$, 100 segments in all. A record lists
the equality cases, the minimum of $F(n)-n$, and the last $n$ with
$F(n)-n\le t$ for 18 thresholds. It also has the exact sum of $F(n)-n$ and a
64-bit fingerprint of the whole sequence $(n,F(n)-n)$. The two committed
logs agree on every record. The method, the warm-up lemma and the fingerprint
are described in Section 8 of the [mathematical details](DETAILS.md).

**Result.** There are exactly 100 equality cases $F(n)=n$ for
$6\le n\le10^{11}$. They are the same 100 values found below $10^9$, so

\[
\boxed{267681\le n\le10^{11}\Longrightarrow F(n)>n.}
\]

No index in $(10^9,10^{11}]$ has $F(n)-n\le20000$. The minimum of
$F(n)-n$ is 23331 on $(10^9,10^{10}]$, first attained at $n=1009345789$,
and 81881 on $(10^{10},10^{11}]$, first attained at $n=10119571529$. In
particular, the twelve slack-threshold records of
[`billion_result.json`](billion_result.json), for $t\le1000$, are unchanged
through $10^{11}$. Section 8.5 of the [mathematical details](DETAILS.md)
lists all 18 records.

The summary is [`extended_result.json`](extended_result.json). The raw
per-segment logs are [`logs/allint_segments_6_1e11.jsonl`](logs/allint_segments_6_1e11.jsonl)
and [`logs/odd_carry_6_1e11.jsonl`](logs/odd_carry_6_1e11.jsonl); their
SHA-256 values are recorded in the summary.

**Reproduction.** From the repository root:

```bash
python3 problems/erdos-385/verify_extended.py          # CI mode
python3 problems/erdos-385/verify_extended.py --full   # recompute all 100 segments
```

The committed logs come from one run of each program on 2026-10-24, compiled
with Apple clang 21 at `-O3` and run concurrently, two threads each, on a
shared Apple M5 Max with load average above 40. `allint_segments` took 447 s
of wall time (419 s CPU) and `odd_carry` 443 s (298 s CPU); each used less
than 7 MB of memory. CI mode checks the log hashes, the agreement of all 100
records and the recombined summary. It then recompiles both programs,
recomputes the first and last $10^9$ segments with each, and compares both
with trial division on $[6,30000]$. Here it took about 10 s of wall time and
118 MB of peak memory. `--full` recomputes all 100 segments with both
programs (10.3 min of wall time with four threads here); it is not registered
as CI-feasible.

**Not claimed.** This is a finite verification; neither asymptotic question
is decided. The fingerprint is a cross-check between the two programs, not a
certificate on its own. The exact objects (equality cases, threshold records,
minima and sums) are compared exactly.

## Statement faithfulness and upstream status

The local Lean definition takes the supremum of the finite range $m<n$ and
spells out “composite” as $1<m$ and $m$ nonprime. It therefore equals the
canonical maximum whenever the range is nonempty, and differs only by being
definitionally zero at the empty small-index boundary. Every theorem here
except the coverage criterion `lt_F_iff` starts at $n=5$, so the boundary
convention cannot affect it. `lt_F_iff` holds for every $n$; at the empty
boundary $n\le4$ both of its sides are false. Lean's `Nat.minFac` is the
least prime factor of every $m\ge2$, so it agrees with $p(m)$ on composites.
There is no index-base or natural-subtraction ambiguity; the occurrences of
$n-1$ and $n-2$ are protected by lower bounds.

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
