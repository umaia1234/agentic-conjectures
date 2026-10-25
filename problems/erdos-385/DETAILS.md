**English** | [한국어](DETAILS.ko.md)

# Erdős #385: proof and finite-certificate details

## 1. Definition and exact finite statement

For a composite integer $m$, let $p(m)$ be its least prime factor and set

\[
F(n)=\max_{\substack{m<n\\m\text{ composite}}}(m+p(m)).
\]

The computer-assisted theorem proved here is

\[
\boxed{267681\le n\le10^9\quad\Longrightarrow\quad F(n)>n.}
\tag{E385-1}
\]

Together with the Lean lower bound $F(n)\ge n$ for $n\ge5$, the
certificate also classifies all equalities in the range:

\[
\#\{n:6\le n\le10^9,\ F(n)=n\}=100,
\]

and the largest equality is $n=267680$. The complete list is certificate
data rather than a hand-maintained table; it is stored in
[`billion_result.json`](billion_result.json) and checked on every verifier
run. Section 8 extends (E385-1) and this classification through $10^{11}$
with two further independent programs; the equality cases are the same 100.

The original 1979 wording asks whether $F(n)\le n$ infinitely often, then
observes that plausible conjectures on primes predict only finitely many such
indices. The current problem page asks the equivalent opposite-direction
eventual question $F(n)>n$, plus divergence of $F(n)-n$. The bounded theorem
(E385-1) concerns this current formulation but decides neither one.

## 2. Infinite elementary subfamily

Suppose first that $n\ge5$ is odd. Then $m=n-1\ge4$ is even and composite,
and $p(m)=2$. Consequently

\[
F(n)\ge m+p(m)=(n-1)+2=n+1>n.
\tag{E385-2}
\]

If $n\ge5$ is even, then in fact $n\ge6$. Now $m=n-2\ge4$ is even and
composite, so

\[
F(n)\ge(n-2)+2=n.
\tag{E385-3}
\]

These two arguments are formalized as
`AgenticConjectures.Erdos385.odd_index_lt_F` and
`AgenticConjectures.Erdos385.index_le_F`. They explain why every exceptional
value recorded by the computation is an equality, never a strict failure.

## 3. Coverage intervals

A composite $m$ proves $F(n)>n$ precisely for the later indices

\[
m<n<m+p(m),
\]

or equivalently the integer interval

\[
n\in[m+1,m+p(m)-1].
\tag{E385-4}
\]

When scanning $n$ upward, define the farthest covered endpoint

\[
R(n)=\max_{\substack{m<n\\m\text{ composite}}}(m+p(m)-1).
\]

Then

\[
F(n)-n=R(n)+1-n.
\tag{E385-5}
\]

The dense implementation computes this identity directly after constructing
the least prime factor of every integer through the bound.

There is a second, lower-memory reduction. For odd $n\ge5$, equation
(E385-2) already gives strict inequality. For even $n\ge6$, every even
composite $m<n$ has $p(m)=2$ and hence $m+p(m)\le n$. Thus a strict
improvement can come only from an odd composite $m$. It is therefore enough
to segment-sieve the odd integers and retain only their record coverage
endpoints; equation (E385-3) supplies the equality baseline.

## 4. Two independent exhaustive implementations

The verifier uses the following independent algorithms.

1. `ep430_experiment.cpp` uses a dense Euler sieve. It stores `spf[m]` for
   every $m\le10^9$, visits each integer once, and updates the endpoint
   $m+p(m)-1$.
2. `ep430_segmented.cpp` first sieves primes only through
   $\sqrt{10^9}$, then marks the least prime factors of odd integers in
   blocks of 16,000,000. It uses the parity reduction above rather than the
   dense program's all-integer recurrence.

The Python wrapper does not accept agreement only on the last exception. It
requires equality of the entire 100-element list and of every record

\[
\max\{n\le10^9:F(n)-n\le t\}
\]

for $t\in\{0,1,2,3,5,10,20,50,100,200,500,1000\}$. It then compares those
objects with the committed JSON certificate. A disagreement or altered
certificate makes the command fail.

## 5. Reproduction and resource audit

From the repository root, run

```bash
python3 problems/erdos-385/verify_billion.py
```

The measured 2026-08-12 run was:

| Component | Wall time | Peak memory |
|---|---:|---:|
| Dense linear sieve | 8.87 s | about 4.1 GiB |
| Odd segmented sieve | 6.67 s | about 20 MiB |
| Wrapper including compilation | 16.31 s | 4,108,120 KiB |

No binary is committed. Compilation products live in a temporary directory
under `/tmp` and are removed automatically.

## 6. Faithfulness and scope

The canonical and FormalConjectures definitions maximize the same value over
composite $m<n$. The local Lean module makes compositeness explicit as
$1<m$ and $m$ nonprime, and uses a finite `Finset.sup`. The only semantic
difference is its value at an empty candidate set; all claims begin at
$n\ge5$, where $m=4$ is available. The program's `uint32_t` indices are
exact throughout $n\le10^9$, and the endpoint arithmetic is promoted to
`uint64_t`.

None of (E385-1), (E385-9) and the Lean families of Sections 2 and 7
controls the even indices $n>10^{11}$ with $n-1$ prime. In particular, they do not prove eventual strict inequality, do not
prove $F(n)-n\to\infty$, and do not establish the conjectured
$(1-o(1))\sqrt n$ lower behavior. The canonical page still reports the
problem as open, and no novelty is claimed without external review.


## 7. Further elementary families (Lean)

The first argument of Section 2 does not need $n$ to be odd. Whenever
$n\ge5$ and $n-1$ is not prime, $m=n-1\ge4$ is composite and $p(m)\ge2$, so

\[
F(n)\ge(n-1)+p(n-1)\ge n+1>n.
\tag{E385-6}
\]

For example, if $n\ge5$ and $n\equiv4\pmod 6$, then $n\ge10$ and $n-1\ge9$
is an odd multiple of $3$, hence composite. Together with the odd indices,
only $n\equiv0,2\pmod 6$ remain possible equality cases. Combined with
(E385-3), (E385-6) gives a necessary condition:

\[
n\ge5,\ F(n)=n\quad\Longrightarrow\quad n\text{ even and }n-1\text{ prime}.
\tag{E385-7}
\]

All 100 computed equality cases satisfy (E385-7); `verify_extended.py`
checks this with an exact primality test. The same argument applied to later
witnesses such as $m=n-3$ yields further congruence classes. The Lean module
records only the $n-1$ family.

Finally, the Lean module proves, for every $n$, the coverage criterion that
both programs implement:

\[
n<F(n)\iff\exists\,m<n\text{ composite with }n<m+p(m).
\tag{E385-8}
\]

| Declaration | Statement |
|---|---|
| `AgenticConjectures.Erdos385.lt_F_iff` | (E385-8), for every $n$ |
| `AgenticConjectures.Erdos385.lt_F_of_not_prime_pred` | (E385-6) |
| `AgenticConjectures.Erdos385.lt_F_of_mod_six_eq_four` | $n\ge5$, $n\equiv4\pmod6\Rightarrow F(n)>n$ |
| `AgenticConjectures.Erdos385.even_and_prime_pred_of_F_eq` | (E385-7) |

## 8. Extension through $10^{11}$

### 8.1 Statement

Two new exhaustive programs extend the certificate of Section 1:

\[
\#\{n:6\le n\le10^{11},\ F(n)=n\}=100,
\qquad
\boxed{267681\le n\le10^{11}\Longrightarrow F(n)>n.}
\tag{E385-9}
\]

The 100 equality cases are exactly the ones already found below $10^9$.

### 8.2 Independent segments

Let $6\le\mathrm{lo}\le\mathrm{hi}$, $r=\lfloor\sqrt{\mathrm{hi}}\rfloor$ and
$W=\mathrm{lo}-r-2$. A composite $m<W$ has $p(m)\le\lfloor\sqrt m\rfloor\le r$,
hence $m+p(m)-1\le\mathrm{lo}-4$. For $n\in[\mathrm{lo},\mathrm{hi}]$, the
even composite among $n-2$ and $n-1$ already gives $R(n)\ge n-1\ge\mathrm{lo}-1$.
Thus omitting every $m<W$ changes neither $R(n)$ nor $F(n)$ on the segment.
`allint_segments.cpp` starts each segment at $W$. When `odd_carry.cpp` is
asked for a range with $\mathrm{lo}>6$, it starts at an odd number
$W'\le\mathrm{lo}-2r-9$. Every omitted odd composite then has
$m+p(m)<\mathrm{lo}\le n$, below the parity baseline $n+[n\text{ odd}]$. The
full $10^{11}$ run of `odd_carry.cpp` starts at $m=3$ and omits nothing.

### 8.3 The two programs

| | `allint_segments.cpp` | `odd_carry.cpp` |
|---|---|---|
| Integers sieved | every integer | odd integers only |
| Least prime factor | primes written in decreasing order with unconditional overwrite, so the smallest prime is written last | primes applied in increasing order; the first prime reaching an entry is kept |
| Evaluation | $F(n)=1+R(n)$ over all composites $m<n$, with an abort if $F(n)<n$ | parity reduction $F(n)=\max(n+[n\text{ odd}],\,1+R_{\mathrm{odd}}(n))$ |
| Decomposition | each $10^9$ segment independent, from its warm-up start $W$ | one exact carried scan of $[3,10^{11}]$ |
| Parallelism | threads take whole segments | workers sieve blocks ahead of a single in-order scanner |

Both write one JSON record per index segment
$(k\cdot10^9,(k+1)\cdot10^9]\cap[6,10^{11}]$, $k=0,\ldots,99$.

### 8.4 Segment records and fingerprint

A record contains the equality cases, the minimum slack $s(n)=F(n)-n$ with
the first $n$ attaining it, and $\max\{n:s(n)\le t\}$ for 18 thresholds
$t\in\{0,1,2,3,5,10,20,50,100,200,500,1000,2000,5000,10^4,2\cdot10^4,5\cdot10^4,10^5\}$.
It also contains the exact sum $\sum s(n)$ and the fingerprint

\[
H=\sum_n \mathrm{splitmix64}\bigl(2^{20}n+s(n)\bigr)\bmod 2^{64}.
\]

Every slack satisfies $s(n)\le\max(1,p(m)-1)<\sqrt{10^{11}}<2^{20}$, where $m$
is the maximizing composite, so the key $2^{20}n+s(n)$ determines the pair
$(n,s(n))$. The verifier compares the equality cases, threshold records,
minima and sums exactly. Matching $H$ on all 100 segments is a probabilistic
check, up to a 64-bit collision, that the two programs computed the same
value $F(n)$ at every one of the $10^{11}-5$ indices.

### 8.5 Results

The last $n\le10^{11}$ with $s(n)\le t$, for each threshold:

| $t$ | last $n$ | $t$ | last $n$ |
|---:|---:|---:|---:|
| 0 | 267680 | 200 | 810569 |
| 1 | 267683 | 500 | 1823893 |
| 2 | 267683 | 1000 | 5540903 |
| 3 | 267683 | 2000 | 16348153 |
| 5 | 267683 | 5000 | 68722999 |
| 10 | 267689 | 10000 | 221789563 |
| 20 | 267689 | 20000 | 790192477 |
| 50 | 267779 | 50000 | 3974083249 |
| 100 | 279229 | 100000 | 14416872451 |

The first twelve records, $t\le1000$, equal those of `billion_result.json`.
No index in $(10^9,10^{11}]$ has $s(n)\le20000$:

| Range | $\min s(n)$ | First attained at |
|---|---:|---:|
| $(10^9,10^{10}]$ | 23331 | 1009345789 |
| $(10^{10},10^{11}]$ | 81881 | 10119571529 |

Over $6\le n\le10^{11}$, $\sum s(n)=20395584727328899$, and the combined
fingerprint is `cc63c411546fd132`.

### 8.6 Reproduction and resources

```bash
python3 problems/erdos-385/verify_extended.py          # CI mode
python3 problems/erdos-385/verify_extended.py --full   # all 100 segments
```

CI mode checks, in order: the SHA-256 values of both logs; their headers,
contiguous coverage of $[6,10^{11}]$ and agreement on every record; the
recombined summary against `extended_result.json` and segment 0 against
`billion_result.json`; (E385-7) for every equality case, by an exact
primality test; and, after recompiling both programs, the first and last
segments recomputed by each program, together with a comparison of both
programs against trial division on $[6,30000]$. `--full` recomputes all
100 segments instead of two.

| Run (2026-10-24, shared Apple M5 Max, load average above 40) | Wall time | CPU time | Peak memory |
|---|---:|---:|---:|
| `allint_segments`, 2 threads (committed log) | 447 s | 419 s | 6.9 MB |
| `odd_carry`, 2 threads (committed log) | 443 s | 298 s | 5.6 MB |
| `verify_extended.py` (CI mode) | 10.2 s | 17.1 s | 118 MB |
| `verify_extended.py --full`, 4 threads | 10.3 min | 11.7 min | 118 MB |

The two production runs ran concurrently. Binaries are compiled into a
temporary directory and never committed. As a check on the verifier itself,
it fails when one log value, one equality case of the summary, or one
segment fingerprint is altered (the last with the log hash updated to
match). It also fails on two deliberately injected bugs: keeping the largest
instead of the smallest prime in `odd_carry.cpp`, and a too-short warm-up in
`allint_segments.cpp`.

### 8.7 Scope

(E385-9) is a finite statement; it does not decide either asymptotic
question. The fingerprint is a cross-check of the two computations, not an
independent certificate of any value of $F$. The source hashes and timings
in `extended_result.json` are provenance only.
