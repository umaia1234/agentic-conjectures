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
run.

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

Neither (E385-1) nor the odd-index theorem controls arbitrarily large even
indices. In particular, they do not prove eventual strict inequality, do not
prove $F(n)-n\to\infty$, and do not establish the conjectured
$(1-o(1))\sqrt n$ lower behavior. The canonical page still reports the
problem as open, and no novelty is claimed without external review.
