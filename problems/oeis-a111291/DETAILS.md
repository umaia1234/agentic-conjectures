**English** | [한국어](DETAILS.ko.md)

# OEIS A111291 / Colton's conjecture: proof details

This file gives the complete argument behind the claim in [README.md](README.md). Write
$\tau(k)$ for the number of divisors of $k$, $T(x)=\#\{1\le k\le x:\ \tau(k)\mid k\}$ for the
number of refactorable (tau) numbers up to $x$, and $\pi(x)$ for the number of primes up to $x$.
The claim is

\[
\pi(n)\le 2\,T(n)\qquad\text{for every integer } n\ge 0,
\]

with equality only at $n=0$ and $n=7$ ($\pi(7)=4$, $T(7)=2$).

The proof is computer-assisted. Three overlapping parts cover all $n$, and CI re-runs all three:

| Range | Method | Files | Section |
|---|---|---|---|
| $n\le 10^6$ | direct divisor-count sieve | `verify_small.py` | 2 |
| $10^6\le n\le 1.13\cdot 10^{13}$ | grid certificate (exact $T$ and $\pi$ at 66 points) | `verify_grid.py`, `tau_count.cpp`, `grid.txt` | 4 |
| $n\ge 10^{12}$ | analytic tail with exactly computed constants | `verify_tail.py`, `generators.cpp` | 3 |

In addition, a pointwise segmented sieve (`colton_sieve.cpp`, section 6) independently checks
every $n\le 10^{12}$, and the full grid reaches $10^{15}$, beyond Zelinsky's threshold
$7.42\cdot 10^{13}$ (section 3.4). Section 7 lists the cross-validation of the two independent
$T$ implementations.

## 1. Elementary facts

All six facts are proved in Lean in
[`AgenticConjectures/OeisA111291.lean`](../../AgenticConjectures/OeisA111291.lean) (theorem
names in parentheses).

- **(F1)** An odd refactorable number is a square (`isSquare_of_odd_refactorable`). If $n$ is
  odd and $\tau(n)\mid n$, then $\tau(n)=\prod_p(e_p+1)$ is odd, so every exponent $e_p$ is even.
- **(F2)** For odd $u$, $2u$ is refactorable iff $u$ is (`two_mul_refactorable_iff`), because
  $\tau(2u)=2\tau(u)$.
- **(F3)** Generators (the direction of Zelinsky's Lemma 6 that is used;
  `refactorable_mul_prime`). If $2\tau(d)\mid d$ and $p$ is a prime with $p\nmid d$, then
  $\tau(dp)=2\tau(d)$ divides $d$, hence $dp$. Such $d$ are *$p$-generators*; they are
  multiples of 4 (if $d$ is a square, $\tau(d)$ is odd and $d$ is an even square; otherwise
  $\tau(d)$ is even and $4\mid 2\tau(d)\mid d$).
- **(F4)** Disjoint families (`sum_card_primes_le_count`, `sum_primeCounting_sub_le`). Let $G$
  be a finite set of $p$-generators and let $P(d)$ bound the prime factors of $d\in G$ (below,
  $P(d)$ is the largest prime factor). The numbers $dp$ with $p$ prime and
  $P(d)<p\le x/d$ are refactorable by (F3), are at most $x$, and are pairwise distinct, because
  $p$ is the largest prime factor of $dp$. Hence, for every $x$,
  \[
  T(x)\ \ge\ \sum_{d\in G}\bigl(\pi(x/d)-\pi(P(d))\bigr). \tag{1}
  \]
  The Lean version uses truncated subtraction, which is stronger.
- **(F5)** Grid step (`grid_step`). $T$ and $\pi$ are non-decreasing, so if $x\le y$ and
  $\pi(y)\le 2T(x)$, then $\pi(n)\le 2T(n)$ for all $x\le n\le y$.
- **(F6)** $\pi(7)=2T(7)$ (`primeCounting_seven`, checked by `decide`), so the constant $2$
  cannot be lowered.

## 2. Small range: $n\le 10^6$

`verify_small.py` computes $\tau(k)$ for all $k\le 10^6$ with a plain divisor-count sieve and
checks $\pi(n)\le 2T(n)$ for every $1\le n\le 10^6$. Equality with $\pi(n)>0$ occurs only at
$n=7$ ($n=0$ is trivial). It also checks $T(10^6)=44705$ and $\pi(10^6)=78498$, the first grid
point. It shares no code with the C++ programs.

## 3. The analytic tail: $n\ge 10^{12}$

### 3.1 Bounds for $\pi$

The tail uses, for real $y\ge 599$ and real $x>1$,

\[
\pi(y) > \frac{y}{\ln y}\Bigl(1+\frac{1}{2\ln y}\Bigr), \qquad
\pi(x) < \frac{x}{\ln x}\Bigl(1+\frac{3}{2\ln x}\Bigr). \tag{2}
\]

Both follow from Dusart, *Estimates of some functions over primes without R.H.*,
[arXiv:1002.0442v1](https://arxiv.org/abs/1002.0442), Theorem 6.9, inequality (6.5):
$\frac{x}{\ln x}(1+\frac{1}{\ln x})\le\pi(x)$ for $x\ge 599$ and
$\pi(x)\le\frac{x}{\ln x}(1+\frac{1.2762}{\ln x})$ for $x>1$; the strict inequalities in (2)
follow because $\frac{1}{2\ln y}<\frac{1}{\ln y}$ and $1.2762<\frac32$. This statement was
checked against the arXiv PDF on 2026-10-24. The same weaker bounds are Rosser and
Schoenfeld's (3.1) and (3.2) (Illinois J. Math. 6 (1962), Theorem 1, for $y\ge 59$ and $x>1$),
and they also follow from Dusart, Math. Comp. 68 (1999), 411–415, the source Zelinsky cites.
Those two papers were not re-read for this work.

### 3.2 The inequality

Let $G$ be the set of $p$-generators $d\le D=28\,653\,696$ (the set Zelinsky uses) and put

\[
A=\sum_{d\in G}\frac1d,\qquad A_1=\sum_{d\in G}\frac{\ln d}{d},\qquad
B=\sum_{d\in G}\pi(P(d)).
\]

Let $x\ge 599\max G$ be real and $L=\ln x$. For every $d\in G$ we have $x/d\ge 599$ and
$t_d=\ln(x/d)=L-\ln d>0$, so (2) gives $\pi(x/d)>\frac{x}{d}\,\varphi(t_d)$ with
$\varphi(t)=\frac1t+\frac1{2t^2}$. The function $\varphi$ is convex and decreasing on $t>0$, so
for $c=\ln d\ge 0$,

\[
\varphi(L-c)\ \ge\ \varphi(L)-c\,\varphi'(L)=\varphi(L)+c\Bigl(\frac1{L^2}+\frac1{L^3}\Bigr)
\ \ge\ \varphi(L)+\frac{c}{L^2}.
\]

Summing over $G$, using (1) and the upper bound in (2):

\[
2T(x)-\pi(x)\ >\ x\Bigl(\frac{2A}{L}+\frac{A+2A_1}{L^2}-\frac1L-\frac{3}{2L^2}\Bigr)-2B
\ =\ f(x)-2B,\qquad f(x)=x\Bigl(\frac{c_1}{L}+\frac{c_2}{L^2}\Bigr),
\]

with $c_1=2A-1$ and $c_2=A+2A_1-\frac32$. If $c_1,c_2>0$, then $f$ is increasing for $x>e^2$
(the derivatives of $x/L$ and $x/L^2$ are $(L-1)/L^2$ and $(L-2)/L^3$), and for fixed $x$ the
bracket decreases in $L$. With $X=10^{12}$ and $\ln X<28$, every $x\ge X$ satisfies
$f(x)\ge f(X)\ge X\bigl(\frac{c_1}{28}+\frac{c_2}{28^2}\bigr)$. Therefore

\[
X\ge 599\max G\quad\text{and}\quad X\Bigl(\frac{c_1}{28}+\frac{c_2}{28^2}\Bigr)>2B
\quad\Longrightarrow\quad \pi(n)<2T(n)\ \text{for every integer } n\ge X. \tag{3}
\]

### 3.3 The numbers (`verify_tail.py`)

- `generators.cpp` lists the 413,980 $p$-generators $d\le 28\,653\,696$ with their
  factorizations, in increasing order. `verify_tail.py` re-checks every listed $d$: the factors
  are increasing primes, their product is $d$, $2\tau(d)\mid d$, and the listed values are
  strictly increasing, so no $d$ is counted twice. The generator program is therefore not
  trusted: (1) holds for any set of $p$-generators, so a missing generator could only weaken the
  bound.
- Zelinsky uses the generators $\le 28\,653\,696$ but counts 413,980 of them "less than"
  $28\,653\,696$. Since $28\,653\,696=2^7\cdot 3^3\cdot 8291$ is itself a generator, 413,979 lie
  strictly below it; this repository uses the consistent reading $d\le 28\,653\,696$ (413,980).
- $B=3\,348\,506\,095$ exactly (sieve of primes up to $D/4$, which bounds every prime factor of a
  generator).
- $A\ge 0.508000047238$ (Zelinsky: "over .508") and $A_1\ge 3.149503211455$, computed as lower
  bounds in fixed point with scale $2^{100}$, every term rounded down (the script also prints
  every bound rounded down). For $\ln d$ the script writes $d=2^k z$ with $1\le z<2$ and uses
  $\ln z=2\operatorname{artanh} s\ge 2(s+s^3/3+s^5/5+s^7/7)$ with $s=(z-1)/(z+1)$ (all series
  terms are positive) and $\ln 2\ge\sum_{j<160}1/(j2^j)$.
- $c_1>0$, $c_2>0$; $e^{28}>10^{12}$ is checked with a partial sum of the exponential series;
  $599\max G=17\,163\,563\,904\le 10^{12}$; and
  $X(\frac{c_1}{28}+\frac{c_2}{28^2})/(2B)\ge 1.0960$. All comparisons are exact rational
  arithmetic.

By (3), $\pi(n)<2T(n)$ for every $n\ge 10^{12}$.

### 3.4 Relation to Zelinsky's Theorem 8

Zelinsky (J. Integer Seq. 5 (2002), Article 02.2.8, Theorem 8) proves $T(n)>\pi(n)/2$ for
$n>7.42\cdot 10^{13}$ with the same generator set. His Lemma 9 states the lower bound
$A\pi(n)-B$ with $B=\sum(\pi(g(a_i))+1)$, and its one-line justification ("an error of at most
1" per summand) does not by itself establish that bound. The proof of Theorem 8 does not need
it: the inequality used there, $T(n)>0.508\,\frac{n}{\log n}(1+\frac{0.992}{\log n})-B$ for
$n>598\cdot 28\,653\,696$, follows from (1) by applying Dusart's lower bound to each
$\pi(n/a_i)$ and using that $t\mapsto\frac1t(1+\frac{0.992}{t})$ is decreasing. His bound
$B<8\,694\,520\,815$ is consistent with the exact value
$\sum(\pi(g(a_i))+1)=3\,348\,920\,075$, and a floating-point re-evaluation of his final step
confirms it at $n=10^{13.87}$ (ratio $1.0001$, growing with $n$). The grid of section 4 covers
$[10^6,10^{15}]\supset[10^6,7.42\cdot10^{13}]$, so Theorem 8 gives a second, independent route
to the full statement. The tail above lowers the threshold to $10^{12}$ by computing $B$
exactly and keeping the gain $\ln d$ in $\ln(x/d)$ (the $A_1$ term).

## 4. The grid: $10^6\le n\le 10^{15}$

`grid.txt` lists 77 points $10^6=x_0<x_1<\dots<x_{76}=10^{15}$ with exact $T(x_i)$ and
$\pi(x_i)$. `verify_grid.py` recomputes both columns with `tau_count` and checks
$\pi(x_{i+1})\le 2T(x_i)$ for every $i$; by (F5) this proves $\pi(n)\le 2T(n)$ on
$[10^6,10^{15}]$. The largest ratio $\pi(x_{i+1})/2T(x_i)$ is $0.9999848\ldots<1$
(`logs/verify_grid_full.log`), so the inequality is strict there. CI runs the prefix up to the
first point $\ge 10^{13}$ (66 points up to $1.13\cdot 10^{13}$, about 6 s), which covers the gap
between section 2 and section 3; the full grid is a non-CI command (about 2.5 minutes and 0.7 GB
at $x=10^{15}$). The points were chosen greedily with three significant digits; the choice does
not matter for the proof.

The $\pi$ column comes from the Lucy_Hedgehog table inside `tau_count`. It was cross-checked at
all 77 points with primecount 8.8 (`crosscheck_primecount.py`, `logs/crosscheck_primecount.log`).

## 5. The structured counter `tau_count.cpp`

`tau_count x` returns $T(x)$ and $\pi(x)$ in about $0.3$ s at $x=10^{12}$ and $36$ s at
$x=10^{15}$. Splitting by the 2-adic valuation of $n$:

- odd $n$: by (F1), $n=s^2$ with $s$ odd; count odd $s\le\sqrt x$ with $\tau(s^2)\mid s^2$;
- $n=2u$ with $u$ odd: by (F2), this count is $T_{\rm odd}(x/2)$;
- $4\mid n$: a depth-first search over $n=2^a p_1^{e_1}\cdots p_k^{e_k}$. For $n<2^{64}$ every
  exponent is at most 63, so every prime factor of $\tau(n)=\prod(e_i+1)$ is at most 61.
  Write $n=dm$ where $d$ collects the primes $\le 61$ and $m$ the primes $>61$. Since
  $\gcd(\tau(n),m)=1$ and $\tau(n)=\tau(d)\tau(m)$, we get $\tau(n)\mid n$ iff $\tau(d)\mid d$ and
  $\tau(m)\mid d/\tau(d)$. The search enumerates the prefixes $d$ explicitly and counts the
  admissible $m\le x/d$ with a recursion `gen(A, y, P)` that aggregates the largest prime of $m$
  through $\pi$. In that recursion, every exponent $a$ of $m'$ satisfies $(a+1)\mid A'$, hence
  $a+1\ge s$ for the least divisor $s\ge 2$ of $A'$, which gives the pruning bound
  $p^{e+s-1}<y$.

$\pi(v)$ is only needed at $v\le\sqrt x$ or $v=\lfloor x/k\rfloor$, which the Lucy_Hedgehog
table provides. The source comments describe the partition of the search tree in detail.

## 6. The pointwise sieve `colton_sieve.cpp`

`colton_sieve N` checks $\pi(n)\le 2T(n)$ for every $n\le N$ without `tau_count`. It sieves
segments of $2^{21}$ numbers in parallel: primes by an odd-only Eratosthenes sieve, $\tau(k)$ for
$k\equiv 0\pmod 4$ by a segmented factor sieve, and the refactorable numbers that are odd or
$\equiv 2\pmod 4$ ($1$, $2$, $s^2$, $2s^2$ by (F1) and (F2)) from a precomputed list. For each
segment it records the exact minimum of $2T-\pi$ over the primes of the segment. Since $T$ can
only grow between consecutive primes while $\pi$ stays constant, these minima cover every $n$.

The run for $N=10^{12}$ (`logs/sieve_1e12.log`) reports $T(10^{12})=26\,568\,322\,474$,
$\pi(10^{12})=37\,607\,912\,018$, global minimum of $2T(p)-\pi(p)$ over primes equal to $0$, first
attained at $p=7$, and `RESULT: VERIFIED pi(n) <= 2T(n) for all n <= 1000000000000`. The
`TAIL` lines give the minimum of $2T(p)-\pi(p)$ over primes $p$ from (roughly) each power of ten
on, for example $23\,800$ from $2\,097\,152$ on; their ratio column, a floating-point evaluation
of the coarse bound $\min 2T(L-1)/\pi(R-1)$ over segments $[L,R)$, is for orientation only and is
not used. The program also prints
$T$ and $\pi$ at 1433 checkpoints (all powers of ten, random values and values around segment
boundaries).

## 7. Cross-validation of the two $T$ implementations

| Check | Result |
|---|---|
| `test_bruteforce.py`: brute force up to $2\cdot 10^7$ against `colton_sieve` (454 checkpoints, 1 and 3 threads, all `TAIL` minima) and `tau_count` (8099 values of $x$) | 0 mismatches |
| `crosscheck_sieve_log.py`: `tau_count` at the 1433 checkpoints of the $10^{12}$ sieve run | 0 mismatches |
| OEIS A111291 data $a(0),\dots,a(11)$ | reproduced by both programs |
| `spot_check.py`: interval sieve against `tau_count` on intervals of length $\approx 2\cdot 10^9$ around $10^{13}$, $7.42\cdot 10^{13}$, $10^{14}$, $10^{15}$ (5 points each) | all agree |
| `crosscheck_primecount.py`: $\pi$ at the 77 grid points against primecount 8.8 | all agree |

The two programs share only the reductions (F1) and (F2), which are proved in Lean, and the brute
force in `test_bruteforce.py` assumes neither.

## 8. Values of $T(10^k)$

| $k$ | $T(10^k)=$ A111291$(k)$ | $\pi(10^k)$ |
|---:|---:|---:|
| 0 | 1 | 0 |
| 1 | 4 | 4 |
| 2 | 16 | 25 |
| 3 | 92 | 168 |
| 4 | 665 | 1229 |
| 5 | 5257 | 9592 |
| 6 | 44705 | 78498 |
| 7 | 394240 | 664579 |
| 8 | 3558181 | 5761455 |
| 9 | 32608999 | 50847534 |
| 10 | 302172507 | 455052511 |
| 11 | 2823898245 | 4118054813 |
| 12 | 26568322474 | 37607912018 |
| 13 | 251342379436 | 346065536839 |
| 14 | 2388671712980 | 3204941750802 |
| 15 | 22789342999100 | 29844570422669 |

The values for $k\le 11$ agree with the OEIS data. The values for $12\le k\le 15$ come from
`tau_count` (for $k=12$ also from the sieve). They have not been submitted to OEIS.

## 9. Scope and trust

- Lean checks only the elementary facts (F1)–(F6). The computations and the analytic bounds (2)
  are not formalized; mathlib has no explicit Dusart-type bounds.
- The proof trusts: the C++ and Python implementations (with the cross-checks of section 7), the
  compilers and interpreters, and the published bounds (2). For $n\le 10^{12}$ two independent
  programs (the grid via `tau_count` and the sieve) each prove the statement; for $n\ge 10^{12}$
  the tail is independent of both.
- The argument has not been reviewed by a human mathematician.
