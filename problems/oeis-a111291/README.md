**English** | [한국어](README.ko.md)

# OEIS A111291 — Colton's conjecture $\pi(n)\le 2T(n)$

## Verdict

Colton's conjecture on refactorable numbers holds for **every** $n$: with $\tau(k)$ the number of
divisors of $k$, $T(n)=\#\{1\le k\le n:\ \tau(k)\mid k\}$ and $\pi(n)$ the number of primes
$\le n$,

\[
\pi(n)\le 2\,T(n)\qquad(n\ge 0),
\]

with equality only at $n=0$ and $n=7$. This is a **computer-assisted proof**: a brute-force check
for $n\le 10^6$, a grid certificate with exact values of $T$ and $\pi$ for
$10^6\le n\le 1.13\cdot 10^{13}$, and an analytic tail for $n\ge 10^{12}$ that rests on
Zelinsky's $p$-generators, exactly computed constants and Dusart's explicit bounds for $\pi$.
CI re-runs all three parts. Lean 4 checks the statement and the elementary lemmas the argument
uses, not the computations. The full argument is in [DETAILS.md](DETAILS.md).

Independent of the tail, a pointwise sieve checks every $n\le 10^{12}$, and the grid extends to
$10^{15}$, past the threshold $7.42\cdot 10^{13}$ above which Zelinsky proved the inequality in
2002. So the result also follows from Zelinsky's Theorem 8 together with the grid.

## Canonical statement and prior-art check

[OEIS A111291](https://oeis.org/A111291), checked on 2026-10-24, is the number of refactorable
numbers ([A033950](https://oeis.org/A033950)) up to $10^n$, with data $a(0..11)$. Its comment
attributes to Colton the conjecture that the count below $x$ is at least $x/(2\log x)$; upstream
Formal Conjectures states that form for all sufficiently large $x$ as `conjecture` (category
`research solved`), and it is not the target here. The pointwise form treated here is
Zelinsky's reading of Colton's conjecture (J. Integer Seq. 5 (2002), Article 02.2.8): “Colton's
conjecture becomes: $T(n)\ge\pi(n)/2$ for all $n$.” Zelinsky proved it for
$n>7.42\cdot 10^{13}$.

The upstream formalization
[`FormalConjectures/OEIS/111291.lean`](upstream/111291.lean) (google-deepmind/formal-conjectures
at commit `c094b979`, 2026-10-23) states it as `colton_conjecture` with the category
`research open`; its docstring says the range below Zelinsky's bound is open.

Searches on 2026-10-24 (OpenAlex and arXiv queries on refactorable numbers, tau numbers and
Colton's conjecture, and the OpenAlex list of works citing Zelinsky's paper) found
Colton (1999), Zelinsky (2002) and Abel, Lauer and Redi (Acta Comment. Univ. Tartu. Math. 25
(2021)), whose abstract concerns $\tau$-numbers relative to polynomials. None of them closes the
range below $7.42\cdot 10^{13}$. This is only a negative search result, not a literature review
or a claim of novelty. The proof is unreviewed and has not been reported to OEIS, upstream or
any other venue (external submissions need human approval).

## Proof outline

| Range | Method | Re-run by |
|---|---|---|
| $n\le 10^6$ | divisor-count sieve | `python3 verify_small.py` (CI) |
| $10^6\le n\le 1.13\cdot 10^{13}$ | grid $x_0<\dots<x_{65}$ with $\pi(x_{i+1})\le 2T(x_i)$; monotonicity | `verify_grid.py` + `tau_count.cpp` (CI) |
| $n\ge 10^{12}$ | $T(x)\ge\sum_{d\in G}(\pi(x/d)-\pi(P(d)))$ over the 413,980 $p$-generators $d\le 28\,653\,696$, Dusart's bounds, exact constants | `verify_tail.py` + `generators.cpp` (CI) |

A $p$-generator is a $d$ with $2\tau(d)\mid d$; then $dp$ is refactorable for every prime
$p\nmid d$. Taking only primes $p>P(d)$, the largest prime factor of $d$, makes the families of
different generators disjoint, since $d=n/P(n)$ for $n=dp$ (without this restriction they
overlap, e.g. $640\cdot 3=384\cdot 5$). The tail then reads $2T(x)-\pi(x)>f(x)-2B$ with $f$
increasing, and the script checks $f(10^{12})>2B$ in exact arithmetic (margin about 9.6%).

## Statement faithfulness

[`AgenticConjectures/OeisA111291.lean`](../../AgenticConjectures/OeisA111291.lean) copies
`countRefactorableNat`, `a` and `countRefactorable` from the upstream file term for term, and
`AgenticConjectures.OeisA111291.statement` is exactly the proposition of upstream
`colton_conjecture`:

```lean
def statement : Prop :=
  ∀ n : ℕ, Nat.primeCounting n ≤ 2 * countRefactorableNat n
```

`countRefactorableNat n` counts $k\in[1,n]$ with `k.divisors.card ∣ k`, so $k=0$ is excluded as
in OEIS, and `Nat.primeCounting n` counts primes $\le n$. The statement includes $n=0$, where both
sides vanish, and uses no subtraction. The upstream module header, attributes and the
`native_decide` tests are not copied (see the module docstring).

`statement` stays a `def … : Prop`; it is **not** proved in Lean, and the claimed status
`proved` refers to the computer-assisted proof described here. The Lean theorems, all in the
namespace `AgenticConjectures.OeisA111291`, are the building blocks of the argument (fact
numbers as in [DETAILS.md](DETAILS.md)):

| Declaration | Statement |
|---|---|
| `a_0`, `a_1`, `a_2` | upstream tests $a(0)=1$, $a(1)=4$, $a(2)=16$ (`rfl`) |
| `primeCounting_seven` | $\pi(7)=2T(7)$ (`decide`; F6) |
| `countRefactorableNat_mono` | $T$ is monotone |
| `grid_step` | if $\pi(y)\le 2T(x)$ and $x\le n\le y$, then $\pi(n)\le 2T(n)$ (F5) |
| `isSquare_of_odd_refactorable` | an odd refactorable number is a square (F1) |
| `two_mul_refactorable_iff` | for odd $u$, $2u$ is refactorable iff $u$ is (F2) |
| `refactorable_mul_prime` | if $2\tau(d)\mid d$ and $p\nmid d$ is prime, then $dp$ is refactorable (F3) |
| `card_filter_prime_Ioc` | the number of primes in $(x,y]$ is $\pi(y)-\pi(x)$ |
| `sum_card_primes_le_count`, `sum_primeCounting_sub_le` | the disjoint-family bound $T(x)\ge\sum_{d\in G}(\pi(x/d)-\pi(P(d)))$ (F4) |

## Machine verification and reproduction

From this directory (CI runs the first three commands):

```bash
python3 verify_small.py
g++ -O3 -std=c++17 tau_count.cpp -o /tmp/oeis_a111291_tau_count && python3 verify_grid.py /tmp/oeis_a111291_tau_count 10000000000000
g++ -O3 -std=c++17 generators.cpp -o /tmp/oeis_a111291_generators && python3 verify_tail.py /tmp/oeis_a111291_generators
```

Further checks, not run in CI (times on an Apple M5 Max):

| Command | Time | Log |
|---|---|---|
| `python3 verify_grid.py /tmp/oeis_a111291_tau_count` (full grid to $10^{15}$, 0.7 GB) | 2.3 min | `logs/verify_grid_full.log` |
| `g++ -O3 -std=c++17 -pthread colton_sieve.cpp -o /tmp/oeis_a111291_sieve && /tmp/oeis_a111291_sieve 1000000000000 3 logs/sieve_1e12_checkpoints.txt` | 16.3 min | `logs/sieve_1e12.log` |
| `python3 crosscheck_sieve_log.py /tmp/oeis_a111291_tau_count` | 65 s | `logs/crosscheck_sieve_log.log` |
| `python3 spot_check.py /tmp/oeis_a111291_sieve /tmp/oeis_a111291_tau_count` | 4.5 min | `logs/spot_check.log` |
| `python3 crosscheck_primecount.py` (needs primecount) | 1 s | `logs/crosscheck_primecount.log` |
| `python3 test_bruteforce.py /tmp/oeis_a111291_sieve /tmp/oeis_a111291_tau_count` (needs numpy) | 13 s | `logs/test_bruteforce.log` |

`logs/tau_count_powers_of_ten.log` lists $T(10^k)$ and $\pi(10^k)$ for $0\le k\le 15$. The values
for $k\le 11$ agree with the OEIS data; $a(12)=26\,568\,322\,474$, $a(13)=251\,342\,379\,436$,
$a(14)=2\,388\,671\,712\,980$ and $a(15)=22\,789\,342\,999\,100$ are computed here and have not been
submitted to OEIS.

Lean:

```bash
lake build AgenticConjectures.OeisA111291
```

## Notes for reviewers

- The computations and Dusart's bounds are not formalized; mathlib has no explicit bounds of
  this kind.
- For $n\le 10^{12}$ two independent programs prove the statement (the grid via the structured
  counter `tau_count`, and the pointwise sieve); beyond $10^{12}$ the tail does not use either.
  The two $T$ implementations agree at 1433 checkpoints up to $10^{12}$, on four intervals near
  $10^{13}$, $7.42\cdot 10^{13}$, $10^{14}$ and $10^{15}$, and with brute force up to
  $2\cdot 10^7$; the $\pi$ values agree with primecount.
- Zelinsky's Lemma 9 has a justification that does not by itself establish it; his Theorem 8
  does not depend on it (DETAILS.md, section 3.4).
- The cited prime-counting bounds were checked against the arXiv version of Dusart's paper only.
