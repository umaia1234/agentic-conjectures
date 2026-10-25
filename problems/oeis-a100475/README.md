**English** | [한국어](README.ko.md)

# OEIS A100475 — no start goes into a loop

## Verdict

The upstream conjecture is **refuted**. Let $p_k$ be the $k$-th prime
($p_1=2$) and $\operatorname{rev}$ the reversal of decimal digits. For every
start $x\ge1$, the orbit

\[
x,\ f(x),\ f(f(x)),\ \ldots \qquad f(k)=\operatorname{rev}(p_k)
\]

is not ultimately periodic. In particular no start other than $1$ "goes into
a loop". The start $x=1$, which is the OEIS sequence itself, does not loop
either.

The whole refutation is a Lean 4 proof, checked without `sorry`, extra
axioms, or `native_decide`. Its finite parts (prime counts and a search below
$1230$) are kernel evaluations with `decide +kernel`. The Python script in
this directory re-derives the same numbers independently. The proof does not
depend on it.

## Canonical statement and prior art

[OEIS A100475](https://oeis.org/A100475) (revision #21, Feb 16 2025, read on
2026-10-24) is "Prime-th recurrence with reversal at each step", with
$a(0)=1$ and $a(n)=\operatorname{reversal}(p_{a(n-1)})$. Its comment asks:

> “Starting at other than a(n) = 1, does this sequence ever go into a loop?”

The Formal Conjectures file
[`FormalConjectures/OEIS/100475.lean`](upstream/100475.lean) (see
[upstream/README.md](upstream/README.md)) states the "yes" answer as an open
conjecture:

```lean
theorem conjecture :
    ∃ x : ℕ, 0 < x ∧ x ≠ 1 ∧ IsUltimatelyPeriodic (aStartAt x)
```

The OEIS entry gives no answer and still carries the keyword `more`. The
question is not listed in OEIS Open. The entry links to MathWorld's page on
Rosser's theorem $p_n>n\ln n$, which already forces digit growth for large
numbers. The argument below is elementary and may well be known; no novelty
is claimed. The result has not been reported to OEIS, because external
submissions need human approval.

## Proof

Write $L(n)$ for the number of decimal digits of $n$.

1. **Digit length never decreases.** No prime is divisible by $10$, so
   $\operatorname{rev}(p)$ has the same number of digits as $p$. Also
   $p_k\ge k+1$. Hence $L(f(k))=L(p_k)\ge L(k)$. Orbits from $x\ge1$ never
   reach $0$, so $L$ is non-decreasing along them.
2. **A loop lives in one digit band.** If the orbit satisfies
   $a_{n+P}=a_n$ for all $n\ge N$ with $P>0$, then for $n\ge N$ we get
   $L(a_N)\le L(a_n)\le L(a_{N+nP})=L(a_N)$. Let $d$ be this common length.
3. **Counting.** For $n\ge N$, put $k=a_n$. Then $10^{d-1}\le k$ and
   $L(p_k)=L(a_{n+1})=d$, so $p_1<\dots<p_k<10^d$ and
   $\pi(10^d)\ge k\ge10^{d-1}$.
4. **This is impossible for $d\ge5$**, because $\pi(10^d)<10^{d-1}$:
   - $d=5$: an exact count gives $\pi(100112)=9600$, so
     $\pi(10^5)\le9600<10^4$.
   - $d=6$: the primes in $(m,2m]$ divide $\binom{2m}{m}\le4^m$, so if
     $(m+1)^{K+1}>4^m$ there are at most $K$ of them. With $m=500000$ and
     $K=52821$, and the exact count $\pi(509712)=42269$, we get
     $\pi(10^6)\le42269+52821=95090<10^5$.
   - $d=7$: four more such blocks, $m=625000,1250000,2500000,5000000$ with
     $K=64923,123435,235255,449367$, give
     $\pi(10^7)\le968070<10^6$.
   - $d\ge8$, by induction: the primes in $[10^{d-1},10^d)$ multiply to at
     most $\operatorname{primorial}(10^d)\le4^{10^d}$, and each is at least
     $10^{d-1}$. If there were at least $9\cdot10^{d-2}$ of them, then
     $10^{9(d-1)}\le4^{100}<10^{63}$, which is false. So
     $\pi(10^d)<10^{d-2}+9\cdot10^{d-2}=10^{d-1}$.
5. **The case $d\le4$ is finite.** For $n\ge N$ we have
   $p_{a_n}<10^d\le10^4$, so $a_n\le\pi(10^4)=1229$. The tail stays in the
   band of $d$-digit numbers $k\le1229$. A kernel check shows that from
   every such $k$, iterating $f$ leaves the band. (It takes at most four
   steps; the Lean check allows $1230$.) This contradicts step 2.

**Corrections to the harvest triage.** The triage argument is right, but
two details change. First, the case $d\le4$ needs only the primes below
$10^4$, not $p_{9999}$: a tail value with at most four digits is at most
$\pi(10^4)=1229$. That is also why the triage search over starts below
$20000$ was enough. Second, no Rosser–Schoenfeld estimate is needed. Exact
counts and central-binomial blocks cover $d=5,6,7$, and
$\operatorname{primorial}(n)\le4^n$ covers $d\ge8$.

## Lean formalization

[`AgenticConjectures/OeisA100475.lean`](../../AgenticConjectures/OeisA100475.lean)
(namespace `AgenticConjectures.OeisA100475`):

| Declaration | Content |
| --- | --- |
| `not_statement` | `¬ statement`, the negation of the upstream `conjecture` |
| `not_isUltimatelyPeriodic` | `0 < x → ¬ IsUltimatelyPeriodic (aStartAt x)` |
| `length_digits_reverseDigits` | reversal keeps the digit count when `p % 10 ≠ 0` |
| `count_prime_pow_ten_lt` | `5 ≤ d → Nat.count Nat.Prime (10 ^ d) < 10 ^ (d - 1)` |
| `count_dyadic_le`, `count_step` | the dyadic block bound and the step for `d ≥ 8` |
| `prime_iff_gcd_factorial` | `B < n < (B + 1) ^ 2 → (n.Prime ↔ Nat.gcd n B ! = 1)` |
| `count_prime_10000` | `Nat.count Nat.Prime 10000 = 1229` (kernel check of a table) |
| `cnt_A`, `cnt_B`, `cnt_C` | kernel counts 7649, 722, 32669 of primes in three ranges |
| `escape_check` | kernel check: every band `d ≤ 4` is left from every `k ≤ 1229` |

Kernel computations avoid `Decidable` instances and use `Nat.gcd`,
`Nat.pow`, `Nat.ble` and `Nat.rec` directly. Each one is linked back to
`Nat.Prime` and `Nat.nth` by a proved lemma (`isPrimeB_iff`, `cntCop_eq`,
`nth_prime_eq_table`, `step_eq_G`, `escapes_spec`). `#print axioms` for both
main theorems lists only `propext`, `Classical.choice` and `Quot.sound`.

## Statement faithfulness

- `reverseDigits`, `a`, `aStartAt` and `IsUltimatelyPeriodic` are copied
  term for term from the upstream file; `statement` is the body of the
  upstream `conjecture`. Only the `module` header, the
  `FormalConjecturesUtil` import, `@[expose] public section`, and the
  category attributes are dropped. The upstream lemmas `a_succ`,
  `a_0`–`a_4`, `aStartAt_zero` and `conjecture_with_zero` are not repeated.
- Index base: `Nat.nth Nat.Prime 0 = 2`, so `Nat.nth Nat.Prime (k - 1)` is
  the OEIS $p_k$ for $k\ge1$. This matches the OEIS example: $a(6)=13$,
  $p_{13}=41$, $a(7)=14$.
- ℕ subtraction: `k - 1` is reached only when `k ≠ 0`, so it never
  truncates.
- Boundary values: upstream excludes `x = 0` (whose orbit is constantly `0`,
  see the upstream `conjecture_with_zero`) through `0 < x`, and excludes
  `x = 1`. Our stronger theorem also covers `x = 1`.
- `reverseDigits` drops trailing zeros, like the OEIS programs
  (`FromDigits[Reverse[IntegerDigits[...]]]`). Primes have no trailing
  zero, so this choice does not matter here.
- For an iteration $a_{n+1}=f(a_n)$, "goes into a loop" (some value
  repeats) is the same as being ultimately periodic, so `IsUltimatelyPeriodic`
  is the right reading of the OEIS question.

## Machine verification and reproduction

From the repository root:

```bash
lake build AgenticConjectures.OeisA100475
python3 problems/oeis-a100475/a100475_certificate.py
```

On the 2026-10-24 development run (Apple M5 Max, shared with other jobs) the
module built in about 20 seconds. Most of that time is kernel evaluation;
`cnt_C`, which checks the 409600 numbers in $[100112,509712)$, took 11 to
14 seconds. The Python script uses only the standard library and finished in
about 3 seconds. It sieves the primes below $10^7+1$ and checks:

- every prime count and chunk count used by the Lean proof, and the exact
  values $\pi(10^5)=9592$, $\pi(10^6)=78498$, $\pi(10^7)=664579$;
- the five inequalities $4^m<(m+1)^{K+1}$ in exact integer arithmetic, and
  that each block $(m,2m]$ really holds at most $K$ primes;
- $L(f(k))=L(p_k)\ge L(k)$ for all $k\le664579$;
- that every band $d\le4$ is left from every $k\le1229$, by a cycle search
  that shares no code with the Lean check;
- as a sanity check, that no orbit from $1\le x<20000$ repeats a value
  before it exceeds $664579$.

## What is not claimed

- No novelty. The argument uses only standard tools, and the OEIS entry's
  link to Rosser's theorem suggests that the growth argument was known.
- Nothing is claimed about A100475 beyond the absence of loops, for example
  about the growth rate of its terms.
- The result is unreviewed and has not been submitted to OEIS or to Formal
  Conjectures.
