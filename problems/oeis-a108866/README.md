**English** | [한국어](README.ko.md)

# OEIS A108866 — Ordowski's prime criterion

## Verdict

**Partial.** Let

\[
S_n=\sum_{k=1}^{n}\frac{2^k}{k},\qquad E_n=-\frac{2}{n}+S_n .
\]

Thomas Ordowski conjectured that for $n>3$, $n^2$ divides the numerator of
$E_n$ if and only if $n$ is prime. The Lean module of this problem proves,
without `sorry`, extra axioms, or `native_decide`:

- the prime direction: $p^2$ divides the numerator of $E_p$ for every prime
  $p>3$ (`prime_imp`). The argument is short and classical; no novelty is
  claimed;
- the composite direction ($n^2$ does not divide the numerator) for every even
  $n$, every multiple of 3 that is not a power of 3, and every $n$ that
  satisfies one of two leading-digit criteria at an odd prime $q\mid n$ (see
  [Proof](#proof)).

Two independent programs check the composite direction for every
$3<n\le 2\cdot10^6$. The full conjecture remains **open**. The Lean families
cover no odd prime power $q^k$ with $k\ge2$. Among the other composites up
to $2\cdot10^6$, they miss only 1027 and 55225.

## Canonical statement and prior-art check

[OEIS A108866](https://oeis.org/A108866) (revision #37, 2020-03-07; read on
2026-10-24) is the “Numerator of Sum_{k=1..n} 2^k/k.” Its comment states:

> “Conjecture: for n > 3, numerator(-2/n + Sum_{k=1..n} 2^k/k) == 0 (mod n^2)
> if and only if n is prime. See my formula below. Cf. A332786. - Thomas
> Ordowski, Mar 02 2020”

The upstream formalization is `OeisA108866.conjecture` in
google-deepmind/formal-conjectures. Its provenance and a byte-exact snapshot
are in [`upstream/`](upstream/README.md).

The OEIS entry records no proof of either direction. Since
$E_p=2q_p(2)+\sum_{k=1}^{p-1}2^k/k$, where $q_p(2)=(2^{p-1}-1)/p$ is the
Fermat quotient, the prime direction is equivalent to the congruence

\[
\sum_{k=1}^{p-1}\frac{2^k}{k}\equiv-2\,q_p(2)\pmod{p^2}\qquad(p\ge5).
\]

Congruences of this kind for Fermat quotients are classical, and the proof
below is a short consequence of Wolstenholme's theorem. Beyond the OEIS
entry, no literature search was made. The entry cites A. M. Robert, *A
Course in p-adic Analysis* (Springer, 2000), p. 278, which was not
consulted. No novelty is claimed, and nothing has been reported to OEIS or
upstream.

## Lean results

All declarations are in
[`AgenticConjectures/OeisA108866.lean`](../../AgenticConjectures/OeisA108866.lean),
namespace `AgenticConjectures.OeisA108866`. Here `num` is the reduced
numerator and $a(c)$ is A108866 itself, the numerator of $S_c$.

| Theorem | Statement |
|---|---|
| `prime_imp` | $p$ prime, $p>3$ ⇒ $p^2 \mid \mathrm{num}(E_p)$ |
| `not_modEq_of_even` | $n>0$, $2\mid n$ ⇒ $n^2\nmid\mathrm{num}(E_n)$ |
| `not_modEq_of_three_dvd` | $n>0$, $3\mid n$, $n$ not a power of 3 ⇒ $n^2\nmid\mathrm{num}(E_n)$ |
| `not_modEq_of_lead_one` | $q$ odd prime, $q\mid n$, $q^e<n<2q^e$ ⇒ $n^2\nmid\mathrm{num}(E_n)$ |
| `not_modEq_of_top_digit` | $q$ odd prime, $q\mid n<q^{e+1}$, $q^e\nmid n$, $q\nmid a(\lfloor n/q^e\rfloor)$ ⇒ $n^2\nmid\mathrm{num}(E_n)$ |
| `not_modEq_of_mul_pow` | $q$ odd prime, $e>0$, $c<q$, $n=cq^e$, $q\nmid\mathrm{num}(E_c)$ ⇒ $n^2\nmid\mathrm{num}(E_n)$ |
| `statement_iff_composite` | `statement` ⇔ the composite direction for every $n>3$ |
| `iff_of_families` | the equivalence holds at every $n>3$ that is prime or meets the hypotheses of one of the theorems above |

The full `statement` is not proved.

## Proof

### Prime direction

1. Induction on $n$ with Pascal's rule gives
   $S_n=H_n+\sum_{k=1}^{n}\binom nk/k$, where $H_n=\sum_{k\le n}1/k$
   (`sum_two_pow_div`). Since $\binom pk/k=p\binom{p-1}{k-1}/k^2$, this
   becomes
   \[
   E_p=H_{p-1}+p\sum_{k=1}^{p-1}\frac{\binom{p-1}{k-1}}{k^2}
   \]
   (`ratExpression_succ`).
2. Wolstenholme's theorem $p^2\mid H_{p-1}$ for $p\ge5$
   (`padicNorm_harmonic_le`). Pairing $k$ with $p-k$ gives
   $2H_{p-1}=p\sum_{k=1}^{p-1}1/(k(p-k))$. Moreover
   $1/(k(p-k))\equiv-1/k^2 \pmod p$, and
   $\sum_{x\in\mathbb F_p^\times}x^{-2}=\sum_{x\in\mathbb F_p}x^2=0$ for
   $p\ge5$.
3. $p\mid\sum_{k=1}^{p-1}\binom{p-1}{k-1}/k^2$ (`padicNorm_sum_choose_le`).
   Pairing $k$ with $p-k$ shows that twice the sum is congruent modulo $p$
   to $\sum_k\binom pk/k^2$, and $p\mid\binom pk$ for $0<k<p$.

Hence $v_p(E_p)\ge2$, which is `prime_imp`.

### Composite direction

Write $\lVert\cdot\rVert_q$ for the $q$-adic absolute value. If some prime
$\ell\mid n$ has $\lVert E_n\rVert_\ell>1/\ell$, then $\ell$ does not divide
the numerator of $E_n$, and so neither does $n^2$ (`not_modEq_of_padicNorm`).

- **$\ell=2$, $n$ even.** Every term $2^k/k$ has
  $\lVert 2^k/k\rVert_2<1$, while $\lVert2/n\rVert_2\ge1$. So
  $\lVert E_n\rVert_2\ge1$.
- **$\ell=q$ odd.** Let $q^e\le n<q^{e+1}$ and let $c=\lfloor n/q^e\rfloor$,
  the leading base-$q$ digit, so $1\le c<q$. A term $2^k/k$ with $q^e\nmid k$
  has norm $<q^e$. The remaining terms $k=jq^e$, $1\le j\le c$, sum to
  $q^{-e}\sum_{j\le c}2^{jq^e}/j$. Fermat's little theorem gives
  $2^{jq^e}\equiv2^j\pmod q$, and $c<q$, so
  $\sum_{j\le c}2^{jq^e}/j\equiv S_c\pmod q$. The numerator of $S_c$ is
  $a(c)$.
  - If $q^e\nmid n$, then $\lVert2/n\rVert_q<q^e$. So $q\nmid a(c)$ gives
    $\lVert E_n\rVert_q=q^e$ (`not_modEq_of_top_digit`).
    - With $c=1$ and $a(1)=2$ this gives `not_modEq_of_lead_one`.
    - For $q=3$ the digits $c\in\{1,2\}$ have $a(1)=2$ and $a(2)=4$.
      Together with the even case, this covers every multiple of 3 that is
      not a power of 3 (`not_modEq_of_three_dvd`).
  - If $n=cq^e$ with $e\ge1$, then $-2/n$ joins the top terms. Their sum is
    $q^{-e}$ times a number congruent to $E_c$ modulo $q$. So
    $q\nmid\mathrm{num}(E_c)$ gives $\lVert E_n\rVert_q=q^e$
    (`not_modEq_of_mul_pow`).

**Where the families stop.** For an odd prime power $n=q^k$ with $k\ge2$, we
have $c=1$ and $E_1=0$, so the leading terms cancel. A finer $q$-adic
expansion would be needed. Up to $2\cdot10^6$, only two other composites
escape every theorem; each fails both criteria at every prime factor:

- $1027=6\cdot13^2+13=13\cdot79$: here $13\mid a(6)=416$ and
  $79\mid\mathrm{num}(E_{13})$;
- $55225=3\cdot5^6+8350=25\cdot47^2$: here $5\mid a(3)=20$ and
  $47\mid\mathrm{num}(E_{25})$.

Both are excluded computationally ($v_{13}(E_{1027})=-1$ and
$v_5(E_{55225})=-4$).

## Statement faithfulness

- `a` and `ratExpression` are term-for-term copies of the upstream
  definitions. `statement` is `∀ n : ℕ, n > 3 → ((ratExpression n).num ≡ 0
  [ZMOD (n^2 : ℤ)] ↔ n.Prime)`, the upstream `conjecture` with its hypothesis
  moved under the quantifier. It is the same proposition.
- `∑ i ∈ range n, 2^(i+1)/(i+1)` is $\sum_{k=1}^n2^k/k$ (index shift
  $k=i+1$). The `if n > 0` branch only matters at $n=0$.
- `Rat.num` is the numerator of the reduced fraction, as in the OEIS
  wording. The congruence `≡ 0 [ZMOD (n^2 : ℤ)]` is divisibility of that
  integer by $n^2$; its sign is irrelevant.
- The composite-direction theorems carry their own hypotheses (for example
  $n>0$) and do not assume $n>3$; `iff_of_families` restates them as
  instances of the equivalence for $n>3$.
- The upstream test lemmas `a_0`–`a_4` and their `eval_a` macro are not
  copied. They check values of `a`, not the conjecture.

## Machine verification and reproduction

$E_n$ is a nonzero rational (indeed $E_n>0$ for $n\ge2$). So $n^2$ divides
its numerator if and only if $v_q(E_n)\ge2v_q(n)$ for every prime $q\mid n$.
Both programs compute the capped valuation $\min(v_q(E_n),2v_q(n))$ for every
pair $(n,q)$ with $q$ a prime factor of $n$.

- [`a108866_check.py`](a108866_check.py) uses only the Python standard
  library (gmpy2 is optional through `--gmpy2`). It runs three computations:
  - a literal `Fraction` test of the numerator modulo $n^2$;
  - method A: exact integers $A_n/\mathrm{lcm}(1,\dots,n)$;
  - method B: $q$-adic running sums modulo $q^{3L}$.

  `--compare FILE` checks every line `n q v` of FILE against method A. The
  script also lists the composites that no Lean theorem covers, evaluating
  the theorems' hypotheses exactly modulo $q$.
- [`a108866_qadic.cpp`](a108866_qadic.cpp) is a separate C++ implementation
  of the $q$-adic method with 128-bit modular products. Its algorithm is
  independent of method A. It processes every multiple of each prime
  $q\le\sqrt N$ and has a fallback for composites without a witness; no
  composite up to $2\cdot10^6$ needed it. It also checks the pairs $(p,p)$
  for the primes $p\le10^5$.

| Run | Range | Result | Runtime |
|---|---|---|---|
| `python3 a108866_check.py` (CI) | $3<n\le10^4$ | literal ($n\le3000$), A and B agree; 40 composites outside the Lean families (39 odd prime powers and 1027) | 3 s |
| C++ + method A, `--compare` (CI) | $3<n\le10^5$ | all 211,744 C++ lines agree with method A; 95 composites outside the Lean families (93 odd prime powers, 1027, 55225) | 22 s, including compilation |
| C++ + method A with gmpy2, `--compare` (local, `ci_feasible: false`) | $3<n\le2\cdot10^6$ | see below | 6.4 min under load |

The local run took place on 2026-10-24 on an Apple M5 Max shared with other
jobs. Its log summary:

- C++: 1,851,066 composites, none needing the fallback and none
  unexcluded. Minimum $\min(v_p(E_p),2)=2$ over the 9,590 primes
  $5\le p\le10^5$. 4,498,598 lines written. 21 s on a nearly idle machine,
  26 s under load.
- Method A (Python 3.12.13, gmpy2 2.3.2): 148,931 primes and 1,851,066
  composites with $3<n\le2\cdot10^6$, and 5,808,798 $(n,q)$ pairs. $n^2$
  divides the numerator of $E_n$ exactly when $n$ is prime, and
  $\min(v_p(E_p),2)=2$ for every prime $5\le p\le2\cdot10^6$. All 4,498,598
  C++ lines agree. The coverage report lists 285 composites outside the
  Lean families: 283 odd prime powers, 1027 and 55225. Method A and the
  report took 357 s under load, and the whole command 384 s; an earlier run
  of method A alone took 306 s on a nearly idle machine.

From the repository root:

```bash
lake build AgenticConjectures.OeisA108866
cd problems/oeis-a108866
python3 a108866_check.py
mkdir -p build && g++ -O2 -std=c++17 -o build/a108866_qadic a108866_qadic.cpp
./build/a108866_qadic 100000 > build/qadic_1e5.tsv
python3 a108866_check.py --limit 100000 --skip-qadic --literal-limit 0 --compare build/qadic_1e5.tsv
# local only: writes a 59 MB file
./build/a108866_qadic 2000000 > build/qadic_2e6.tsv
python3 a108866_check.py --limit 2000000 --skip-qadic --literal-limit 0 --gmpy2 --compare build/qadic_2e6.tsv
```

Without gmpy2 the last command falls back to Python integers; this was not
timed at $2\cdot10^6$.

## What is not claimed

- The conjecture is not proved. No Lean theorem handles the odd prime powers
  $q^k$ with $k\ge2$ (283 of them up to $2\cdot10^6$), or the composites 1027
  and 55225 (the only others up to $2\cdot10^6$), where every odd prime
  factor fails both digit criteria.
- The computation is a finite check of $3<n\le2\cdot10^6$ only.
- No novelty is claimed. The result has not been reviewed or reported to OEIS
  or upstream; external submissions need human approval.
