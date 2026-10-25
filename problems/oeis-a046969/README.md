**English** | [한국어](README.ko.md)

# OEIS A046969 — Conjecture I

## Verdict

Conjecture I of [OEIS A046969](https://oeis.org/A046969) is **proved**, in
the stronger form

\[
a(p)=12\,(2p-1)\qquad\text{for every prime } p>3 \text{ such that } 2p-1 \text{ is prime},
\]

so $a(p)/12=2p-1$ is prime. Here $a(n)$ is the denominator of
$B_{2n}/(2n(2n-1))$, where $B_k$ are the Bernoulli numbers.

The proof is formalized in Lean 4
([`AgenticConjectures/OeisA046969.lean`](../../AgenticConjectures/OeisA046969.lean))
and checked without `sorry`, extra axioms, or `native_decide`.

## Canonical statement and prior-art check

[OEIS A046969](https://oeis.org/A046969) (revision #70, checked on
2026-10-24) lists the denominators of the coefficients of Stirling's series
for $\log\Gamma(z)$; its Maple and PARI programs compute
$a(n)=\operatorname{denominator}\bigl(B_{2n}/(2n(2n-1))\bigr)$ with offset 1.
On Oct 13 2020, Lorenzo Sauras Altuzarra added:

> “Conjecture I: if n > 2, then a(A005382(n))/12 is prime.”

Here [A005382](https://oeis.org/A005382) lists the primes $p$ for which
$2p-1$ is also prime: $2, 3, 7, 19, 31, 37, \ldots$. The same comment states
a Conjecture II, which the entry now records as disproved by Adamczewski at
$n=236791$ (arXiv:2608.11941); the upstream Formal Conjectures file marks it
as solved. Conjecture II is out of scope here.

The entry records no proof of Conjecture I, and the upstream statement is
still tagged `research open` at the
[snapshot commit](upstream/README.md). The OEIS Open study
(arXiv:2608.11941) and its published attempt scores cover only
Conjecture II. The argument below is a direct
application of classical results: the von Staudt–Clausen theorem, Adams'
theorem, Kummer's congruence, and Voronoi's congruence. No novelty is
claimed. The proof is unreviewed and has not been reported to OEIS or any
other external venue; external submissions need human approval.

## Proof

Let $p>3$ and $q=2p-1$ be primes. Then $p\ge 5$ (4 is not prime), and
$q\ge 9$.

**Step 1 (the denominator of $B_{2p}$).** If $3\mid q$ then $q=3$, which is
impossible, and $3\nmid p$; hence $p\equiv1\pmod 3$ and $3\mid 2p+1$. A
prime $r$ with $(r-1)\mid 2p$ has $r-1\in\{1,2,p,2p\}$. The value $r=p+1$ is
even and larger than 2, and $r=2p+1$ is a multiple of 3 larger than 3. So
the von Staudt–Clausen theorem gives $B_{2p}+\tfrac12+\tfrac13=z\in\mathbb Z$,
that is,

\[
B_{2p}=\frac{N}{6},\qquad N=6z-5,\qquad \gcd(N,6)=1 .
\]

**Step 2 (reduction).** We have $a(p)=\operatorname{den}\bigl(N/(12pq)\bigr)$.
If $p\mid N$ and $q\nmid N$, write $N=pM$. Then $B_{2p}/(2pq)=M/(12q)$ and
$M$ is prime to 2, 3 and $q$, so $a(p)=12q$. It remains to show $p\mid N$
and $q\nmid N$.

**Step 3 (power sums modulo $\ell^2$).** Let $\ell\ge5$ be prime, $m$ even,
and $S_m(\ell)=\sum_{k<\ell}k^m$. Faulhaber's formula with
$\binom{m+1}{i}/(m+1)=\binom{m}{i}/(m+1-i)$ gives

\[
S_m(\ell)=\ell B_m+\sum_{i<m} B_i\binom{m}{i}\frac{\ell^{\,j}}{j},
\qquad j=m+1-i\ge2 .
\]

For $j=2$ the coefficient $B_{m-1}$ is $0$ or $B_1=-\tfrac12$, so the term
has $\ell$-adic valuation at least 2. For $j\ge3$, von Staudt–Clausen gives
$v_\ell(B_i)\ge-1$, and $\ell^{v_\ell(j)}\le j<5^{\,j-2}\le\ell^{\,j-2}$
gives $v_\ell(j)\le j-3$; so the term again has valuation at least
$-1+j-(j-3)=2$. Hence $S_m(\ell)\equiv\ell B_m\pmod{\ell^2}$ in
$\mathbb Z_{(\ell)}$.

**Step 4 (doubling).** Let $\ell=2h+1$. Split $\{0,\ldots,\ell-1\}$ into the
even numbers $2k$ ($k\le h$) and the odd numbers $2j+1$ ($j<h$). Doubling
sends $k=h+1+j$ to $2k=\ell+(2j+1)$, so

\[
(2^m-1)\,S_m(\ell)=\sum_{j<h}\bigl((\ell+2j+1)^m-(2j+1)^m\bigr)
\equiv \ell\, m\sum_{j<h}(2j+1)^{m-1}\pmod{\ell^2}.
\]

This is Voronoi's congruence with multiplier 2, stated for power sums.

**Step 5 (Adams half: $p\mid N$).** Take $\ell=p$ and $m=2p$. The right side
of Step 4 is a multiple of $p\cdot2p$, so $p^2\mid(2^{2p}-1)\,S_{2p}(p)$. By
Fermat, $2^{2p}-1\equiv3\not\equiv0\pmod p$, so $p^2\mid S_{2p}(p)$. Step 3
then gives $v_p(pB_{2p})\ge2$, hence $v_p(N)=v_p(B_{2p})\ge1$.

**Step 6 (Kummer half: $q\nmid N$).** Take $\ell=q$, $m=q+1=2p$ and
$h=p-1$. If $q\mid N$, then $v_q(qB_{2p})\ge2$, so $q^2\mid S_{2p}(q)$ by
Step 3. Step 4 then gives $q\mid(q+1)\sum_{j<p-1}(2j+1)^q$. By Fermat this
sum is congruent to $\sum_{j<p-1}(2j+1)=(p-1)^2$ modulo $q$. But
$0<p-1<q$, so $q\nmid(p-1)^2$, a contradiction.

Steps 5 and 6 are the special cases of Adams' theorem ($p\mid m$ and
$(p-1)\nmid m$ imply $p\mid\operatorname{num}B_m$) and of Kummer's
congruence $B_{2p}/(2p)\equiv B_2/2=\tfrac1{12}\pmod q$ that the proof
needs. Indeed, the computation gives $3B_{q+1}\equiv\tfrac14$, i.e.
$B_{q+1}\equiv\tfrac1{12}\pmod q$.

## Lean formalization

All declarations live in the namespace `AgenticConjectures.OeisA046969`.

| Declaration | Content |
|---|---|
| `a` | the upstream definition, copied term for term |
| `statement` | `∀ p, p.Prime → (2 * p - 1).Prime → 3 < p → (a p / 12).Prime` |
| `conjecture1_holds` | `statement` (Conjecture I) |
| `conjecture1` | the same, with the exact upstream signature |
| `a_eq` | `a p = 12 * (2 * p - 1)` for a prime `p > 3` with `2 * p - 1` prime (Step 2) |
| `vonStaudt_primes_eq` | the von Staudt–Clausen primes for $B_{2p}$ are $\{2,3\}$ (Step 1) |
| `bernoulli_two_mul_eq` | $B_{2p}=(6z-5)/6$ for some integer $z$ (Step 1) |
| `padicNorm_bernoulli_le` | $\lvert B_n\rvert_\ell\le\ell$ for every odd prime $\ell$ |
| `padicNorm_sum_pow_sub_le` | $\lvert S_m(\ell)-\ell B_m\rvert_\ell\le\ell^{-2}$ for a prime $\ell\ge5$ and even $m$ (Step 3) |
| `voronoi_two` | Step 4, as a divisibility by $(2h+1)^2$ in $\mathbb Z$ |
| `sq_dvd_sum_pow_two_mul` | $p^2\mid S_{2p}(p)$ for a prime $p\ge5$ |
| `not_sq_dvd_sum_pow_succ` | $q^2\nmid S_{q+1}(q)$ for a prime $q=2h+1$, $h\ge1$ |
| `prime_dvd_num` | $p\mid N$ when $B_{2p}=N/6$ (Step 5) |
| `not_dvd_num` | $q\nmid N$ when $B_{2p}=N/6$ (Step 6) |

`conjecture1_holds`, `conjecture1`, `a_eq`, `padicNorm_sum_pow_sub_le` and
`voronoi_two` are registered in [`status.yaml`](status.yaml) for the axiom
audit. The proof uses mathlib's `Bernoulli.vonStaudt_clausen`,
`sum_range_pow` (Faulhaber), `sq_dvd_add_pow_sub_sub`, and the `padicNorm`
API.

## Statement faithfulness

- **Definition.** `a` is copied term for term from the
  [upstream snapshot](upstream/README.md): `a 0 = 0`, and for `n ≠ 0`,
  `a n = (bernoulli m / (k : ℚ)).den` with `m = 2 * n` and
  `k = m * (m - 1)` computed in `ℕ`. This is the OEIS formula for $n\ge1$;
  the PARI program also returns 0 for $n<1$. Mathlib's `bernoulli` uses
  $B_1=-\tfrac12$, but only even indices $2n\ge2$ occur, where all
  conventions agree. The sanity-check script confirms that this definition
  reproduces the 35 terms of the OEIS DATA line.
- **Index base.** Since $A005382(1)=2$ and $A005382(2)=3$, and A005382 is
  increasing, $\{A005382(n): n>2\}$ is exactly the set of primes $p>3$ with
  $2p-1$ prime. Our `statement` quantifies over exactly this set, as the
  upstream docstring does.
- **Natural-number subtraction.** In `2 * p - 1` we have $p\ge2$, and in
  `m - 1` we have $m=2p\ge2$, so neither subtraction truncates.
- **Natural-number division.** `a p / 12` truncates in `ℕ`, but `a_eq`
  shows `a p = 12 * (2 * p - 1)`, so the division is exact.
- **Boundary values.** The `n = 0` branch of `a` is never used, since `p`
  is prime. The hypotheses match the upstream theorem exactly: `statement`
  is its universal closure, and `conjecture1` repeats its signature.

## Machine verification and reproduction

From the repository root:

```bash
lake build AgenticConjectures.OeisA046969
python3 problems/oeis-a046969/a046969_certificate.py --limit 400
```

On 2026-10-24 (on a shared, heavily loaded machine with mathlib prebuilt),
`lake build` compiled the module in 8.6 seconds (13 seconds wall time). The
script ran in about 1 second.

[`a046969_certificate.py`](a046969_certificate.py) uses only the Python
standard library and exact rationals. It is a sanity check, not part of the
proof. It computes $B_0,\ldots,B_{800}$ from the recurrence
$\sum_{k\le n}\binom{n+1}{k}B_k=0$, and checks:

- $a(1),\ldots,a(35)$ against the OEIS DATA line;
- for all 17 primes $3<p\le400$ with $2p-1$ prime, that
  $\operatorname{den}B_{2p}=6$, $p\mid N$, $q\nmid N$, $a(p)=12(2p-1)$, and
  that $a(p)/12$ is prime.

Repository CI also rebuilds the module, audits the axioms of the registered
theorems, and reruns the script.

## What is not claimed

- Conjecture II of the same entry is not addressed.
- No novelty is claimed: the ingredients are classical, and the result is
  unreviewed.
- Nothing has been reported to OEIS or upstream.
