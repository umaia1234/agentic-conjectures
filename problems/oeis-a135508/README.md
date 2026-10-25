**English** | [한국어](README.ko.md)

# OEIS A135508: McEachen's conjecture a(p−1) = p — criterion and partial results

## Statement

[OEIS A135508](https://oeis.org/A135508) (Benoit Cloitre, 2008; entry checked on
2026-10-24, revision #47) defines, with offset 1,

\[
a(n)=\frac{x(n+1)}{x(n)}-2,\qquad x(1)=1,\quad x(n)=2\,x(n-1)+\operatorname{lcm}(x(n-1),n),
\]

so that \(a(1),a(2),\dots = 2, 3, 1, 1, 1, 7, 2, 1, 1, 11, 1, 1, \dots\) The entry
contains the conjecture

> "Conjecture: For prime p such that p-2 is not a prime, a(p-1) = p. The set of sorted
> primes, except 7, is A025584." — Bill McEachen, Sep 26 2025

The Formal Conjectures file ([upstream snapshot](upstream/README.md)) states it as

```lean
theorem conjecture (p : ℕ) (hp : p.Prime) (hp_twin : ¬ (p - 2).Prime) : a (p - 1) = p
```

and leaves it open (`sorry`).

## Result

Status: **partial**. The full conjecture is **not** proved.

Proved in Lean 4 ([`AgenticConjectures/OeisA135508.lean`](../../AgenticConjectures/OeisA135508.lean)),
against the upstream definitions copied term for term:

1. **Criterion.** For every prime \(p\ge5\):
   \(a(p-1)=p \iff \gcd(x(p-3),\,p-2)>1\).
2. **Residue classes mod 3 and 5.** \(a(p-1)=p\) for every prime \(p\ge7\) with
   \(p\equiv2\pmod 3\) or \(p\equiv2\pmod 5\); no hypothesis on \(p-2\) is needed.
   These primes have relative density \(5/8\) among all primes.
3. **Certificate.** Every prime \(r<1009\) divides \(x(r^2-1)\).
4. **Consequences.** The conjecture holds at every prime \(p\) such that \(p-2\) is
   composite with least prime factor below 1009. In particular it holds
   - for every prime \(r<1009\), at every prime \(p\equiv 2\pmod r\) with \(p-2\) not prime;
   - at every prime \(p<1009^2+2=1018083\).

   By Dirichlet's theorem, the primes not covered have relative density
   \(\prod_{3\le q<1009}\frac{q-2}{q-1}\approx0.107\); the theorem covers about 89%.
5. **Conditional reductions.** The full conjecture follows from "every prime \(r\)
   divides \(x(r^2-1)\)", and hence from the OEIS comment "this sequence consists of
   1's or primes only". Conversely, that comment would force, for every prime
   \(r\ge5\), a prime \(s\equiv-2\pmod r\) with \(s<r^2\). Such a bound on the least
   prime in an arithmetic progression is, to our knowledge, not known, so this route
   does not give a proof.

Checked by scripts (not by Lean), with two independently written programs that
agree on a fingerprint of all of \(a(1),\dots,a(10^9)\):

- \(a(n)\) is 1 or a prime for every \(n\le10^9\);
- the conjecture holds for all 47,423,028 primes \(p\le10^9+1\) with \(p-2\) not prime;
- every prime \(r\le31622\) divides \(x(r^2-1)\). Together with the Lean lemma
  `a_pred_eq_of_minFac_dvd`, this gives the conjecture at every prime \(p\) such that
  \(p-2\) is composite with least prime factor \(\le31622\) (relative density about
  93%). This is a script-plus-Lean result, not a kernel-checked one;
- \(p=7\) is the only prime \(p\le10^9+1\) with \(p-2\) prime and \(a(p-1)=p\).

Not claimed: the conjecture for primes \(p>10^9+1\) for which every prime factor of
\(p-2\) exceeds 31622 (or, for the purely Lean statement, primes \(p\ge1018083\) for
which every prime factor of \(p-2\) exceeds 1008). Beyond the last scan observation,
nothing is claimed about the twin-prime comments in the entry.

## Proofs

**Structure.** For \(n\ge1\), \(x(n)>0\) and, with \(g=\gcd(x(n),n+1)\),
\(\operatorname{lcm}(x(n),n+1)=x(n)\cdot\frac{n+1}{g}\). Hence
\(x(n+1)=x(n)\bigl(\frac{n+1}{g}+2\bigr)\) and \(a(n)=\frac{n+1}{g}\). So
\(a(n)\mid n+1\), \(x(n+1)=x(n)\,(a(n)+2)\), \(x(n)=\prod_{m=1}^{n-1}(a(m)+2)\), and
\(x(m)\mid x(n)\) for \(1\le m\le n\).

**Criterion.** Let \(p\ge5\) be prime. Since \(a(p-1)=p/\gcd(x(p-1),p)\), we have
\(a(p-1)=p\) iff \(p\nmid x(p-1)=x(p-3)\,(a(p-3)+2)\,(a(p-2)+2)\).
- Every factor \(a(m)+2\) of \(x(p-3)\) has \(m\le p-4\), so \(3\le a(m)+2\le p-1\);
  hence \(p\nmid x(p-3)\).
- \(a(p-2)\mid p-1\) gives \(a(p-2)+2\le p+1\). Divisibility by \(p\) would need
  \(a(p-2)=p-2\), but \(p-2\nmid p-1\). So \(p\nmid a(p-2)+2\).
- \(a(p-3)\mid p-2\) gives \(a(p-3)+2\le p\). So \(p\mid a(p-3)+2\) iff
  \(a(p-3)=p-2\) iff \(\gcd(x(p-3),p-2)=1\).

**Transfer and residue classes.** If \(q>1\) divides both \(x(N)\) and \(p-2\), with
\(1\le N\le p-3\), then \(q\mid\gcd(x(p-3),p-2)\). Since \(x(4)=60\), taking \(q=3\)
or \(q=5\) and \(N=4\) gives item 2.

**Least prime factor.** If \(p-2\) is composite with least prime factor \(r\), then
\(r^2\le p-2\). So \(r\mid x(r^2-1)\) implies \(r\mid x(p-3)\) and \(a(p-1)=p\).
Write \(F(r)=\min\{n: r\mid x(n)\}\). The Lean certificate has three parts:
- for the 46 primes \(r<211\), the kernel checks \(r\mid x(F(r))\) and
  \(F(r)\le r^2-1\). The tightest case is \(F(7)=47\le48\): no \(a(m)\) with
  \(m\le45\) is \(\equiv5\pmod 7\), and \(a(46)+2=49\);
- for the 122 primes \(211\le r\le997\), it checks that their product divides
  \(x(42611)\). Here \(42611=F(991)\) is the largest first-entry index below 1009,
  and \(42611\le211^2-1\);
- every prime below 1009 is covered: the kernel checks that each \(r\in[211,1009)\)
  divides that product or has a divisor in \([2,32)\).

If \(p-2<1009^2\) is composite, its least prime factor is below 1009, which gives the
finite range.

**Conditional reductions and their limit.** Suppose \(a(n)\) is 1 or prime for all
\(n\ge1\). If a prime \(r\) did not divide \(x(r^2-1)\), then
\(\gcd(x(r^2-1),r^2)=1\) and \(a(r^2-1)=r^2\), which is neither 1 nor prime. Hence
every prime \(r\) divides \(x(r^2-1)\), and the conjecture follows. Conversely, for a
prime \(r\ge5\), \(r\mid x(r^2-1)\) means \(r\mid a(m)+2\) for some \(m\le r^2-2\).
Then \(a(m)\ne1\), so \(a(m)\) is a prime \(s\equiv-2\pmod r\) with
\(s\mid m+1<r^2\). The best unconditional exponent in Linnik's theorem on the least
prime in a progression is 5 (Xylouris), and GRH gives roughly \((\varphi(q)\log q)^2\).
Neither yields \(s<r^2\) for every \(r\). The data fit the expected picture:
\(F(r)/r^2\le0.96\) for all primes \(r\le31622\), with the maximum at \(r=7\).

## Lean formalization

`lake build AgenticConjectures.OeisA135508` takes about 25 s; the kernel evaluation of
\(x(42611)\) dominates. All kernel computations use `decide +kernel`; there is no
`sorry`, extra axiom or `native_decide`.

| Declaration | Content |
|---|---|
| `x`, `a` | upstream definitions, verbatim |
| `statement` | upstream `conjecture` as a `Prop` |
| `a_0` … `a_4` | upstream test values, same `rfl` proofs |
| `a_eq`, `x_succ_eq` | for `n ≥ 1`: `a n = (n + 1) / gcd (x n) (n + 1)`, `x (n + 1) = x n * (a n + 2)` |
| `x_dvd_x` | `x m ∣ x n` for `1 ≤ m ≤ n` |
| `a_pred_eq_iff` | `p.Prime → 5 ≤ p → (a (p - 1) = p ↔ ¬ Nat.Coprime (x (p - 3)) (p - 2))` |
| `a_pred_eq_of_dvd` | `q ≠ 1`, `q ∣ x N`, `q ∣ p - 2`, `1 ≤ N`, `N + 3 ≤ p` imply `a (p - 1) = p` |
| `a_pred_eq_of_mod_three_or_five` | `p.Prime → 7 ≤ p → p % 3 = 2 ∨ p % 5 = 2 → a (p - 1) = p` |
| `prime_dvd_x_sq_sub_one` | `r.Prime → r < 1009 → r ∣ x (r ^ 2 - 1)` |
| `a_pred_eq_of_minFac_dvd` | `p.Prime → ¬ (p - 2).Prime → (p - 2).minFac ∣ x ((p - 2).minFac ^ 2 - 1) → a (p - 1) = p` |
| `a_pred_eq_of_minFac_lt` | `p.Prime → ¬ (p - 2).Prime → (p - 2).minFac < 1009 → a (p - 1) = p` |
| `a_pred_eq_of_mod_eq_two` | `p.Prime → ¬ (p - 2).Prime → r.Prime → r < 1009 → p % r = 2 → a (p - 1) = p` |
| `a_pred_eq_of_lt` | `p.Prime → ¬ (p - 2).Prime → p < 1009 ^ 2 + 2 → a (p - 1) = p` |
| `statement_of_forall_prime_dvd` | `(∀ r, r.Prime → r ∣ x (r ^ 2 - 1)) → statement` |
| `statement_of_a_eq_one_or_prime` | `(∀ n, 1 ≤ n → a n = 1 ∨ (a n).Prime) → statement` |
| `exists_prime_of_a_eq_one_or_prime` | the same hypothesis gives, for each prime `r ≥ 5`, a prime `s < r ^ 2` with `r ∣ s + 2` |

The certificate data `smallCerts` (pairs \((r,F(r))\)) and `largePrimes` were produced
by `a135508_scan.cpp --certs`. The kernel re-checks every divisibility, so the proof
does not trust them; `a135508_check.py` also confirms that they are the first-entry
indices.

### Statement faithfulness

- `x` and `a` are the upstream definitions verbatim: `x 0 = 0`, `x 1 = 1`, and the third
  clause is the recurrence at indices \(\ge2\); `a 0 = 0` is the upstream boundary value.
  `a` uses natural-number division and truncated subtraction. For \(n\ge1\), `a_eq`
  shows that neither truncation is active: \(x(n)\mid x(n+1)\) and the quotient is
  \(a(n)+2\ge3\).
- The offset matches OEIS: for \(n\ge1\), `a n` is the OEIS \(a(n)\). The script checks
  the 92 DATA terms against the literal definition. (The entry's formula
  "a(2*4^k) = 2" uses an index shifted by one, as in Schepke's \(q_2\); in the OEIS
  offset, \(a(n)=2\) exactly for \(n=2\cdot4^k-1\), which the script also checks up to
  its bound.)
- `statement` is the upstream `conjecture` with the same binders and the same truncated
  `p - 2` and `p - 1`. For \(p=2,3\) the truncated \(p-2\) is \(0,1\), not prime, so
  these primes are included, as in the OEIS wording; `a 1 = 2` and `a 2 = 3` hold. For
  primes \(p\ge2\), \(p-1\) is not truncated.
- The partial theorems keep the hypothesis `¬ (p - 2).Prime` where it is needed; the
  mod-3/mod-5 theorem does not need it. `(p - 2).minFac` is Mathlib's `Nat.minFac`.
- Dropped: the upstream attributes (`@[category ...]`, `@[AMS ...]`), the `module` /
  `public section` / `@[expose]` header, and the `FormalConjecturesUtil` import. None
  of them affects the statement.

## Numerical verification (script check)

| Program | Method | Run |
|---|---|---|
| [`a135508_scan.cpp`](a135508_scan.cpp) | exponent bookkeeping in C++; Eratosthenes table of least prime factors (`uint16`, odd numbers); exponents capped at 255 | \(N=10^9\): 65 s, 1.5 GB |
| [`a135508_scan_numba.py`](a135508_scan_numba.py) | written separately in Python + numba; linear sieve (`uint32`); exact exponents for \(q<65536\), membership flags above | \(N=10^9\): 92 s, 3.7 GB |
| [`a135508_check.py`](a135508_check.py) | standard library only; literal upstream definitions with big integers, plus a pure-Python bookkeeping scan to \(10^6\) | literal range 5000: 2 s (CI); 200000: 62 s |

The bookkeeping programs use \(a(n)=(n+1)/\gcd(x(n),n+1)\) and
\(x(n+1)=x(n)(a(n)+2)\), proved in Lean (`a_eq`, `x_succ_eq`); `a135508_check.py`
also confirms them against the literal recurrence on \(1\le n\le200000\). Each program
checks: (C1) every \(a(n)\) is 1 or prime; (C2) the conjecture for primes \(p\le N+1\);
(C3) the criterion; (C4) \(\operatorname{minFac}(p-2)\mid x(p-3)\) for every prime
\(p\le N+1\) with \(p-2\) composite; (C5) \(F(r)\le r^2-1\) for every prime
\(r\le\sqrt{N+1}\). At \(N=10^9\) both bookkeeping programs report no failure and the
same fingerprint

```
count_a1=843268629 count_a2=15 sum_a=35999661488869551 hash=d10d4d138b066d11
```

(the hash is \(h\leftarrow 1000003\,h+a(n) \bmod 2^{64}\) over \(n=1,\dots,N\)). The
logs are in [`logs/`](logs/). Reproduce from the repository root:

```bash
python3 problems/oeis-a135508/a135508_check.py                      # 2 s
python3 problems/oeis-a135508/a135508_check.py --literal 200000     # 62 s
g++ -O3 -std=c++17 problems/oeis-a135508/a135508_scan.cpp -o /tmp/a135508_scan
/tmp/a135508_scan 10000000                                         # 0.4 s
/tmp/a135508_scan 1000000000                                       # 65 s, 1.5 GB
python3 problems/oeis-a135508/a135508_scan_numba.py 1000000000      # 92 s, 3.7 GB; needs numpy, numba
lake build AgenticConjectures.OeisA135508                          # 25 s
```

Runtimes were measured on an Apple M5 Max on 2026-10-24.

## Prior art and submission status

- The conjecture is Bill McEachen's (Sep 26 2025). The OEIS entry also asserts, without
  proof, that the "sequence consists of 1's or primes only" and that "largest primes in
  twin pairs never occur" (\(a(6)=7\) is an exception).
- Markus Schepke's thesis *Über Primzahlerzeugende Folgen* (U. Hannover, 2009; linked
  from the entry), §3.2.2, studies this sequence as \(q_2\) (index shifted by one). It
  gives \(q_2(n)=n/\gcd(n,b_2(n-1))\), so \(a(n)\mid n+1\), and reports experimentally
  that the sequence consists of 1's and primes and misses the larger twin primes
  above 7. For the companion sequence \(b_1(n)=b_1(n-1)+\operatorname{lcm}(n,b_1(n-1))\)
  (§3.2.1) it ties the first appearance of a prime factor \(p\) to the least prime
  \(\equiv-1\pmod p\), and remarks that the bound it would need (such a prime below
  \(p^2\)) is unlikely to be provable by elementary methods. Our structure lemmas and
  the obstruction above follow the same pattern for A135508.
- The harvest triage on 2026-10-24 found the criterion and the mod-3/mod-5 classes. It
  also found that the OEIS Open benchmark (arXiv:2608.11941; score files in
  epoch-research/LeanOpenProblems-results) lists attempts on the full statement
  `oeis_135508_conjecture_0`, all scored I (not proved).
- No novelty is claimed. The results are unreviewed and have not been reported to OEIS
  or to Formal Conjectures.
