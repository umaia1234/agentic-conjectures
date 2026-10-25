**English** | [한국어](README.ko.md)

# OEIS A000224 Conjecture Attack Log

Date of verification: 2026-08-12; Lean extension to prime powers and
two-prime products: 2026-10-24.

The expanded definitions and proofs are in the
[problem-local mathematical details](DETAILS.md).

Let `R(n)` denote the number of distinct quadratic residues modulo `n`
(including 0). [OEIS A000224](https://oeis.org/A000224) conjectures the
following.

> For `n>1`, `R(n)(R(n)-1) | n^2-1` holds if and only if `n` is an odd
> prime.

OEIS records that this has been checked up to `10^8`. The results below
are not a proof of the full conjecture, but rigorous partial theorems
obtained in the composite direction together with additional
computational exploration.

## Scope proved in this work

There is no composite counterexample in the following three classes.

1. all even `n`;
2. all odd prime powers `p^e`, `e>=2`;
3. products `p*q` of two distinct odd primes.

Therefore, if a counterexample exists, it is odd, has at least two
distinct prime factors, and `Omega(n)`, counting prime factors with
multiplicity, is at least 3. The third item is a computer-assisted
proof that uses a small finite computation as its final step.

All three items, and this conclusion about the shape of a
counterexample, are kernel-checked in Lean 4 against the exact upstream
definition; see [Lean 4 formalization](#lean-4-formalization). The Lean
module also proves that the upstream equivalence holds at every prime
power and at every `n>1` with `Omega(n)<=2`.

## Preliminary identities

`R` is multiplicative, and for an odd prime `p`,

```text
R(p^e) = floor(p^(e+1)/(2p+2)) + 1.
```

More concretely, letting `r=R(p^e)`,

```text
2(p+1)r = p^(e+1) + 2p+1    (e odd),
2(p+1)r = p^(e+1) + p+2     (e even).
```

If the divisibility condition holds, then of course

```text
gcd(n, R(n)(R(n)-1)) = 1.                         (1)
```

The converse direction is verified immediately. If `p` is an odd prime,
then `R(p)=(p+1)/2`, so

```text
R(p)(R(p)-1) = (p^2-1)/4.
```

Hence the quotient is exactly 4.

## Even numbers and prime powers

If `n` is even, then `n^2-1` is odd, whereas the product `R(R-1)` of
two consecutive integers is even, so this case is immediately
impossible.

This even-input exclusion is also kernel-checked in Lean 4. The theorem
[`even_not_conjecture_rhs`](../../AgenticConjectures/OeisA000224.lean) uses
the exact `A000224` definition and `Nat.ModEq` congruence from the pinned
upstream snapshot. It retains the upstream `n=0` convention and natural-number
subtraction, while its `1<n` hypothesis excludes the boundary values. This
theorem covers the even subcase only: it reduces the claimed congruence
modulo 2 and contradicts the parity of an even square. The prime-power and
two-prime cases below are formalized in the same module; reproduction
commands and runtimes are in [Lean 4 formalization](#lean-4-formalization).

Now let `n=p^e` with `p` odd and `e>=2`.

- If `e` is even, reducing the identity above modulo `p` gives
  `r == 1 (mod p)`. Hence `p | r-1`, but `p` cannot divide
  `p^(2e)-1`, contradicting (1).
- If `e` is odd, then

  ```text
  r   = (X+2p+1)/(2(p+1)),
  r-1 = (X-1)/(2(p+1)),       X=p^(e+1).
  ```

  Direct comparison yields the following open intervals.

  ```text
  4r(r-1) < p^(2e)-1 < 5r(r-1),       p>=11;
  5r(r-1) < p^(2e)-1 < 6r(r-1),       p=5,7;
  7r(r-1) < p^(2e)-1 < 8r(r-1),       p=3, e>=5.
  ```

  The remaining case `(p,e)=(3,3)` has `r=11` and
  `6*110 < 27^2-1 < 7*110`. In no case is the ratio an integer.

Multiplying the comparison inequalities by the positive number
`4p^2(p+1)^2` turns them into simple sign checks of quadratics. For
example, the difference from the 4-fold multiple is

```text
4(X-p^2)(2Xp+X+p^2) > 0,
```

and the leading coefficient in the 5-fold case is `-p^2+8p+4<0`
(`p>=11`). For `p=3,5,7` one substitutes the boundary values written
above.

The Lean proof of the odd-exponent case does not use these intervals. It
follows the gcd argument of [DETAILS.md](DETAILS.md) §4: `r-1` divides
both `p^(e+1)-1` and `p^(2e)-1`, hence `p^2-1`, but `r-1>p^2-1`.

## Products of two distinct primes

Let `n=pq`, `3<=p<q`, and set

```text
a=(p+1)/2,  b=(q+1)/2,  R=ab
```

Assume the divisibility holds and set

```text
K=(n^2-1)/(R(R-1))
```

then `K` is a positive integer.

First, direct expansion gives

```text
16R(R-1) - (n^2-1)
 = 2p^2q+p^2+2pq^2-2p+q^2-2q-2 > 0,
```

so `K<=15`. On the other hand, since `n^2>R`,

```text
K > (n/R)^2
  = ((2-1/a)(2-1/b))^2
  > (2-1/a)^4.
```

If `a>=32`, the right-hand side is `(63/32)^4>15`
(`63^4-15*32^4=24321`). Therefore necessarily `a<=31`, i.e., `p<=61`.

Also, since `R | n^2-1` and `q == -1 (mod b)`,

```text
b | p^2-1 = 4a(a-1).                               (2)
```

Now it suffices to check the primes `p<=61` and the divisors from (2).
`semiprime_certificate.py` enumerates exactly this finite set without
any external libraries. The raw candidates obtained from condition (2)
and the primality condition number 117 pairs, of which only 22 pairs
also pass `R | n^2-1`. In all of those cases we verify that
`(n^2-1) mod (R-1)` is nonzero.

Reproduction command:

```bash
python problems/oeis-a000224/semiprime_certificate.py \
  --output problems/oeis-a000224/semiprime_result.json
```

The Lean proof replaces this enumeration by a `decide` check that needs
no primality test. Write `4a(a-1)=bc`. Then `b>a` forces `c<4a`, so it
runs over the 1950 pairs `(a,c)` with `2<=a<=31`, `1<=c<4a`. For the 392
pairs with `c | 4a(a-1)` and `b=4a(a-1)/c>a`, it checks that
`((2a-1)(2b-1))^2` is not `1` modulo `ab-1`. The script remains as an
independent check.

## Additional local conditions every potential counterexample must satisfy

Let `p^e || n`, `m=n/p^e`, `r_p=R(p^e)`, and set

```text
c_p = 2p+1  (e odd),
c_p = p+2   (e even)
```

If `R(n) | n^2-1`, then `r_p | n^2-1`. From the preliminary identities
above, `p^(e+1) == -c_p (mod r_p)` and `gcd(p,r_p)=1`, so

```text
r_p | m^2*c_p^2 - p^2.                             (3)
```

The right-hand side is positive. In particular,

```text
p^(e+1) < 2(p+1)m^2*c_p^2,
```

so candidates in which one prime power is excessively large relative to
the cofactor are automatically excluded. This condition is useful for
branch-and-bound over the remaining `p^e q^f` and many-prime-factor
cases.

## Generalized-Pell search

If the division quotient `K` is an integer, then for `X=2n`, `Y=2R-1`
we have exactly

```text
X^2-KY^2 = 4-K                                      (4)
```

`pell_quotient_scan.py` enumerates all CAS-generated candidates of (4)
with `K<=375`, `n<=10^18`, and then recomputes `R(n)` by actual prime
factorization. This is a Pell-orbit scan, not a linear range scan.

Writing `omega(n)=s` for the number of distinct prime factors of an odd
`n`, at each local factor

```text
p^e/R(p^e) < 2(p+1)/p <= 8/3.
```

Hence for `s<=3` the potential quotient satisfies `K<=375`. This search
therefore also covers every unresolved shape with `n<=10^18` and
`omega(n)<=3`. However, the completeness of the Pell seeds depends on
SymPy's exact `diop_DN` implementation, so this part is classified as a
reproducible CAS-assisted computation, not an independent formal proof
of the full conjecture.

```bash
python problems/oeis-a000224/pell_quotient_scan.py \
  --max-k 375 --max-n 1000000000000000000 \
  --output problems/oeis-a000224/pell_result.json
```

`K=1` gives only `n=1` from `(X-Y)(X+Y)=3`. `K=4` is handled by a
separate proof. (4) forces `n=2R-1`. For an odd prime power `x=p^e` we
have `R(x)<=(x+1)/2`, with equality only when `e=1`. For coprime odd
`u,v>1`,

```text
R(uv)=R(u)R(v) <= (u+1)(v+1)/4 < (uv+1)/2,
```

so for odd `n>1` the cases with `R(n)=(n+1)/2` are exactly the odd
primes.

## Lean 4 formalization

The results for even numbers, prime powers, and products of two distinct
primes are formalized, `sorry`-free and against mathlib only, in
[`AgenticConjectures/OeisA000224.lean`](../../AgenticConjectures/OeisA000224.lean)
(namespace `AgenticConjectures.OeisA000224`). Below, `RHS(n)` is the
upstream right-hand side `n * n ≡ 1 [MOD A000224 n * (A000224 n - 1)]`.
The two headline statements are:

- for every `n>1` with `Omega(n)<=2`, and for every prime power `p^e`
  with `e>=1`, the upstream equivalence
  `(n.Prime ∧ n ≠ 2) ↔ RHS(n)` holds;
- every `n>1` that violates the upstream equivalence is odd, is not a
  prime power, and has `Omega(n)>=3`.

| Declaration | Content |
|---|---|
| `A000224` | the upstream definition, term for term (`1` at `n=0`, otherwise the number of distinct `k^2 % n` for `k<n`) |
| `even_not_conjecture_rhs` | no even `n>1` satisfies `RHS(n)` (unchanged from the first formalization) |
| `two_mul_A000224_prime` | `2R(p)=p+1` for an odd prime `p` |
| `two_mul_A000224_prime_pow_add_two` | `2R(p^(e+2)) = p^(e+1)(p-1) + 2R(p^e)`, i.e. `R(p^(e+2)) = R(p^e) + φ(p^(e+2))/2`, for an odd prime `p` |
| `A000224_prime_pow_even`, `A000224_prime_pow_odd` | the closed form (A224-3): `2(p+1)R(p^(2k)) = p^(2k+1)+p+2` and `2(p+1)R(p^(2k+1)) = p^(2k+2)+2p+1` |
| `odd_prime_conjecture_rhs` | every odd prime `p` satisfies `RHS(p)` (quotient 4) |
| `odd_prime_pow_not_conjecture_rhs` | no `p^e` with `p` an odd prime and `e>=2` satisfies `RHS(p^e)` |
| `conjecture_prime_pow` | the upstream equivalence at every prime power `p^e`, `e>=1` (including `p=2`) |
| `A000224_mul` | `R(mn)=R(m)R(n)` for coprime `m,n>0` (Chinese remainder theorem) |
| `odd_primes_mul_not_conjecture_rhs` | no product `pq` of two distinct odd primes satisfies `RHS(pq)` |
| `conjecture_mul_primes` | the upstream equivalence at every product `pq` of two distinct primes |
| `conjecture_of_primeFactorsList_length_le_two` | the upstream equivalence at every `n>1` with `Omega(n)<=2` |
| `counterexample_shape` | a counterexample `n>1` satisfies `Odd n`, `¬ IsPrimePow n`, and `Omega(n)>=3` |

Method. Modulo `p^e` (`p` odd, `e>=1`) the squares split into those
prime to `p` and those divisible by `p`. Squaring is exactly two-to-one
on the residues prime to `p`: if `k^2 == l^2`, then `p` cannot divide
both `l-k` and `l+k`, so `p^e` divides one of them. This gives
`φ(p^e)/2` unit squares. The squares divisible by `p` are `p^2 t` with
`t` a square modulo `p^(e-2)` when `e>=2`, and only `0` when `e=1`.
This gives the recursion, and a two-step induction gives (A224-3). The
prime-power exclusion follows the argument of [DETAILS.md](DETAILS.md)
§4: for even `e`, `p | r-1`; for odd `e`, `r-1 | p^2-1` while
`r-1>p^2-1`. In the two-prime case, multiplicativity gives `R=ab` with
`a=R(p)<b=R(q)`. Then `b | 4a(a-1)` because `q == -1 (mod b)`. If
`a>=32`, explicit polynomial identities give
`15R(R-1) < n^2-1 < 16R(R-1)`. The remaining `a<=31` cases are the
`decide` check described above.

Statement faithfulness. `A000224` is copied verbatim from the upstream
snapshot, including its `n=0` convention and the `%` on `ℕ`. `RHS(n)` is
the upstream right-hand side, with the same natural-number subtraction
`A000224 n - 1`; for `n>=1` we have `A000224 n>=1`, so no truncation
occurs. The left-hand side `n.Prime ∧ n ≠ 2` is also copied verbatim,
and squares are written `n * n` as upstream (`p ^ e * p ^ e`,
`p * q * (p * q)`). The upstream hypothesis `1<n` appears explicitly in
`even_not_conjecture_rhs`, `conjecture_of_primeFactorsList_length_le_two`
and `counterexample_shape`. Elsewhere it follows from the hypotheses
(`p^e` with `p` prime and `e>=1`, or `pq` with `p,q` prime). Here
`Omega(n)` is `n.primeFactorsList.length` (prime factors counted with
multiplicity), and "not a prime power" is mathlib's `¬ IsPrimePow n`.

Reproduction (from the repository root; `lake build` and
`check_axioms.py` need the mathlib cache):

```bash
lake build AgenticConjectures.OeisA000224   # this module alone
lake build                                  # whole library (needed by check_axioms.py)
python3 scripts/check_sorry.py
python3 scripts/check_axioms.py             # only propext / Classical.choice / Quot.sound
```

On the verification machine (2026-10-24, shared Apple M5 Max, mathlib
cache populated), the module built in 12 seconds. The `decide` step
took about 0.4 seconds to elaborate and 0.3 seconds to kernel-check. A
full `lake build` after that took 9.5 seconds, and the axiom audit took
8.2 seconds. For the first, even-only version, the full build took
7.3 seconds and the audit 3.6 seconds (2026-08-12).
For all 13 theorems registered in `status.yaml`, the axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`.

Not claimed: the full conjecture, the general `p^e q^f` case with
`Omega(n)>=3`, and anything about three or more distinct primes. The
Pell scan stays a script-checked computation and is not formalized.

## Limitations

- Composite cases that are not prime powers and have `Omega(n)>=3` are
  not proved. These are the general `p^e q^f` case and every case with
  three or more distinct prime factors. The Pell scan searches
  `omega(n)<=3` only up to `n<=10^18`.
- What lies outside the `K,n` bounds of the Pell search also remains.
- We therefore do not claim to have resolved the OEIS conjecture
  itself.

## Upstream Lean formalization

The FormalConjectures [original snapshot and provenance record](upstream/README.md)
is preserved in [`224_2322a58c.lean`](upstream/224_2322a58c.lean). That file is a
**conjecture statement** with the full equivalence written as `by sorry`, not a
formal proof. The results in this folder prove only the subfamilies specified
above. The Lean module proves the upstream equivalence on exactly those
subfamilies (every prime power and every `n>1` with `Omega(n)<=2`), not the
universal statement.
