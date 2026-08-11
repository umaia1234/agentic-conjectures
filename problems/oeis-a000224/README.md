**English** | [한국어](README.ko.md)

# OEIS A000224 Conjecture Attack Log

Date of verification: 2026-08-12.

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
subtraction, while its `1<n` hypothesis excludes the boundary values. The proof
only formalizes the even subcase: it reduces the claimed congruence modulo 2
and contradicts the parity of an even square. The axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

```bash
lake build
python3 scripts/check_axioms.py
```

With the mathlib cache already populated, the full build took 7.3 seconds and
the axiom audit took 3.6 seconds on the verification machine (2026-08-12).

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

## Limitations

- The general `p^e q^f` case and the case of four or more distinct
  prime factors are not yet proved.
- What lies outside the `K,n` bounds of the Pell search also remains.
- We therefore do not claim to have resolved the OEIS conjecture
  itself.

## Upstream Lean formalization

The FormalConjectures [original snapshot and provenance record](upstream/README.md)
is preserved in [`224_2322a58c.lean`](upstream/224_2322a58c.lean). That file is a
**conjecture statement** with the full equivalence written as `by sorry`, not a
formal proof. The results in this folder prove only the subfamilies specified
above.
