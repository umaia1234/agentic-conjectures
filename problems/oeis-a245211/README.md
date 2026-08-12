**English** | [한국어](README.ko.md)

# OEIS A245211 progress report

Date checked: 2026-08-11

The expanded arguments are in the
[problem-local mathematical details](DETAILS.md).

## Conclusion and limitations

**The full conjecture is not yet resolved.** What this document proves is
only a strong necessary condition, a few complete partial classifications,
and an exact computation over the stated range.

[OEIS A245211](https://oeis.org/A245211) is defined by

\[
 a(n)=\sum_{\substack{d\mid n\\d<n}}d\,\tau(d)
\]

and carries the conjecture that the only solution of `a(n)=n` is `n=21`.
By the results below, if a counterexample exists it must belong to one of
the following two families.

1. A nonsquarefree number with unbounded exponents;
2. A squarefree number with an odd number of distinct prime factors, that
   number being at least 5.

Moreover, such a counterexample must be coprime to `2*3*5*7*11=2310`.

## Product form

Write the prime factorization as

\[
n=\prod_{i=1}^r p_i^{a_i},\qquad
D=\tau(n)=\prod_{i=1}^r(a_i+1)
\]

and write

\[
H_a(x)=\sum_{j=0}^a(j+1)x^j.
\]

Since the divisor sum of the function \(d\mapsto d\tau(d)\) is
multiplicative,

\[
\sum_{d\mid n}d\tau(d)=\prod_i H_{a_i}(p_i).
\]

Therefore `a(n)=n` is exactly equivalent to

\[
\boxed{\prod_i H_{a_i}(p_i)=n(D+1)}. \tag{1}
\]

\(n=21\) does indeed satisfy this equation.

## Proven lemmas

### 1. Lower bound for each prime factor

Let \(p_i^{a_i}\Vert n\). In the original proper-divisor sum, the single
term corresponding to \(d=n/p_i\) is

\[
\frac{n}{p_i}\tau(n/p_i)
=\frac{n}{p_i}\frac{a_iD}{a_i+1}.
\]

Since the other terms are also positive, this single term is less than
\(n\). Therefore every solution satisfies

\[
\boxed{p_i>a_i\frac{D}{a_i+1}
=a_i\prod_{j\ne i}(a_j+1)}. \tag{2}
\]

In particular, \(p_{\min}>\Omega(n)\). Indeed,

\[
\prod_{j\ne i}(a_j+1)\ge 1+\sum_{j\ne i}a_j,
\]

and multiplying the right-hand side by \(a_i\) gives at least
\(\sum_j a_j\).

### 2. Prime powers are not solutions

If \(n=p^a\), dividing (1) by \(p^a\) gives

\[
\frac a p+\frac{a-1}{p^2}+\cdots+\frac1{p^a}=1.
\]

By (2), \(p>a\), and the left-hand side is

\[
<\frac a p\left(1+\frac1p+\cdots\right)
=\frac{a}{p-1}\le1,
\]

a contradiction.

### 3. Exact 2-adic valuation at odd inputs

For odd \(x\), the following identity holds.

\[
\boxed{v_2(H_a(x))
=v_2\!\left(\frac{(a+1)(a+2)}2\right)}. \tag{3}
\]

Let us prove it. Setting \(m=a+1\), \(x=1+2u\),
\(T=m(m+1)/2\), we have

\[
H_a(x)=\sum_{k=1}^m kx^{k-1}.
\]

By the binomial expansion and the hockey-stick identity,

\[
H_a(1+2u)-T
=\sum_{t=1}^{m-1}2^tu^t(t+1){m+1\choose t+2}.
\]

The 2-adic valuation of the ratio of each coefficient to \(T\) is

\[
v_2\!\left(
\frac{2^t(t+1){m+1\choose t+2}}{T}
\right)
=v_2\!\left(
\frac{2^{t+1}{m-1\choose t}}{t+2}
\right)\ge1,
\]

because \(v_2(t+2)\le t\). Therefore
\(H_a(x)\equiv T\pmod {2^{v_2(T)+1}}\), and (3) follows.

Now if \(n\) is odd, taking the 2-adic valuation of (1) yields a necessary
condition determined by the exponents alone:

\[
\boxed{
\sum_i v_2\!\left(\frac{(a_i+1)(a_i+2)}2\right)
=v_2(D+1)}. \tag{4}
\]

### 4. Exclusion of the small prime factors 2, 3, 5, 7, 11

- `2`: If there are at least two distinct prime factors, the right-hand
  side of (2) is at least 2, so `2 > a_i D/(a_i+1)` is impossible. Prime
  powers were already excluded.
- `3`: By (2), \(3>a_iD_i\) with \(D_i\ge2\), so only
  \(a_i=1,D_i=2\) is possible. That is, \(n=3q\). The squarefree semiprime
  equation is

  \[
  (2p+1)(2q+1)=5pq
  \quad\Longleftrightarrow\quad
  (p-2)(q-2)=5,
  \]

  so only \(n=3\cdot7=21\) remains.
- `5`: The exponent patterns with \(5>a_iD_i\) in (2) are only
  `(1;1)`, `(1;2)`, `(1;3)`, `(1;1,1)`, `(2;1)`.
  The first case is handled by the semiprime classification above, the
  middle three nonsquarefree cases by (4), and the squarefree
  three-prime-factor case by the theorem of the next section.
- `7`: Applying (2) and (4), apart from the semiprime/squarefree
  three-prime-factor cases only `(1;4)` and `(1;5)` remain. If the latter
  two cases were \(n=7q^b\), then by (1) \(q^b\mid H_1(7)=15\), which is
  impossible since \(b\ge4\).
- `11`: After (2), (4), and the squarefree classification below, the
  remaining exponent patterns are

  \[
  (1;4),(1;5),(1;8),(1;9),(4;1),(5;1),(1;1,4).
  \]

  The first four cases are impossible because \(q^b\mid H_1(11)=23\).
  For `(4;1)` and `(5;1)`, directly rearranging (1) gives, respectively,

  \[
  q=78915/3221,\qquad q=1045221/3221,
  \]

  which are not integers. For the last case, write
  \(n=11pq^4\) and set

  \[
  B=H_4(q)=5q^4+4q^3+3q^2+2q+1;
  \]

  then (1) becomes

  \[
  p=\frac{23B}{q^4-184q^3-138q^2-92q-46}. \tag{5}
  \]

  For positivity we need the prime \(q\ge191\), and in this range the
  denominator exceeds \(q^3\), so (5) gives \(p<138q\). On the other hand,
  viewing (1) modulo \(q^4\), we get \(q^4\mid23(2p+1)\), and since
  \(q\ne23\), \(q^4\mid2p+1\). This contradicts \(2p+1<277q<q^4\).

Therefore any counterexample \(n\ne21\) is coprime to \(2310\).

### 5. Complete exclusion of squarefree three prime factors

Suppose \(n=xyz\), \(5\le x<y<z\) is a squarefree solution. Equation (1)
becomes

\[
(2x+1)(2y+1)(2z+1)=9xyz. \tag{6}
\]

The largest prime \(z\) must divide \(2x+1\) or \(2y+1\), and since both
numbers are less than \(2z\) and odd, it is in fact equal to one of them.

- If \(z=2y+1\), then (6) gives
  \((x-4)(y-6)=27\).
- If \(z=2x+1\), then (6) gives
  \((x-6)(y-4)=27\).

Substituting the positive divisors of 27, no case satisfies the primality
conditions and \(x<y<z\) simultaneously.

### 6. Squarefree with an even number of distinct prime factors is impossible

Let the number of prime factors be an even \(r\ge4\). By (2), every
\(p_i>2^{r-1}\); in particular \(p_i\ne3\). Equation (1) becomes

\[
\prod_i(2p_i+1)=(2^r+1)\prod_i p_i. \tag{7}
\]

For even \(r\), \(3\nmid2^r+1\). Therefore no factor on the left-hand side
is divisible by 3, so every \(p_i\equiv2\pmod3\). But then the left-hand
side of (7) is \(2^r=1\) mod 3, while the right-hand side is
\((2^r+1)2^r=2\), a contradiction.

## Exact computation results

### 1. All integers `n <= 10^9`

Using segmented factorization, \(D\) and \(\prod H_a(p)\) were computed as
integers and (1) was compared directly. Using the multiples-of-2, 3, 5, 7
exclusions proved above, only numbers with `gcd(n,210)=1` were tested, and
21 was included separately.

Result:

```text
limit 1000000000
coprime_to_210_tested 228571428
coarse_inequality_survivors 227185758
solutions 21
```

This is an exact computation over the finite range `n <= 10^9`, not a proof
of the infinite statement.

Source:

```text
Absolute path: /home/user/projects/agentic-conjectures/problems/oeis-a245211/a245211_scan.cpp
Relative to workspace root: problems/oeis-a245211/a245211_scan.cpp
SHA256:   712cb0294def17f7300b921ca1a393a9618865f5a55609a819c0681f533f345e
```

Reproduction:

```bash
g++ -O3 -march=native -std=c++17 -Wall -Wextra \
  problems/oeis-a245211/a245211_scan.cpp -o /tmp/a245211_scan
/tmp/a245211_scan 1000000000 1000000
```

### 2. The case of exactly two distinct prime factors

Let \(n=p^a q^b\), \(p<q\). From equation (1),
\(q^b\mid H_a(p)\). Moreover, using (2) and
\(H_a(p)<(a+2)p^a\), \(b>a\) is impossible, so \(b\le a\).

For fixed \((a,b)\), (2) gives \(p>a(b+1)\). Since the normalized local
factor is decreasing in the prime, it suffices to test \(p\) only while

\[
H_a(p)H_b(p)>(D+1)p^{a+b}
\]

holds, and every prime after the first failure of this condition is
automatically excluded. Therefore the range of \(p\) is finite.

Suppose a \(p\) is fixed. Set

\[
G=(D+1)p^a-(b+1)H_a(p),\qquad y=G/H_a(p).
\]

The required \(q\) must satisfy

\[
y=\frac bq+\frac{b-1}{q^2}+\cdots+\frac1{q^b}.
\]

But

\[
\frac bq\le y<\frac b{q-1},
\]

so within an interval of length less than 1 only the single value

\[
q=\left\lceil\frac{bH_a(p)}G\right\rceil
\]

is possible. The code re-checks the primality of this integer and the
original equation (1) with exact integer arithmetic.

Result of testing all exponent pairs with `1 <= b <= a <= 200`:

```text
Exponent pairs passing the 2-adic condition: 4204
Prime candidates checked exactly: 388919
Solutions: (p,a,q,b) = (3,1,7,1)
```

For each exponent pair, this computation checks the entire possible range
without imposing a separate upper bound on the size of the primes \(p,q\).
However, the restriction to exponents `a,b <= 200` remains.

Source:

```text
Absolute path: /home/user/projects/agentic-conjectures/problems/oeis-a245211/a245211_two_prime.py
Relative to workspace root: problems/oeis-a245211/a245211_two_prime.py
SHA256:   7d1a9fb86f08eac506c4081f0d90d690cc98eccee0f0ad59dee8e73224ff3fed
```

Reproduction:

```bash
python3 problems/oeis-a245211/a245211_two_prime.py 200
```

## Remaining problems

The core cases not fully handled by proof are the following.

- Two prime factors but with exponents exceeding 200;
- The general nonsquarefree case with three or more prime factors;
- The squarefree case with an odd number \(r\ge5\) of distinct prime
  factors.

Therefore the present result is not a proof of the A245211 conjecture, but
partial progress that greatly reduces the forms a future proof must
address.

## Upstream Lean formalization

The FormalConjectures [original snapshot and provenance record](upstream/README.md)
is preserved in [`245211_cbf46b82.lean`](upstream/245211_cbf46b82.lean).
The theorem recording the uniqueness of `21` is a `by sorry` **conjecture
statement**, not a formal proof. The results of this folder are likewise
limited to the necessary conditions and partial classifications stated
above.
