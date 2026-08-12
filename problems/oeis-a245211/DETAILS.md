**English** | [한국어](DETAILS.ko.md)

# OEIS A245211: Weighted Proper-Divisor Sum

## 1. The Basic Equation

Define the following.

\[
S(n)=\sum_{\substack{d\mid n\\d<n}}d\,\tau(d).
\]

The conjecture is that the unique solution of

\[
S(n)=n
\]

is \(n=21\). Write the prime factorization as

\[
n=\prod_{i=1}^r p_i^{a_i},\qquad
D=\tau(n)=\prod_{i=1}^r(a_i+1)
\]

and define

\[
H_a(x)=\sum_{j=0}^a(j+1)x^j.
\]

The function \(d\mapsto d\tau(d)\) is multiplicative, so

\[
\sum_{d\mid n}d\tau(d)=\prod_iH_{a_i}(p_i).
\]

Subtracting \(n\tau(n)=nD\) from the full divisor sum yields the
proper-divisor sum, so

\[
\boxed{
S(n)=n
\quad\Longleftrightarrow\quad
\prod_iH_{a_i}(p_i)=n(D+1)
}.
\tag{A245-1}
\]

Indeed, for \(n=21=3\cdot7\),

\[
H_1(3)H_1(7)=7\cdot15=105=21(4+1),
\]

so it is a solution.

## 2. A Strong Lower Bound for Each Prime Factor

If \(n=1\), then \(S(n)=0\); and if \(n=p\) is prime, then
\(S(p)=1\); so neither is a solution. Hence any potential solution is
composite.

Let \(p_i^{a_i}\Vert n\). In the original proper-divisor sum, the
single term with \(d=n/p_i\) is

\[
\frac n{p_i}\tau(n/p_i)
=\frac n{p_i}\frac{a_iD}{a_i+1}.
\]

For composite numbers, \(n/p_i>1\), so \(d=1\) is a positive term
different from this one. If the total sum equals \(n\), the selected
term is strictly less than \(n\). Hence every solution satisfies

\[
\boxed{
p_i>a_i\frac D{a_i+1}
=a_i\prod_{j\ne i}(a_j+1)
}.
\tag{A245-2}
\]

In particular,

\[
\prod_{j\ne i}(a_j+1)
\ge1+\sum_{j\ne i}a_j
\]

and since \(a_i\ge1\),

\[
a_i\left(1+\sum_{j\ne i}a_j\right)
\ge a_i+\sum_{j\ne i}a_j.
\]

Therefore

\[
\boxed{p_{\min}>\Omega(n)=\sum_i a_i}.
\tag{A245-3}
\]

## 3. Complete Exclusion of Prime Powers

If \(n=p^a\), dividing (A245-1) by \(p^a\) yields

\[
\frac ap+\frac{a-1}{p^2}+\cdots+\frac1{p^a}=1.
\tag{A245-4}
\]

By (A245-2), \(p>a\). But the left-hand side is

\[
<\frac ap\left(1+\frac1p+\frac1{p^2}+\cdots\right)
=\frac a{p-1}\le1
\]

and the first inequality is strict, a contradiction. Hence no prime
power, including primes themselves, is a solution.

## 4. Exact 2-adic Valuation for Odd Inputs

**Lemma.** For odd \(x\) and \(a\ge0\),

\[
\boxed{
v_2(H_a(x))
=v_2\!\left(\frac{(a+1)(a+2)}2\right)
}.
\tag{A245-5}
\]

**Proof.** Set \(m=a+1\), \(x=1+2u\), \(T=m(m+1)/2\); then

\[
H_a(x)=\sum_{k=1}^m kx^{k-1}.
\]

By the binomial expansion and the hockey-stick identity,

\[
H_a(1+2u)-T
=\sum_{t=1}^{m-1}2^tu^t(t+1){m+1\choose t+2}.
\tag{A245-6}
\]

For each \(t\), the ratio of the coefficient to \(T\) is, inside the
2-adic field,

\[
\frac{2^t(t+1){m+1\choose t+2}}T
=\frac{2^{t+1}}{t+2}{m-1\choose t}.
\]

For \(t\ge1\) we have \(v_2(t+2)\le t\), so the 2-adic valuation of
this ratio is at least 1. Hence

\[
H_a(x)\equiv T\pmod{2^{v_2(T)+1}},
\]

i.e., the exact 2-adic valuations of the two numbers coincide.
\(\square\)

Now, if \(n\) is odd, taking the 2-adic valuation of (A245-1) yields
the necessary condition

\[
\boxed{
\sum_i
v_2\!\left(\frac{(a_i+1)(a_i+2)}2\right)
=v_2(D+1)
}
\tag{A245-7}
\]

which is independent of the sizes of the primes and determined solely
by the exponent pattern. In particular,

\[
v_2\!\left(\frac{(a+1)(a+2)}2\right)=0
\quad\Longleftrightarrow\quad
a\equiv0,1\pmod4.
\tag{A245-8}
\]

## 5. Partial Classification of Squarefree Solutions

If all exponents are 1 and the number of distinct prime factors is
\(r\), then (A245-1) becomes

\[
\boxed{
\prod_{i=1}^r(2p_i+1)
=(2^r+1)\prod_{i=1}^rp_i
}.
\tag{A245-9}
\]

### \(r=1\)

Included in the prime-power exclusion.

### \(r=2\)

If \(n=pq\), then

\[
(2p+1)(2q+1)=5pq,
\]

that is,

\[
\boxed{(p-2)(q-2)=5}.
\]

Hence \(\{p,q\}=\{3,7\}\), and the only squarefree semiprime solution
is \(21\).

### \(r=3\)

Let \(n=xyz\), \(5\le x<y<z\). By (A245-2) each prime exceeds 4. The
equation reads

\[
(2x+1)(2y+1)(2z+1)=9xyz.
\tag{A245-10}
\]

The largest prime \(z\) must divide one of the factors on the
left-hand side. Since \(z\nmid2z+1\) and \(z\ne3\), either
\(z\mid2x+1\) or \(z\mid2y+1\). Both numbers are less than \(2z\), so

\[
z=2x+1\quad\text{or}\quad z=2y+1.
\]

- If \(z=2y+1\), canceling \(z\) in (A245-10) gives

  \[
  (x-4)(y-6)=27.
  \]

- If \(z=2x+1\), similarly

  \[
  (x-6)(y-4)=27.
  \]

Substituting the positive divisors \(1,3,9,27\) of 27, no case
produces three primes with \(x<y<z\). Hence there is no solution with
\(r=3\).

### Even \(r\ge4\)

From (A245-2), every \(p_i>2^{r-1}\); in particular \(p_i\ne3\). For
even \(r\), \(2^r+1\equiv2\pmod3\). The right-hand side of (A245-9)
is not divisible by 3, so no factor on the left-hand side may be
divisible by 3. Hence every \(p_i\equiv2\pmod3\). But then

\[
\prod_i(2p_i+1)\equiv2^r\equiv1\pmod3,
\]

whereas

\[
(2^r+1)\prod_ip_i\equiv2\cdot2^r\equiv2\pmod3,
\]

a contradiction.

In the end, in the squarefree case only \(21\) has been confirmed, and
the only shape not yet excluded by this argument is odd \(r\ge5\).

## 6. Small Prime Factors \(2,3,5,7,11\)

Below, \((a;b_1,b_2,\ldots)\) means that the exponent of the
designated small prime is \(a\) and the multiset of the exponents of
the remaining prime factors is \(b_1,b_2,\ldots\).

### Prime factors 2 and 3

If \(2^a\Vert n\) and there is another prime factor, the right-hand
side of (A245-2) is at least 2, so the strict inequality
\(2>aD/(a+1)\) is impossible. Since prime powers are already
excluded, every solution is odd.

If \(3^a\Vert n\) and there is another prime factor, then

\[
3>a\prod_{j\ne i}(a_j+1).
\]

The product on the right is at least 2, so \(a=1\) and the remaining
exponent pattern consists of a single exponent 1. That is, \(n=3q\),
and by the earlier semiprime classification \(n=21\).

### Prime factor 5

The only exponent patterns allowed by the condition that the
right-hand side of (A245-2) be less than 5 are

\[
(1;1),(1;2),(1;3),(1;1,1),(2;1).
\]

Applying (A245-7) leaves only \((1;1)\) and \((1;1,1)\). The former,
by the semiprime classification, gives only 21, which does not contain
5; the latter is impossible by the squarefree three-prime-factor
exclusion. Hence 5 divides no solution.

### Prime factor 7

This time \(a\prod_{j\ne i}(a_j+1)\le6\). Filtering the possible
exponent patterns through (A245-7), apart from the semiprime and
squarefree three-prime-factor cases only

\[
(1;4),\qquad(1;5)
\]

remain. Let \(n=7q^b\), \(b\in\{4,5\}\). Viewing (A245-1) modulo
\(q^b\), since \(\gcd(H_b(q),q)=1\),

\[
q^b\mid H_1(7)=15,
\]

which is impossible. Hence the only solution containing 7 is 21 as
well.

### Prime factor 11

Filtering the exponent patterns with
\(a\prod_{j\ne i}(a_j+1)\le10\) through (A245-7) and excluding the
earlier squarefree classification leaves only

\[
(1;4),(1;5),(1;8),(1;9),(4;1),(5;1),(1;1,4).
\]

In the first four cases, \(n=11q^b\) with \(b\ge4\), and

\[
q^b\mid H_1(11)=23
\]

follows, which is impossible. For \((4;1)\) and \((5;1)\), solving
(A245-1) gives, respectively,

\[
q=\frac{78915}{3221},\qquad
q=\frac{1045221}{3221},
\]

which are not integers.

Finally, let \(n=11pq^4\) and set

\[
B=H_4(q)=5q^4+4q^3+3q^2+2q+1.
\]

Here \(D=20\) and (A245-1) reads

\[
23(2p+1)B=231pq^4.
\]

Solving this for \(p\),

\[
p=\frac{23B}{q^4-184q^3-138q^2-92q-46}.
\tag{A245-11}
\]

For the denominator to be positive we need \(q>184\), hence the prime
\(q\ge191\). In this range the denominator exceeds \(q^3\) and
\(B<6q^4\), so

\[
p<138q.
\]

Meanwhile, viewing the original equation modulo \(q^4\),

\[
q^4\mid23(2p+1)B.
\]

Since \(B\equiv1\pmod q\) and \(q\ne23\), we get \(q^4\mid2p+1\).
But

\[
0<2p+1<277q<q^4,
\]

a contradiction. Hence 11 divides no solution either.

In conclusion, every potential solution other than \(21\) satisfies

\[
\boxed{\gcd(n,2310)=1}
\tag{A245-12}
\]

and its smallest prime factor is at least 13.

## 7. The Case of Exactly Two Distinct Prime Factors

Let

\[
n=p^aq^b,\qquad p<q.
\]

(A245-1) is

\[
H_a(p)H_b(q)=p^aq^b\bigl((a+1)(b+1)+1\bigr).
\tag{A245-13}
\]

Since \(H_b(q)\equiv1\pmod q\),

\[
\boxed{q^b\mid H_a(p)}.
\tag{A245-14}
\]

### Ordering of the exponents: \(b\le a\)

The normalized local factor is

\[
F_a(x)=\frac{H_a(x)}{x^a}
=(a+1)+\frac ax+\frac{a-1}{x^2}+\cdots+\frac1{x^a}.
\]

From (A245-2), \(p>a(b+1)\), and by the geometric-series upper bound
on the tail,

\[
\frac ap+\frac{a-1}{p^2}+\cdots+\frac1{p^a}
<\frac a{p-1}<1,
\]

hence

\[
H_a(p)<(a+2)p^a.
\tag{A245-15}
\]

If \(b>a\), then \(b\ge a+1\). If \(a=1\), then \(p>3\), so
\(p>a+2\); and if \(a\ge2\), then \(p>a(a+2)>a+2\). Hence

\[
q^b>p^{a+1}>(a+2)p^a>H_a(p),
\]

contradicting (A245-14). Therefore

\[
\boxed{b\le a}.
\tag{A245-16}
\]

### Complete finite reduction for each fixed exponent pair

Setting \(D=(a+1)(b+1)\), (A245-13) is

\[
F_a(p)F_b(q)=D+1.
\tag{A245-17}
\]

\(F_a(x)\) is strictly decreasing for \(x>0\). Since \(q>p\), a
necessary condition is

\[
F_a(p)F_b(p)>D+1.
\tag{A245-18}
\]

The left-hand side decreases in \(p\) with limit \(D\), so for fixed
\((a,b)\) only finitely many \(p\) satisfy (A245-18).

Now fix \(p\) and set

\[
G=(D+1)p^a-(b+1)H_a(p),
\qquad
y=\frac G{H_a(p)}.
\]

(A245-17) is equivalent to

\[
y=\frac bq+\frac{b-1}{q^2}+\cdots+\frac1{q^b}.
\tag{A245-19}
\]

Hence if \(G\le0\) there is no solution, and if \(G>0\), then

\[
\frac bq\le y<\frac b{q-1}.
\]

Inverting this,

\[
\frac by\le q<\frac by+1.
\]

Only one integer can lie in a half-open interval of length 1, so

\[
\boxed{
q=\left\lceil\frac{bH_a(p)}G\right\rceil
}.
\tag{A245-20}
\]

That is, each fixed exponent pair \((a,b)\) is completely decided by
checking finitely many \(p\) and, for each \(p\), only a single
candidate \(q\). The important limitation is that this argument does
not give a global upper bound on the exponent pairs themselves.

In an exact finite enumeration checking the 4,204 exponent pairs with
\(1\le b\le a\le200\) admissible under the 2-adic valuation condition
and 388,919 prime candidates, the only solution was

\[
(p,a,q,b)=(3,1,7,1).
\]

This is a theorem only for exponents up to 200, not a proof for all
exponents.

## 8. Currently Remaining Cases

In a separate complete integer enumeration, computing both sides of
(A245-1) directly from the prime factorization,

\[
\boxed{
1\le n\le10^9,\quad S(n)=n
\quad\Longleftrightarrow\quad n=21
}
\]

was also verified. This is an exact statement for the stated finite
range and does not eliminate the remaining infinite families below.

The results above prove the following.

- All prime powers are impossible.
- The only squarefree semiprime solution is 21.
- Squarefree with three prime factors, and squarefree with an even
  number \(r\ge4\) of prime factors, are impossible.
- No solution other than 21 is divisible by any of the primes
  \(2,3,5,7,11\).
- Every fixed exponent pair for two prime factors can be effectively
  decided in finitely many steps.

However, the following infinite families remain.

1. The case of two distinct prime factors with unbounded exponents
   \((a,b)\),
2. the general nonsquarefree case with three or more distinct prime
   factors,
3. the squarefree case with an odd number \(r\ge5\) of prime factors.

Hence the full conjecture for A245211 remains unresolved.
