**English** | [한국어](PROOF.ko.md)

# Excluding a prime power \(n+12\) in A056777

## Problem and theorem

Suppose a composite number \(n\ge4\) simultaneously satisfies

\[
\varphi(n+12)=\varphi(n)+12, \tag{1}
\]

\[
\sigma(n+12)=\sigma(n)+12 \tag{2}
\]

**Theorem.** For a composite \(n\ge4\) satisfying (1) and (2), \(n+12\)
cannot be a prime power.

## Four auxiliary functions and invariants

Set

\[
N:=n+12
\]

and define

\[
A(m):=m-\varphi(m),
\qquad
B(m):=\sigma(m)-m,
\qquad
T(m):=B(m)-A(m)
\]

From (1),

\[
\begin{aligned}
A(N)&=N-\varphi(N)\\
&=(n+12)-(\varphi(n)+12)\\
&=n-\varphi(n)=A(n).
\end{aligned}
\]

Similarly from (2), \(B(N)=B(n)\), hence

\[
A(N)=A(n),\qquad B(N)=B(n),\qquad T(N)=T(n). \tag{3}
\]

Now set

\[
Q(m):=A(m)B(m)-mT(m)
\]

Expanding the definition,

\[
\begin{aligned}
Q(m)
&=(m-\varphi(m))(\sigma(m)-m)\\
&\quad-m(\sigma(m)-m-(m-\varphi(m)))\\
&=m^2-\varphi(m)\sigma(m).
\end{aligned} \tag{4}
\]

Using (3),

\[
\begin{aligned}
Q(n)
&=A(n)B(n)-nT(n)\\
&=A(N)B(N)-(N-12)T(N)\\
&=Q(N)+12T(N).
\end{aligned} \tag{5}
\]

## If there are at least two distinct prime factors, then \(Q(m)>m\)

Let

\[
m=\prod_i r_i^{e_i}
\]

At each prime power,

\[
\varphi(r^e)\sigma(r^e)
=r^{e-1}(r-1)\frac{r^{e+1}-1}{r-1}
=r^{2e}\left(1-\frac1{r^{e+1}}\right).
\]

By multiplicativity,

\[
\varphi(m)\sigma(m)
=m^2\prod_i\left(1-\frac1{r_i^{e_i+1}}\right).
\]

Therefore

\[
Q(m)=m^2\left[1-\prod_i\left(1-\frac1{r_i^{e_i+1}}\right)\right]. \tag{6}
\]

Suppose \(m\) has at least two distinct prime factors. Let \(r\) be its
smallest prime factor and write

\[
r^e\parallel m,\qquad m=r^eu
\]

then \(u>r\) since there is another prime factor. From (6),

\[
1-\prod_i(1-x_i)>x_r=\frac1{r^{e+1}},
\]

hence

\[
Q(m)>\frac{m^2}{r^{e+1}}=m\frac ur>m. \tag{7}
\]

## The assumption \(N=q^\ell\)

For contradiction, assume

\[
N=q^\ell
\]

where \(q\) is prime and \(\ell\ge1\).

First, if we also assume \(n=r^a\) is a composite prime power, then
\(a\ge2\), and from (3)

\[
r^{a-1}=A(n)=A(N)=q^{\ell-1}. \tag{8}
\]

If \(\ell=1\), the right-hand side is \(1\) while the left-hand side is
\(r^{a-1}>1\), a contradiction. If \(\ell\ge2\), unique factorization
gives \(r=q,a=\ell\), hence \(n=N\), contradicting \(N=n+12\).

Therefore \(n\) has at least two distinct prime factors, and by (7),

\[
Q(n)>n. \tag{9}
\]

Meanwhile, for \(N=q^\ell\),

\[
A(N)=q^{\ell-1},
\qquad
B(N)=1+q+\cdots+q^{\ell-1},
\]

\[
T(N)=\frac{q^{\ell-1}-1}{q-1},
\qquad Q(N)=q^{\ell-1}.
\]

If \(\ell=1\) then \(T(N)=0\), and if \(\ell\ge2\) then
\(T(N)=1+q+\cdots+q^{\ell-2}\). Substituting into (5),

\[
Q(n)=q^{\ell-1}+12\frac{q^{\ell-1}-1}{q-1}. \tag{10}
\]

Since \(n=q^\ell-12\),

\[
\boxed{
(q-1)(Q(n)-n)
=q^{\ell-1}\bigl(12-(q-1)^2\bigr)+12(q-2).
} \tag{11}
\]

By (9), the left-hand side of (11) must be positive.

## Excluding every prime \(q\)

### Case 1: \(\ell=1\)

\(N=q=n+12\ge16\) and \(q\) is prime, so \(q\ge17\). The right-hand
side of (11) is

\[
12-(q-1)^2+12(q-2)=-(q-1)(q-13)<0,
\]

a contradiction. From now on assume \(\ell\ge2\).

### Case 2: \(q\ge7\)

Since \(12-(q-1)^2<0\) and \(q^{\ell-1}\ge q\), the right-hand side of
(11) satisfies

\[
\begin{aligned}
&q^{\ell-1}\bigl(12-(q-1)^2\bigr)+12(q-2)\\
&\le q\bigl(12-(q-1)^2\bigr)+12(q-2)\\
&=-(q-1)(q^2-q-24)<0.
\end{aligned}
\]

This contradicts the positivity of the left-hand side.

### Case 3: \(q=5\)

If \(\ell=2\), then \(n=5^2-12=13\), contradicting the compositeness
assumption. If \(\ell\ge3\), the right-hand side of (11) is

\[
-4\cdot5^{\ell-1}+36<0,
\]

a contradiction.

### Case 4: \(q=3\)

Since \(n=3^\ell-12\ge4\), we have \(\ell\ge3\). Set

\[
m:=3^{\ell-1}-4.
\]

Then

\[
n=3m,\qquad\gcd(3,m)=1,\qquad m\ge5,
\]

and \(m\) is odd. The totient equation (1) gives

\[
\varphi(n)=\varphi(3^\ell)-12=2\cdot3^{\ell-1}-12.
\]

On the other hand, since \(\gcd(3,m)=1\),

\[
\varphi(n)=\varphi(3)\varphi(m)=2\varphi(m).
\]

Therefore

\[
\varphi(m)=3^{\ell-1}-6=m-2,
\]

that is,

\[
m-\varphi(m)=2. \tag{12}
\]

If \(m\) is prime, then \(m-\varphi(m)=1\), a contradiction. If \(m\)
is composite, let \(p\) be its smallest prime factor; then
\(p\ge3,p\le\sqrt m\), and counting only the multiples of \(p\) among
\(1,\ldots,m\) already gives

\[
m-\varphi(m)\ge\frac mp\ge p\ge3,
\]

again contradicting (12).

### Case 5: \(q=2\)

Since \(2^\ell-12\ge4\), we have \(\ell\ge4\). If \(\ell=4\), then
\(n=4\), which is a composite prime power excluded above.

Now assume \(\ell\ge5\). From the divisor-sum equation (2),

\[
\sigma(n)=\sigma(2^\ell)-12=2^{\ell+1}-13,
\]

so \(\sigma(n)\) is odd.

Here we verify a standard auxiliary fact directly. In
\(m=\prod p^e\), for an odd prime \(p\), the parity of

\[
\sigma(p^e)=1+p+\cdots+p^e
\]

equals the parity of \(e+1\), so it is odd if and only if \(e\) is
even. The divisor sum of \(2^e\) is always odd. Therefore

\[
\sigma(m)\text{ is odd}
\iff m\text{ is a square or twice a square}. \tag{13}
\]

However,

\[
n=2^\ell-12=4(2^{\ell-2}-3),
\qquad v_2(n)=2.
\]

Twice a square has odd 2-adic valuation, so \(n\) must be a square.
Hence \(2^{\ell-2}-3\) must also be an odd square. But since
\(\ell\ge5\),

\[
2^{\ell-2}-3\equiv-3\equiv5\pmod8,
\]

whereas an odd square is \(1\pmod8\). Contradiction.

Every prime \(q\) has been excluded, so the theorem is proved.
