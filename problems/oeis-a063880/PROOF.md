**English** | [한국어](PROOF.ko.md)

# OEIS A063880: the case of a powerful core with at most two primes

## Definitions and theorem

Define the unitary divisor sum by

\[
\sigma^*(n)
:=\sum_{\substack{d\mid n\\\gcd(d,n/d)=1}}d
=\prod_{p^e\parallel n}(1+p^e)
\]

The equation to be treated is

\[
\sigma(n)=2\sigma^*(n). \tag{1}
\]

For \(n=\prod_p p^{e_p}\), let

\[
C(n):=\prod_{e_p\ge2}p^{e_p}
\]

be the powerful core of \(n\). A solution \(n\) of (1) is
**primitive** if there is no positive proper divisor \(d<n\) satisfying
(1).

**Theorem.** If \(n\) satisfies (1) and \(\omega(C(n))\le2\), then

\[
C(n)=108=2^2\cdot3^3.
\]

Hence the solutions in this subfamily are exactly

\[
\boxed{n=108s,\qquad s\ge1\text{ squarefree},\qquad\gcd(s,108)=1.} \tag{2}
\]

In this subfamily the unique primitive solution is \(108\), and every
solution satisfies \(n\equiv108\pmod{216}\).

## Reduction to the powerful core

Define the local ratio

\[
R(p,e):=\frac{\sigma(p^e)}{\sigma^*(p^e)}
=\frac{1+p+\cdots+p^e}{1+p^e}
\]

By multiplicativity,

\[
\frac{\sigma(n)}{\sigma^*(n)}
=\prod_{p^e\parallel n}R(p,e). \tag{3}
\]

\[
R(p,1)=\frac{1+p}{1+p}=1.
\]

Hence primes with exponent 1 do not affect the value of (3), and

\[
n\text{ satisfies (1)}\iff C(n)\text{ satisfies (1)}. \tag{4}
\]

If \(e\ge2\), then \(R(p,e)>1\) and

\[
R(p,e)
=\frac{p^{e+1}-1}{(p-1)(p^e+1)}
<\frac p{p-1}, \tag{5}
\]

because \(p^{e+1}-1<p(p^e+1)\).

If the core contains no prime, the ratio is \(1\); if it contains one
prime, then

\[
R(p,e)<\frac p{p-1}\le2
\]

so the ratio cannot be exactly \(2\). If the core contains only two
distinct odd primes \(p<q\), then \(p\ge3,q\ge5\), so

\[
R(p,a)R(q,b)
<\frac p{p-1}\frac q{q-1}
\le\frac32\cdot\frac54=\frac{15}{8}<2.
\]

Hence the only remaining shape is

\[
C=2^a q^b,
\qquad q\text{ odd prime},
\qquad a,b\ge2. \tag{6}
\]

## Complete classification of two-prime cores

Setting

\[
x:=2^a
\]

we have

\[
R(2,a)=\frac{2x-1}{x+1},
\qquad
R(q,b)=\frac{q^{b+1}-1}{(q-1)(q^b+1)}.
\]

Clearing denominators in \(R(2,a)R(q,b)=2\),

\[
(2x-1)(q^{b+1}-1)
=2(x+1)(q-1)(q^b+1). \tag{7}
\]

Expanding and rearranging,

\[
2xq(q^{b-1}-1)
=3q^{b+1}-2q^b+2q-3. \tag{8}
\]

Taking (8) modulo \(q\), the left-hand side is \(0\) and the right-hand
side is \(-3\), so \(q\mid3\). Since \(q\) is an odd prime,

\[
q=3.
\]

Substituting \(q=3\) into (8) and dividing by 3,

\[
2x(3^{b-1}-1)=7\cdot3^{b-1}+1.
\]

Substituting \(x=2^a\) back in and rearranging,

\[
(2^{a+1}-7)3^{b-1}=2^{a+1}+1,
\]

that is,

\[
(2^{a+1}-7)(3^{b-1}-1)=8. \tag{9}
\]

Since \(a\ge2\), \(2^{a+1}-7\) is a positive odd number. By (9) this
number must be a positive odd divisor of 8, so

\[
2^{a+1}-7=1,
\]

hence \(a=2\). Substituting back into (9), \(3^{b-1}-1=8\), hence
\(b=3\). Consequently only

\[
C=2^2\cdot3^3=108
\]

is possible.

Indeed,

\[
\sigma(108)=\sigma(2^2)\sigma(3^3)=7\cdot40=280,
\]

\[
\sigma^*(108)=5\cdot28=140,
\]

so \(108\) is a solution of (1).

## Recovering all solutions and the primitive property

If \(C(n)=108\), the exponents of \(2,3\) are exactly \(2,3\)
respectively, and the exponents of all other primes are \(1\). Hence

\[
n=108s,
\]

where \(s\ge1\) is squarefree and \(\gcd(s,108)=1\). Conversely, for
such \(s\), every newly attached prime has exponent \(1\), so its local
ratio is \(1\). Therefore

\[
\frac{\sigma(108s)}{\sigma^*(108s)}
=\frac{\sigma(108)}{\sigma^*(108)}=2.
\]

If \(s>1\), then \(108\) is a proper divisor of \(108s\) that is a
solution, so \(108s\) is not primitive.

On the other hand, suppose a proper divisor \(d<108\) with \(d\mid108\)
were a solution. Automatically \(\omega(C(d))\le2\), and by the first
part of the theorem we would need \(C(d)=108\), hence \(108\mid d\),
contradicting \(d<108\). Therefore \(108\) is primitive.

Finally, if \(\gcd(s,108)=1\), then \(s\) is odd, so

\[
108s-108=108(s-1)
\]

is a multiple of \(216\). Therefore

\[
108s\equiv108\pmod{216}.
\]

Consequently, if a hypothetical additional primitive solution exists,
its powerful core must contain at least three distinct primes.
