**English** | [한국어](DETAILS.ko.md)

# OEIS A000224: Divisibility Conjecture for the Number of Quadratic Residues

## 1. Definition and Conjecture

Let \(R(n)\) denote the number of distinct quadratic residues modulo
\(n\), including 0. The conjecture is that for \(n>1\),

\[
\boxed{
R(n)(R(n)-1)\mid n^2-1
\quad\Longleftrightarrow\quad
n\text{ is an odd prime}
}
\tag{A224-1}
\]

## 2. A Formula for \(R(p^e)\)

By the Chinese Remainder Theorem, \(R\) is multiplicative. Now let \(p\)
be an odd prime. The \(p\)-adic exponent of a nonzero quadratic residue
has the form \(2j\). The number of quadratic residues with exponent
\(2j<e\) is

\[
\frac{\varphi(p^{e-2j})}{2}
\]

hence

\[
R(p^e)
=1+\frac12
\sum_{j=0}^{\lfloor(e-1)/2\rfloor}\varphi(p^{e-2j}).
\tag{A224-2}
\]

Summing the geometric series, we obtain, for \(r=R(p^e)\),

\[
\boxed{
2(p+1)r=
\begin{cases}
p^{e+1}+2p+1,&e\text{ odd},\\
p^{e+1}+p+2,&e\text{ even}
\end{cases}}
\tag{A224-3}
\]

This is the same as

\[
R(p^e)=\left\lfloor\frac{p^{e+1}}{2p+2}\right\rfloor+1.
\]

If \(e=1\), then \(R(p)=(p+1)/2\), so

\[
R(p)(R(p)-1)=\frac{p^2-1}{4}.
\]

Hence every odd prime satisfies the divisibility condition of (A224-1),
and the quotient is exactly 4.

Moreover, if the divisibility condition holds, then

\[
\boxed{\gcd\bigl(n,R(n)(R(n)-1)\bigr)=1}
\tag{A224-4}
\]

because a common divisor would have to divide both \(n^2\) and \(n^2-1\).

## 3. Exclusion of All Even Numbers

If \(n\ge2\) is even, then \(n^2-1\) is odd. On the other hand,
\(R(n)\ge2\), and the product of two consecutive integers
\(R(n)(R(n)-1)\) is a positive even number. Hence no even number
satisfies the condition.

## 4. Exclusion of All Odd Composite Prime Powers

Let \(n=p^e\), \(e\ge2\).

### Case: \(e\) even

Reducing (A224-3) modulo \(p\) gives

\[
2r\equiv2\pmod p,
\]

so \(p\mid r-1\). This contradicts (A224-4).

### Case: \(e\) odd

Then \(e\ge3\) and

\[
r-1=\frac{p^{e+1}-1}{2(p+1)}.
\tag{A224-5}
\]

If the divisibility condition holds, then \(r-1\mid p^{2e}-1\). Also,
from (A224-5), \(r-1\mid p^{e+1}-1\), so

\[
r-1\mid
\gcd(p^{2e}-1,p^{e+1}-1).
\]

Using the standard identity \(\gcd(x^a-1,x^b-1)=x^{\gcd(a,b)}-1\) and
\(\gcd(2e,e+1)=2\) for odd \(e\), we get

\[
r-1\mid p^2-1.
\tag{A224-6}
\]

However,

\[
\begin{aligned}
r-1
&=\frac{p^{e+1}-1}{2(p+1)}\\
&\ge\frac{p^4-1}{2(p+1)}\\
&=\frac{(p-1)(p^2+1)}2\\
&>p^2-1,
\end{aligned}
\]

where the last inequality holds because \(p^2-2p-1>0\) for \(p\ge3\).
This contradicts (A224-6), so all odd composite prime powers are also
excluded.

## 5. Products of Two Distinct Odd Primes

Let \(n=pq\) with \(3\le p<q\), and set

\[
a=\frac{p+1}{2},\qquad
b=\frac{q+1}{2},\qquad
R=R(n)=ab.
\]

Assume the divisibility condition holds and set

\[
K=\frac{p^2q^2-1}{R(R-1)}\in\mathbb Z_{>0}.
\]

A direct expansion gives

\[
\begin{aligned}
16R(R-1)-(p^2q^2-1)
={}&2p^2q+2pq^2+p^2+q^2\\
&-2p-2q-2>0.
\end{aligned}
\]

Hence \(K<16\), that is, \(K\le15\). On the other hand,

\[
K-\frac{n^2}{R^2}
=\frac{n^2-R}{R^2(R-1)}>0.
\]

Since \(b>a\),

\[
K>
\left(\frac nR\right)^2
=\left(2-\frac1a\right)^2
 \left(2-\frac1b\right)^2
>\left(2-\frac1a\right)^4.
\]

If \(a\ge32\), then

\[
K>\left(\frac{63}{32}\right)^4>15,
\]

and indeed \(63^4-15\cdot32^4=24321>0\). Therefore

\[
\boxed{a\le31,\qquad p\le61}.
\tag{A224-7}
\]

Also, since \(R=ab\mid n^2-1\) and \(q=2b-1\equiv-1\pmod b\),

\[
\boxed{b\mid p^2-1=4a(a-1)}.
\tag{A224-8}
\]

Hence the set to be checked reduces completely to the following finite
set.

\[
2\le a\le31,\quad p=2a-1\text{ is prime},
\]

\[
b>a,\quad b\mid4a(a-1),\quad q=2b-1\text{ is prime}.
\]

There are 117 pairs satisfying these conditions. Among them, only the
22 cases below also satisfy \(R\mid n^2-1\). The last column is
\((n^2-1)\bmod(R-1)\).

| \(p\) | \(q\) | \(R\) | Remainder |
|---:|---:|---:|---:|
| 3 | 7 | 8 | 6 |
| 5 | 7 | 12 | 3 |
| 5 | 11 | 18 | 15 |
| 5 | 47 | 72 | 57 |
| 7 | 11 | 24 | 17 |
| 7 | 23 | 48 | 23 |
| 11 | 19 | 60 | 20 |
| 11 | 23 | 72 | 37 |
| 11 | 59 | 180 | 13 |
| 13 | 83 | 294 | 151 |
| 19 | 29 | 150 | 87 |
| 19 | 71 | 360 | 29 |
| 19 | 179 | 900 | 266 |
| 23 | 43 | 264 | 23 |
| 23 | 263 | 1584 | 938 |
| 29 | 41 | 315 | 92 |
| 29 | 419 | 3150 | 2786 |
| 31 | 479 | 3840 | 3674 |
| 37 | 683 | 6498 | 825 |
| 41 | 839 | 8820 | 1875 |
| 47 | 367 | 4416 | 1150 |
| 47 | 1103 | 13248 | 4155 |

All remainders are nonzero. Since \(\gcd(R,R-1)=1\), for
\(R(R-1)\mid n^2-1\) to hold, each of the two factors must divide
\(n^2-1\). Hence all products of two distinct odd primes are also
excluded. Only the verification of the last 22 integer remainders
amounts to a finite exhaustive enumeration.

## 6. Local Conditions Every Potential Counterexample Must Satisfy

Let \(p^e\Vert n\), \(m=n/p^e\), \(r_p=R(p^e)\), and set

\[
c_p=
\begin{cases}
2p+1,&e\text{ odd},\\
p+2,&e\text{ even}
\end{cases}
\]

If \(R(n)\mid n^2-1\), then by multiplicativity \(r_p\mid n^2-1\).
From (A224-3),

\[
p^{e+1}\equiv-c_p\pmod{r_p}.
\]

Also \(p^{2e}m^2=n^2\equiv1\pmod{r_p}\). Multiplying the latter
congruence by \(p^2\) and substituting the square of the former yields

\[
\boxed{r_p\mid m^2c_p^2-p^2}.
\tag{A224-9}
\]

The right-hand side is positive, and

\[
r_p>\frac{p^{e+1}}{2(p+1)}
\]

so

\[
\boxed{p^{e+1}<2(p+1)m^2c_p^2}.
\tag{A224-10}
\]

This is a necessary condition that excludes candidates in which one
prime power is excessively large relative to the remaining factor.

## 7. Pell-Type Equation

Writing the divisibility quotient as

\[
K=\frac{n^2-1}{R(n)(R(n)-1)}
\]

and setting

\[
X=2n,\qquad Y=2R(n)-1,
\]

we have

\[
4R(R-1)=Y^2-1,
\]

so the original condition turns exactly into the generalized Pell
equation

\[
\boxed{X^2-KY^2=4-K}
\tag{A224-11}
\]

However, among the integer solutions \((X,Y)\) of this equation, only
those that actually satisfy \(Y=2R(n)-1\) are candidates for the
original problem.

In particular, if \(K=4\), then \(n=2R(n)-1\), i.e.,
\(R(n)=(n+1)/2\). For an odd prime power \(x=p^e\),

\[
R(x)\le\frac{x+1}{2}
\]

with equality only when \(e=1\). Indeed, when the difference between
(A224-3) and \((p^e+1)/2\) is put over a common denominator, the
numerator is \(p^e-p\) for odd \(e\) and \(p^e-1\) for even \(e\).

Starting from this prime-power inequality, for coprime odd \(u,v>1\),

\[
R(uv)=R(u)R(v)
\le\frac{(u+1)(v+1)}4
<\frac{uv+1}{2}.
\]

The last strict inequality is equivalent to \((u-1)(v-1)>0\). Applying
induction on the number of prime factors, \(R(n)\le(n+1)/2\) for every
odd \(n>1\), with equality only when there is a single prime-power
factor whose exponent is 1. Hence the \(n>1\) with \(K=4\) are exactly
the odd primes.

## 8. Current Scope of the Proof

Thus, the classes for which the absence of composite counterexamples is
completely proven are

1. all even numbers,
2. all odd composite prime powers \(p^e\) \((e\ge2)\),
3. products of two distinct odd primes.

If a counterexample exists, it must be odd, have at least two distinct
prime factors, and satisfy \(\Omega(n)\ge3\). The general \(p^e q^f\)
case and the case of three or more distinct prime factors still remain,
so the full conjecture for A000224 is unresolved.
