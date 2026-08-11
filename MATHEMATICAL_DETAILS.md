**English** | [한국어](MATHEMATICAL_DETAILS.ko.md)

# Mathematical Details of the Open-Problem Research Results

This document collects only the **definitions, lemmas, proofs, exact finite
propositions, and remaining cases** of the five problems addressed in this
work. Execution commands, software installation instructions, file hashes, and
performance records are excluded. However, in the parts that require
congruences of enormous integers or large-scale finite enumerations, we record
separately exactly which arithmetic propositions were verified and how they
imply the conclusions.

## Logical Status of the Results

| Problem | This result | Status |
|---|---|---|
| OEIS A354747 | \(a(100943)=39101\) | This particular unknown term is completely determined |
| OEIS A076141 | No repeated occurrences for \(0<n<2^{40}\) | Rigorous finite-range theorem; the infinite conjecture remains open |
| OEIS A000224 | Classified even numbers, odd primes, odd composite prime powers, and products of two distinct odd primes | Partial theorem; the full conjecture remains open |
| OEIS A245211 | Strong necessary conditions and complete exclusion of several infinite families | Partial theorem; the full conjecture remains open |
| OEIS A395412 | Non-vanishing witnesses obtained for \(85\le n\le200\) | Rigorous finite-range theorem; the infinite conjecture remains open |

---

# 1. OEIS A354747: \(a(100943)=39101\)

## 1.1. Closed Form of the Recurrence

Let the initial value and the recurrence be

\[
x_0=2n-1,\qquad x_{m+1}=3x_m+2
\]

Setting \(y_m=x_m+1\) gives

\[
y_{m+1}=3y_m,\qquad y_0=2n
\]

so

\[
\boxed{x_m=2n3^m-1}.
\]

Therefore, for \(n=100943\), the numbers to be examined are

\[
T_m=201886\cdot3^m-1
\]

The proposition to be proved is that

\[
T_{39101}\text{ is prime},\qquad
T_m\text{ is composite for all }1\le m<39101
\]

## 1.2. The Prime Candidate and the Lucas Sequence

We set the following.

\[
N=T_{39101}=201886\cdot3^{39101}-1,
\]

\[
A=N+1=2\cdot100943\cdot3^{39101}.
\]

Since \(\sqrt{100943}<318\) and trial division by every prime up to 317
yields no divisor, \(100943\) is prime. Therefore

\[
\boxed{A=2^1\,3^{39101}\,100943^1}
\]

is the complete prime factorization of \(A\).

We define the Lucas sequence by

\[
U_0=0,\qquad U_1=1,\qquad
U_{k+2}=8U_{k+1}-5U_k
\]

The parameters are \((P,Q)=(8,5)\), and the discriminant is

\[
\Delta=P^2-4Q=44
\]

## 1.3. Lucas Rank Lemma

**Lemma.** Suppose an odd prime \(\ell\) does not divide \(2Q\Delta\).
If \(z_\ell\) denotes the smallest positive integer \(k\) such that
\(\ell\mid U_k\), then

\[
\boxed{z_\ell\mid \ell-\left(\frac{\Delta}{\ell}\right)}.
\]

Here the parenthesized symbol is the Legendre symbol. In particular,
\(z_\ell\le\ell+1\).

**Proof.** Let \(\alpha,\beta\) be the two roots in
\(\mathbb F_{\ell^2}\) of the polynomial

\[
X^2-PX+Q
\]

Since \(\ell\nmid Q\Delta\), the two roots are distinct and nonzero. In the
Binet formula

\[
U_k=\frac{\alpha^k-\beta^k}{\alpha-\beta}
\]

setting \(\gamma=\alpha/\beta\) gives

\[
U_k\equiv0\pmod\ell
\quad\Longleftrightarrow\quad
\gamma^k=1.
\]

Therefore \(z_\ell\) is the multiplicative order of \(\gamma\) in the finite
group \(\mathbb F_{\ell^2}^{\times}\).

- If \(\left(\frac{\Delta}{\ell}\right)=1\), both roots lie in
  \(\mathbb F_\ell\), so \(\gamma^{\ell-1}=1\).
- If \(\left(\frac{\Delta}{\ell}\right)=-1\), the Frobenius map swaps the
  two roots, so

  \[
  \gamma^\ell=\frac{\beta}{\alpha}=\gamma^{-1},
  \]

  and therefore \(\gamma^{\ell+1}=1\).

Combining the two cases yields the claimed divisibility relation. \(\square\)

## 1.4. Deterministic Primality Certification

The following relations were verified by exact integer modular arithmetic.

\[
\gcd(2Q\Delta,N)=1,
\]

\[
U_A\equiv0\pmod N,
\]

\[
\gcd(U_{A/2},N)=
\gcd(U_{A/3},N)=
\gcd(U_{A/100943},N)=1.
\tag{A354-1}
\]

Let us see why these four Lucas relations prove the primality of \(N\). Let
\(\ell\) be an arbitrary prime factor of \(N\). From
\(U_A\equiv0\pmod N\) we have \(\ell\mid U_A\), so

\[
z_\ell\mid A.
\]

On the other hand, because of the gcd conditions,

\[
z_\ell\nmid A/2,\qquad
z_\ell\nmid A/3,\qquad
z_\ell\nmid A/100943.
\]

For a divisor \(z_\ell\) of \(A=2^1 3^{39101}100943^1\) to satisfy all three
conditions above, it must carry the exponents of 2, 3, and 100943 exactly as
in \(A\). That is,

\[
z_\ell=A=N+1.
\]

Applying the Lucas rank lemma,

\[
N+1=z_\ell
\mid \ell-\left(\frac{44}{\ell}\right),
\]

so \(N+1\le\ell+1\), i.e., \(\ell\ge N\). But a prime with \(\ell\mid N\)
always satisfies \(\ell\le N\), so \(\ell=N\). Since an arbitrary prime
factor of \(N\) is \(N\) itself,

\[
\boxed{N=201886\cdot3^{39101}-1\text{ is prime}.}
\]

This is not a pseudoprime test saying that \(N\) is likely prime, but a
deterministic proof applying the rank argument above to every possible prime
factor of \(N\).

### Identities for Computing Congruences at Enormous Indices

Defining the companion Lucas sequence by

\[
V_0=2,\qquad V_1=P,\qquad
V_{k+2}=PV_{k+1}-QV_k
\]

the identities

\[
U_{2k}=U_kV_k,
\]

\[
U_{3k}=U_k\bigl(V_k^2-Q^k\bigr),
\]

\[
V_{3k}=V_k\bigl(V_k^2-3Q^k\bigr)
\]

hold. First, the state at index \(100943\) can be computed exactly using the
general Lucas addition formulas or binary exponentiation of the companion
matrix

\[
\begin{pmatrix}P&-Q\\1&0\end{pmatrix}
\]

From that state, applying the tripling formulas above 39,101 times and using
the doubling formula at the end yields the values needed for \(A\),
\(A/2\), and \(A/3\). For \(A/100943\), one starts the same
tripling-and-doubling procedure from index 1. Since only the residues of all
values modulo \(N\) are kept, (A354-1) is an exact statement inside the
finite ring \(\mathbb Z/N\mathbb Z\) that does not depend on approximations
of enormous Lucas integers.

## 1.5. Proof That \(39101\) Is the First Index

Primality alone tells us only \(a(100943)\le39101\), not
\(a(100943)=39101\). Therefore all of

\[
T_m=201886\cdot3^m-1,\qquad 1\le m\le39100
\]

must be excluded.

### Exclusion by Small Prime Factors

For each prime \(p\le10^6\), considering

\[
r_m\equiv201886\cdot3^m\pmod p
\]

we have

\[
r_{m+1}\equiv3r_m\pmod p.
\]

Therefore every \(m\) can be examined without omission using only a finite
recurrence. If \(r_m=1\), then

\[
p\mid T_m.
\]

For \(m\ge2\), \(T_m>10^6\), so this \(p\) is a proper divisor. The case
\(m=1\) is handled separately:

\[
T_1=605657=13\cdot46589
\]

This exact sieve provided proper divisors for 37,482 of the 39,100 indices
and left 1,618.

### Fermat Compositeness Witnesses for the Remaining Terms

Each remaining \(T_m\) is odd, so \(\gcd(2,T_m)=1\). If \(T_m\) were
prime, then by Fermat's little theorem it would necessarily satisfy

\[
2^{T_m-1}\equiv1\pmod{T_m}
\]

However, exact modular exponentiation for each of the 1,618 remaining terms
verified that

\[
\boxed{2^{T_m-1}\not\equiv1\pmod{T_m}}
\]

Since this is the failure of a necessary condition, it is a deterministic
witness that each \(T_m\) is composite. The terms eliminated by small prime
factors and these 1,618 terms exactly partition \(1\le m\le39100\), so
there is no smaller prime term.

Consequently,

\[
\boxed{a(100943)=39101}.
\]

---

# 2. OEIS A076141: Complete Binary-Geometry Reduction for \(n<2^{40}\)

## 2.1. Definition and the Finite-Range Theorem

Let \(L\) be the length of the standard binary representation of a positive
integer \(n\).

\[
2^{L-1}\le n<2^L.
\]

Define the integer obtained by shifting a window of length \(L\) upward by
\(u\) places from the least significant bit of \(n^2\) as

\[
W_u(n^2;L)=
\left\lfloor\frac{n^2}{2^u}\right\rfloor\bmod2^L
\]

A076141 counts the number of positions \(u\) with \(W_u(n^2;L)=n\).
Overlapping occurrences are also allowed.

The finite proposition proved in this work is

\[
\boxed{
1\le n<2^{40}
\Longrightarrow
\#\{u:W_u(n^2;L)=n\}\le1
}
\tag{A076-1}
\]

## 2.2. Bit Length of the Square and Occurrences at the Two Ends

Let \(M\) be the bit length of \(n^2\). Then

\[
2^{2L-2}\le n^2<2^{2L}
\]

so

\[
M=2L-\varepsilon,\qquad\varepsilon\in\{0,1\}.
\]

### The Lowest Window

An occurrence at position 0 means

\[
n^2\equiv n\pmod{2^L},
\]

i.e., \(2^L\mid n(n-1)\). Two consecutive integers are coprime, and exactly
one of them is even.

- If \(n\) is even, we would need \(2^L\mid n\), contradicting
  \(0<n<2^L\).
- If \(n\) is odd, then \(2^L\mid n-1\), so \(n=1\).

The word of \(n=1\) appears only once in \(n^2=1\). Therefore an occurrence
in a counterexample cannot be the lowest window.

### The Highest Window

Let \(t=M-L\) be the starting position of the highest window. If this window
equals \(n\), then

\[
n2^t\le n^2<(n+1)2^t,
\]

so

\[
2^t\le n<2^t+\frac{2^t}{n}.
\]

If \(M=2L\), then \(t=L\), which yields the contradiction \(n\ge2^L\).
If \(M=2L-1\), then \(t=L-1\) and \(n\ge2^t\), so

\[
2^t\le n<2^t+1.
\]

Therefore \(n=2^{L-1}\). In this case \(n^2=2^{2L-2}\) has only one bit
equal to 1, so the word \(10\cdots0\) likewise appears only once, in the
highest window. Therefore, if there is a number with two or more occurrences,
all of its occurrences are internal.

## 2.3. The Geometry of Two Internal Occurrences

Take the starting positions of two distinct occurrences to be

\[
s<s+d
\]

Since neither is the lowest or the highest window, \(s\ge1\), and the length
of the prefix remaining above the second window,

\[
p=M-(s+d+L)
\]

also satisfies \(p\ge1\).

Let the overlap length of the two windows be

\[
r=L-d
\]

Since the two windows and the nonempty parts at both ends all lie within
\(M\le2L\) bits, \(1\le r<L\). Counting bits,

\[
M=p+(L+d)+s.
\]

Substituting \(M=2L-\varepsilon\) and \(r=L-d\),

\[
\boxed{p+s=r-\varepsilon}.
\tag{A076-2}
\]

Therefore the enumeration range is exactly

\[
r\ge\varepsilon+2,\qquad
1\le s\le r-\varepsilon-1,\qquad
p=r-\varepsilon-s
\]

## 2.4. The Period Forced by the Overlap

Writing the binary bits of \(n\) from the most significant as
\(w_0w_1\cdots w_{L-1}\), the overlap of the two identical windows gives

\[
w_i=w_{i+d},\qquad 0\le i<r=L-d.
\]

That is, the word has period \(d\) on the overlapping interval. Letting
\(q\) denote the common \(r\)-bit integer,

\[
\boxed{
q=\left\lfloor\frac n{2^d}\right\rfloor
=n\bmod2^r
}.
\tag{A076-3}
\]

The first expression means that \(q\) is the top \(r\) bits of \(n\); the
second means that the same \(q\) is the bottom \(r\) bits. In particular,

\[
q2^d\le n\le(q+1)2^d-1.
\tag{A076-4}
\]

The possible \(q\) are completely parameterized as follows.

- If \(r\le d\), take every \(r\)-bit word whose leading bit is 1.
- If \(r>d\), repeat periodically every \(d\)-bit seed whose leading bit
  is 1 and take its first \(r\) bits.

Therefore, for each \((L,r,d)\), the number of \(q\) candidates is

\[
2^{\min(r,d)-1}
\]

## 2.5. Reduction to a Quadratic Equation

Define the following.

\[
E=L+d+s.
\]

Let \(A\) be the most significant \(p\)-bit prefix of \(n^2\) and \(B\)
the least significant \(s\)-bit suffix. Then

\[
A=\left\lfloor\frac{n^2}{2^E}\right\rfloor,
\qquad
B=n^2\bmod2^s.
\]

Since \(A\) has exactly \(p\) bits,

\[
2^{p-1}\le A\le2^p-1.
\]

Moreover, since \(s<r\) and \(n\equiv q\pmod{2^r}\),

\[
\boxed{B=q^2\bmod2^s}.
\tag{A076-5}
\]

Adding the two occurrences as \(n2^s\) and \(n2^{s+d}\), the common \(r\)
bits \(q\) enter twice at position \(s+d\). Subtracting this once yields the
exact place-value decomposition

\[
n^2=A2^E+n2^s+n2^{s+d}-q2^{s+d}+B
\]

Therefore, setting

\[
C=2^s(2^d+1),
\]

\[
D_0=A2^E-q2^{d+s}+B
\]

we obtain

\[
\boxed{n^2-Cn-D_0=0}.
\tag{A076-6}
\]

Here \(D_0>0\). Indeed, since \(q<2^r\) and \(d\ge1\),

\[
q2^{d+s}<2^{r+d+s}=2^{L+s}<2^{L+d+s}=2^E\le A2^E.
\]

Therefore the only possible positive root is

\[
n=\frac{C+\sqrt{\Delta}}2,
\qquad
\Delta=C^2+4D_0
\]

That is, \(\Delta\) must be a perfect square and the parity of the numerator
must match.

### The Exact Range of \(A\)

Set \(N_-=q2^d\) and \(N_+=(q+1)2^d-1\). By (A076-4) and the
monotonicity of the squaring function,

\[
\left\lfloor\frac{N_-^2}{2^E}\right\rfloor
\le A\le
\left\lfloor\frac{N_+^2}{2^E}\right\rfloor.
\]

Intersecting this with the \(p\)-bit condition on \(A\),

\[
\max\left(
\left\lfloor\frac{N_-^2}{2^E}\right\rfloor,2^{p-1}
\right)
\le A\le
\min\left(
\left\lfloor\frac{N_+^2}{2^E}\right\rfloor,2^p-1
\right).
\tag{A076-7}
\]

This interval contains every actually possible \(A\). Since there may be
surplus candidates, for each recovered root we directly verify again at the
end that

\[
\operatorname{bitlen}(n)=L,
\]

\[
\operatorname{bitlen}(n^2)=2L-\varepsilon,
\]

\[
W_s(n^2;L)=W_{s+d}(n^2;L)=n
\]

## 2.6. Why the Enumeration Is Complete

Suppose a counterexample exists and pick one pair of distinct occurrences.

1. By the exclusion of occurrences at the two ends, \(s,p\ge1\).
2. The bit length of the square uniquely determines
   \(\varepsilon\in\{0,1\}\).
3. The two starting positions determine \(d\) and \(r=L-d\) and satisfy
   (A076-2).
4. The overlap determines \(q\), and this \(q\) is necessarily included in
   the periodic-seed enumeration above.
5. The actual prefix \(A\) is necessarily contained in (A076-7).
6. The quadratic equation for that \((A,q)\) has the original \(n\) as a
   positive integer root.
7. The recovered \(n\) also passes the final two-window checks.

Therefore, if a counterexample exists, it is necessarily detected in at least
one geometry. A counterexample with three or more occurrences may correspond
to several occurrence pairs, so the proposition needed is not the uniqueness
of the geometry but this **coverage**.

## 2.7. Finite Enumeration Results and Exact Ranges

The number of geometries for a fixed \(L\) is

\[
\sum_{r=2}^{L-1}(r-1)+
\sum_{r=3}^{L-1}(r-2)
=(L-2)^2.
\]

Therefore the total number of geometries for \(2\le L\le40\) is

\[
\sum_{k=0}^{38}k^2=19019
\]

In these geometries,

\[
181{,}402{,}314
\]

\(q\) candidates and

\[
99{,}006{,}717
\]

quadratic equations that passed the prefix range were examined exactly. No
number passed all of the perfect-square discriminant, integer-root, bit-length,
and two-window conditions.

If \(L\le40\), then \(n^2<2^{80}\), and in this reduction
\(C<2^{40}\), \(D_0<2^{80}\), and \(\Delta<2^{83}\). Therefore every
quantity used in the enumeration lies within a fixed exact integer range.
This proves (A076-1), but the infinite remaining range \(n\ge2^{40}\) is
still open.

---

# 3. OEIS A000224: Divisibility Conjecture for the Number of Quadratic Residues

## 3.1. Definition and Conjecture

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

## 3.2. A Formula for \(R(p^e)\)

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

## 3.3. Exclusion of All Even Numbers

If \(n\ge2\) is even, then \(n^2-1\) is odd. On the other hand,
\(R(n)\ge2\), and the product of two consecutive integers
\(R(n)(R(n)-1)\) is a positive even number. Hence no even number
satisfies the condition.

## 3.4. Exclusion of All Odd Composite Prime Powers

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

## 3.5. Products of Two Distinct Odd Primes

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

## 3.6. Local Conditions Every Potential Counterexample Must Satisfy

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

## 3.7. Pell-Type Equation

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

## 3.8. Current Scope of the Proof

Thus, the classes for which the absence of composite counterexamples is
completely proven are

1. all even numbers,
2. all odd composite prime powers \(p^e\) \((e\ge2)\),
3. products of two distinct odd primes.

If a counterexample exists, it must be odd, have at least two distinct
prime factors, and satisfy \(\Omega(n)\ge3\). The general \(p^e q^f\)
case and the case of three or more distinct prime factors still remain,
so the full conjecture for A000224 is unresolved.

---

# 4. OEIS A245211: Weighted Proper-Divisor Sum

## 4.1. The Basic Equation

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

## 4.2. A Strong Lower Bound for Each Prime Factor

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

## 4.3. Complete Exclusion of Prime Powers

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

## 4.4. Exact 2-adic Valuation for Odd Inputs

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

## 4.5. Partial Classification of Squarefree Solutions

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

## 4.6. Small Prime Factors \(2,3,5,7,11\)

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

## 4.7. The Case of Exactly Two Distinct Prime Factors

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

## 4.8. Currently Remaining Cases

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

---

# 5. OEIS A395412: nonvanishing of primorial prime candidates

## 5.1. Definition

Let \(p_n\) be the \(n\)-th prime, and let

\[
P_n=\prod_{i=1}^np_i
\]

be the \(n\)-th primorial. The sequence is defined by

\[
a(n)=\#\left\{
d:\ 1\le d<p_n,\ d\text{ is squarefree},\
\frac{P_n}{d}+d\text{ is prime}
\right\}.
\]

The conjecture is that \(a(n)>0\) for all \(n\ge1\).

Every prime factor of a squarefree integer \(d<p_n\) is smaller than \(p_n\), so
\(d\mid P_n\). Hence \(P_n/d\) in the formula above is always an integer.

## 5.2. Lemma on the absence of small prime factors

For an admissible \(d\), set

\[
C_{n,d}=\frac{P_n}{d}+d.
\]

**Lemma.** No prime \(\ell\le p_n\) divides \(C_{n,d}\).

**Proof.** We split into two cases.

- If \(\ell\nmid d\), then the factor \(\ell\) remains in \(P_n/d\), so

  \[
  C_{n,d}\equiv d\not\equiv0\pmod\ell.
  \]

- If \(\ell\mid d\), then since both \(d\) and \(P_n\) are squarefree,
  no factor \(\ell\) remains in \(P_n/d\). Hence

  \[
  C_{n,d}\equiv P_n/d\not\equiv0\pmod\ell.
  \]

Therefore \(\ell\nmid C_{n,d}\). \(\square\)

By this lemma, the least prime factor of a composite candidate is necessarily
larger than \(p_n\). However, this does not mean that a candidate is prime, nor
does it yield the conclusion that a prime candidate exists for every \(n\).

## 5.3. Why a single witness proves nonvanishing

For a fixed \(n\), it suffices to exhibit a single \(d_n\) satisfying the
following three conditions.

\[
d_n<p_n,
\]

\[
d_n\text{ is squarefree},
\]

\[
C_n=\frac{P_n}{d_n}+d_n\text{ is prime}.
\]

Then, by definition, \(d_n\) is an element of the set being counted, so

\[
\boxed{a(n)\ge1}.
\]

That is, there is no need to compute the exact value of \(a(n)\) in full.

## 5.4. Explicit witnesses for \(85\le n\le200\)

For each \((n,d_n)\) in the table below, the conditions \(d_n<p_n\) and
squarefreeness, together with the primality of \(P_n/d_n+d_n\), were verified
by deterministic primality testing. This section is a computer-assisted finite
theorem that uses a deterministic procedure of the APRCL/ECPP family as its
final step. The values \(d_n\) in the table are the mathematical witness data
that uniquely regenerate each enormous integer candidate via the formula
\(P_n/d_n+d_n\); the primality of a candidate does not become self-evident
merely by looking at the small integers in the table. Each row of the table
contains four \((n,d_n)\) pairs.

| \(n\) | \(d_n\) | \(n\) | \(d_n\) | \(n\) | \(d_n\) | \(n\) | \(d_n\) |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 85 | 38 | 86 | 66 | 87 | 58 | 88 | 2 |
| 89 | 46 | 90 | 71 | 91 | 42 | 92 | 103 |
| 93 | 157 | 94 | 74 | 95 | 31 | 96 | 33 |
| 97 | 231 | 98 | 47 | 99 | 66 | 100 | 77 |
| 101 | 110 | 102 | 13 | 103 | 43 | 104 | 77 |
| 105 | 34 | 106 | 11 | 107 | 71 | 108 | 58 |
| 109 | 7 | 110 | 33 | 111 | 23 | 112 | 26 |
| 113 | 10 | 114 | 7 | 115 | 85 | 116 | 74 |
| 117 | 87 | 118 | 65 | 119 | 137 | 120 | 78 |
| 121 | 39 | 122 | 23 | 123 | 133 | 124 | 137 |
| 125 | 159 | 126 | 66 | 127 | 31 | 128 | 93 |
| 129 | 74 | 130 | 149 | 131 | 6 | 132 | 86 |
| 133 | 122 | 134 | 34 | 135 | 110 | 136 | 14 |
| 137 | 46 | 138 | 7 | 139 | 109 | 140 | 82 |
| 141 | 59 | 142 | 86 | 143 | 73 | 144 | 13 |
| 145 | 393 | 146 | 101 | 147 | 103 | 148 | 113 |
| 149 | 142 | 150 | 69 | 151 | 26 | 152 | 105 |
| 153 | 3 | 154 | 85 | 155 | 102 | 156 | 113 |
| 157 | 107 | 158 | 74 | 159 | 23 | 160 | 19 |
| 161 | 187 | 162 | 546 | 163 | 101 | 164 | 190 |
| 165 | 87 | 166 | 158 | 167 | 217 | 168 | 11 |
| 169 | 43 | 170 | 66 | 171 | 1 | 172 | 1 |
| 173 | 19 | 174 | 85 | 175 | 57 | 176 | 15 |
| 177 | 229 | 178 | 113 | 179 | 137 | 180 | 29 |
| 181 | 238 | 182 | 431 | 183 | 94 | 184 | 57 |
| 185 | 35 | 186 | 158 | 187 | 2 | 188 | 638 |
| 189 | 41 | 190 | 2 | 191 | 131 | 192 | 141 |
| 193 | 331 | 194 | 479 | 195 | 41 | 196 | 13 |
| 197 | 102 | 198 | 65 | 199 | 3 | 200 | 82 |

Therefore, as a finite statement,

\[
\boxed{85\le n\le200\Longrightarrow a(n)>0}
\]

is proved. This is a finite proof giving a separate witness for each \(n\); it
is not a single construction of \(d_n\) that works for all \(n\). The infinite
statement for \(n\ge201\) and the full A395412 conjecture remain open.

---

# 6. Overall summary

None of the present results resolves any one of the infinite conjectures in
its entirety. However, the value at \(n=100943\), which was the first unknown
case of A354747, has been completely determined as

\[
a(100943)=39101
\]

by a deterministic primality proof and a complete minimality check. In the
remaining four problems, the following rigorous progress was secured.

- For A076141, the entire range \(n<2^{40}\) was completely reduced via the
  overlap geometry of two occurrences and a quadratic equation, proving that
  there is no counterexample.
- For A000224, it was confirmed that odd primes satisfy the condition, and all
  even numbers, all odd composite prime powers, and products of two distinct
  odd primes were completely excluded from the composite counterexamples.
- For A245211, we obtained a local lower bound on prime factors, the exact
  2-adic valuation, the exclusion of small prime factors, the classification
  of several squarefree infinite families, and a finite reduction per exponent
  pair for two prime factors.
- For A395412, the nonvanishing range was rigorously extended by giving an
  explicit prime witness for each \(n\) with \(85\le n\le200\).

Until the remaining infinite families, recorded separately in each section,
are resolved, one cannot claim that the corresponding OEIS conjectures are
proved in full.
