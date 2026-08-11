**English** | [한국어](PROOF.ko.md)

# OEIS A340881 — Detailed proof of the modular periodicity

This document is the canonical proof, consolidating on a per-problem basis
the detailed proof written on 2026-08-11 and the subsequent mathematical
audit. The finite computational certificate does not replace the proof; its
only role is to independently re-check the definitions, boundaries, and
derived identities.

Below, "period \(T\)" means that \(T\) is a period; unless minimality is
shown separately, it does not mean that the minimal period is exactly
\(T\). The empty product is defined to be \(1\).

## 1.1. Definition

For \(n\ge1\), define

\[
A(n)=\sum_{k=0}^{n-1}
2^{E(k)}
\prod_{j=k+1}^{n-1}(2^j-1),
\qquad
E(k):=\frac{k(k+1)}2.
\tag{1.1}
\]

For example, at \(n=1\) the product appearing in the sum's only term
\(k=0\) is the empty product, so

\[
A(1)=2^{E(0)}=1.
\]

The statements to be proved are the following two.

1. For a prime \(p\), \(A(n)\bmod p\) is periodic from \(n=1\), and the
   minimal period divides \(2(p-1)\).
2. For every integer \(m\ge2\), \(A(n)\bmod m\) is eventually periodic.

In fact, for odd moduli we obtain a stronger explicit period.

## 1.2. Pure period for odd moduli

Fix an odd \(m>1\). Since \(2\) is an element of
\((\mathbb Z/m\mathbb Z)^\times\), the multiplicative order

\[
L=\operatorname{ord}_m(2)
\]

is defined. That is, \(L\) is the smallest positive integer satisfying

\[
2^L\equiv1\pmod m.
\]

**Lemma 1.1.** For all \(n\ge1\),

\[
A(n+2L)\equiv A(n)\pmod m
\tag{1.2}
\]

holds.

**Proof.** Set \(T=2L\). From the definition,

\[
A(n+T)=
\sum_{k=0}^{n+T-1}
2^{E(k)}
\prod_{j=k+1}^{n+T-1}(2^j-1).
\]

Split this sum into the part with \(0\le k<T\) and the part with
\(T\le k\le n+T-1\).

First suppose \(0\le k<T\). Then \(k+1\le T\), and since \(n\ge1\), we
have \(T\le n+T-1\). Therefore the index range of the product,

\[
k+1\le j\le n+T-1,
\]

necessarily contains \(j=T\). But

\[
2^T-1=2^{2L}-1\equiv1-1=0\pmod m,
\]

so every term of this part is \(0\) modulo \(m\).

Now consider the terms with \(T\le k\le n+T-1\). Substituting
\(k=\ell+T\) gives exactly \(0\le\ell\le n-1\). Substituting \(j=r+T\)
inside the product,

\[
k+1\le j\le n+T-1
\quad\Longleftrightarrow\quad
\ell+1\le r\le n-1.
\]

Each factor is

\[
2^{r+T}-1=2^r2^T-1\equiv2^r-1\pmod m.
\tag{1.3}
\]

Comparing the exponents of the powers of 2 in front as well,

\[
\begin{aligned}
E(\ell+T)-E(\ell)
&=\frac{(\ell+T)(\ell+T+1)-\ell(\ell+1)}2\\
&=\ell T+\frac{T(T+1)}2\\
&=2L\ell+L(2L+1)\\
&=L(2\ell+2L+1).
\end{aligned}
\tag{1.4}
\]

Therefore the exponent difference is a multiple of \(L\), and

\[
\begin{aligned}
2^{E(\ell+T)}
&=2^{E(\ell)}(2^L)^{2\ell+2L+1}\\
&\equiv2^{E(\ell)}\pmod m.
\end{aligned}
\tag{1.5}
\]

Combining (1.3) and (1.5), the term with \(k=\ell+T\) is congruent to the
\(\ell\)-th term of \(A(n)\). Therefore

\[
\begin{aligned}
A(n+T)
&\equiv
\sum_{\ell=0}^{n-1}
2^{E(\ell)}
\prod_{r=\ell+1}^{n-1}(2^r-1)\\
&=A(n)\pmod m.
\end{aligned}
\]

The same computation holds at \(n=1\) as well. Any empty product that may
appear there is \(1\) by definition, so there is no exception. \(\square\)

Therefore, for odd \(m>1\), \(2\operatorname{ord}_m(2)\) is a period of
\(A(n)\bmod m\) starting from the beginning.

## 1.3. The fact that the minimal period divides any period

**Lemma 1.2.** Suppose \(x_1,x_2,\ldots\) is periodic from the first term
with minimal positive period \(d\). If \(T\) is another positive period of
this sequence, then \(d\mid T\).

**Proof.** By Euclidean division, write

\[
T=qd+r,\qquad0\le r<d.
\]

Since \(d\) is a period, \(qd\) is also a period, and

\[
x_{n+qd+r}=x_{n+r}.
\]

On the other hand, since \(T\) is also a period,

\[
x_{n+qd+r}=x_{n+T}=x_n.
\]

Therefore \(x_{n+r}=x_n\) holds for all \(n\ge1\).
If \(r>0\), then \(r\) would be a positive period smaller than \(d\),
contradicting minimality. Therefore \(r=0\), i.e. \(d\mid T\). \(\square\)

## 1.4. Conclusion for prime moduli

**Theorem 1.3.** For a prime \(p\), \(A(n)\bmod p\) is periodic from the
beginning, and the minimal period divides \(2(p-1)\).

**Proof.** First suppose \(p\) is odd.
Setting \(L=\operatorname{ord}_p(2)\), Lagrange's theorem gives

\[
L\mid p-1.
\]

By Lemma 1.1, \(2L\) is a period. Letting \(d\) be the minimal period,
Lemma 1.2 gives

\[
d\mid2L.
\]

Also, since \(L\mid p-1\), we have \(2L\mid2(p-1)\), and therefore

\[
d\mid2(p-1).
\]

In the case \(p=2\), for \(k\ge1\) we have \(E(k)\ge1\), so
\(2^{E(k)}\) is even. The term with \(k=0\) is

\[
\prod_{j=1}^{n-1}(2^j-1),
\]

and every factor is odd. At \(n=1\) it is the empty product \(1\).
Therefore exactly the term with \(k=0\) is odd, and

\[
A(n)\equiv1\pmod2
\]

holds for all \(n\ge1\). In this case the minimal period is \(1\), and
\(1\mid2(p-1)=2\). \(\square\)

## 1.5. First-order recurrence

**Lemma 1.4.** For all \(n\ge1\),

\[
A(n+1)=(2^n-1)A(n)+2^{E(n)}.
\tag{1.6}
\]

**Proof.** From the definition,

\[
A(n+1)=
\sum_{k=0}^{n}
2^{E(k)}
\prod_{j=k+1}^{n}(2^j-1).
\]

In the terms with \(0\le k\le n-1\), the last factor of the product can be
separated.

\[
\prod_{j=k+1}^{n}(2^j-1)
=(2^n-1)\prod_{j=k+1}^{n-1}(2^j-1).
\]

Therefore the sum of these terms is \((2^n-1)A(n)\). The product of the
remaining term \(k=n\) is the empty product, so its value is
\(2^{E(n)}\). Adding the two parts gives (1.6). \(\square\)

## 1.6. Power-of-two moduli

**Lemma 1.5.** If \(e\ge1\), then for all \(n\ge e\),

\[
A(n+1)\equiv-A(n)\pmod{2^e},
\tag{1.7}
\]

and therefore

\[
A(n+2)\equiv A(n)\pmod{2^e}.
\tag{1.8}
\]

**Proof.** If \(n\ge e\), then

\[
2^n-1\equiv-1\pmod{2^e}.
\]

Also, for \(n\ge1\),

\[
E(n)=\frac{n(n+1)}2\ge n\ge e,
\]

so \(2^{E(n)}\equiv0\pmod{2^e}\). Substituting these into (1.6) gives
(1.7). Applying the same identity again at \(n+1\),

\[
A(n+2)\equiv-A(n+1)\equiv A(n)\pmod{2^e},
\]

i.e. (1.8). Therefore the sequence modulo \(2^e\) has period \(2\) at the
latest from \(n=e\). This is not a claim that this period is minimal. For
example, at \(e=1\) the sequence is constant, so the minimal period is
\(1\). \(\square\)

## 1.7. Eventual period for all moduli

**Theorem 1.6.** For every integer \(m\ge2\), \(A(n)\bmod m\) is
eventually periodic.

More concretely, writing

\[
m=2^e u,\qquad e\ge0,\qquad u\text{ odd},
\]

the following holds.

- If \(u>1\), then
  \[
  T=2\operatorname{ord}_u(2)
  \]
  is a period for \(n\ge\max(1,e)\).
- If \(u=1\), i.e. \(m=2^e\), then \(T=2\) is a period for
  \(n\ge e\).

**Proof.** First suppose \(u>1\) and set

\[
L=\operatorname{ord}_u(2),\qquad T=2L.
\]

By Lemma 1.1,

\[
A(n+T)\equiv A(n)\pmod u
\]

holds for all \(n\ge1\).

If \(e=0\), then \(m=u\), so this finishes the proof. If \(e\ge1\),
repeatedly applying Lemma 1.5 gives, for \(n\ge e\), \(r\ge0\),

\[
A(n+r)\equiv(-1)^rA(n)\pmod{2^e}.
\]

Since \(T=2L\) is even,

\[
A(n+T)\equiv A(n)\pmod{2^e}.
\]

Therefore both congruences hold simultaneously for \(n\ge\max(1,e)\).
Since \(\gcd(2^e,u)=1\), the Chinese remainder theorem gives

\[
A(n+T)\equiv A(n)\pmod{2^eu}=\pmod m.
\]

If \(u=1\), then \(m=2^e\), and since \(m\ge2\), we have \(e\ge1\).
In this case Lemma 1.5 directly gives period \(2\) for \(n\ge e\).
\(\square\)
