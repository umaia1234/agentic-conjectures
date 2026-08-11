**English** | [한국어](PROOF.ko.md)

# OEIS A397245 — Detailed Proof of the mod 3 Coefficient Classification

This document is the canonical proof, consolidated per problem, of the
detailed proof written on 2026-08-11 together with the follow-up
mathematical audit. The finite computational certificate does not
replace the proof; its only role is to independently recheck the
definitions, boundary values, and derived identities.

Below, \([x^n]F(x)\) denotes the coefficient of \(x^n\) in \(F(x)\), and
an empty sum is \(0\). \(\mathbb F_3\) is the finite field with three
elements.

Consider the following formal power series.

\[
A(x)=\sum_{n\ge0}a_nx^n,\qquad a_0=a_1=1,
\]

where \(A\) is defined by

\[
A(x)=\exp\!\left(
x+\sum_{n\ge2}\frac{(4n^2-1)a_n}{4n^2}x^n
\right). \tag{4.1}
\]

The statement to be proved is the following.

\[
a_n\equiv1\pmod3
\]

if and only if, for some \(j\ge0\),

\[
n+2=3^j\quad\text{or}\quad n+2=2\cdot3^j,
\]

and

\[
a_n\equiv2\pmod3
\]

if and only if, for some \(0\le i<j\),

\[
n+2=3^i+3^j.
\]

In all other cases \(a_n\equiv0\pmod3\).

## 4.1. Turning the exponential definition into two differential equations

We first compute in \(\mathbb Q[[x]]\). Since \(A(0)=1\), \(A\) is a
unit and \(\log A\), \(A'/A\) are both formally defined. Set the
following series.

\[
C(x)=\sum_{n\ge1}\frac{a_n}{n}x^n.
\]

Then

\[
C'(x)=\sum_{n\ge1}a_nx^{n-1},
\]

so

\[
xC'(x)=\sum_{n\ge1}a_nx^n=A(x)-1. \tag{4.2}
\]

Now take the formal logarithm of both sides of (4.1) and differentiate.
First,

\[
\log A
=x+\sum_{n\ge2}
 \frac{(4n^2-1)a_n}{4n^2}x^n,
\]

so

\[
\begin{aligned}
\frac{A'}A
&=1+\sum_{n\ge2}
 \frac{(4n^2-1)a_n}{4n}x^{n-1}\\
&=1+\sum_{n\ge2}
 \left(n-\frac1{4n}\right)a_nx^{n-1}\\
&=\left(1+\sum_{n\ge2}na_nx^{n-1}\right)
 -\frac14\sum_{n\ge2}\frac{a_n}{n}x^{n-1}.
\end{aligned}
\]

The first parenthesis is \(A'\) because \(a_1=1\), and the second sum is

\[
\sum_{n\ge2}\frac{a_n}{n}x^{n-1}
=\frac{C-x}{x}.
\]

Therefore

\[
\frac{A'}A=A'-\frac{C-x}{4x}.
\]

Solving this for \(C\) gives

\[
\begin{aligned}
C-x
&=4x\left(A'-\frac{A'}A\right)\\
&=4xA'\left(1-\frac1A\right)\\
&=4x(A-1)\frac{A'}A.
\end{aligned}
\]

That is,

\[
C=x+4x(A-1)\frac{A'}A. \tag{4.3}
\]

Hence (4.1) turns into the following system.

\[
\boxed{
xC'=A-1,\qquad
C=x+4x(A-1)\frac{A'}A.
} \tag{4.4}
\]

The converse also holds. Indeed, rearranging (4.3) again gives

\[
\frac{A'}A=A'-\frac{C-x}{4x}.
\]

Integrating both sides and using \(A(0)=1\), the constant of integration
is 0, and

\[
\begin{aligned}
\log A
&=A-1-\frac14\int\frac{C-x}{x}\,dx\\
&=A-1-\frac14
  \sum_{n\ge2}\frac{a_n}{n^2}x^n\\
&=x+\sum_{n\ge2}
  \left(1-\frac1{4n^2}\right)a_nx^n\\
&=x+\sum_{n\ge2}
  \frac{(4n^2-1)a_n}{4n^2}x^n.
\end{aligned}
\]

Therefore (4.1) and (4.4) are exactly equivalent in \(\mathbb Q[[x]]\).

## 4.2. Integrality of \(a_n/n\) and the triangular recurrence

To reduce mod 3 we need the fact that the coefficients of \(C\) are
integers. Set the following.

\[
c_n=\frac{a_n}{n},\qquad
C(x)=\sum_{n\ge1}c_nx^n.
\]

Comparing the \(x^n\) coefficient of (4.2) gives

\[
a_n=nc_n \qquad(n\ge1). \tag{4.5}
\]

Now clearing the denominator of (4.3) gives

\[
A(C-x)=4x(A-1)A'. \tag{4.6}
\]

For \(n\ge2\) we compute the \(x^n\) coefficient of (4.6). On the left,

\[
\begin{aligned}
[x^n]A(C-x)
&=\sum_{j=1}^{n}c_j a_{n-j}-a_{n-1}\\
&=c_n+\sum_{j=2}^{n-1}c_j a_{n-j}.
\end{aligned}
\]

Here we used \(a_0=1\), \(c_1=a_1=1\). In particular, the term
\(c_1a_{n-1}=a_{n-1}\) arising at \(j=1\) cancels against \(-a_{n-1}\).

On the right,

\[
A-1=\sum_{r\ge1}a_rx^r,\qquad
A'=\sum_{j\ge1}ja_jx^{j-1},
\]

so

\[
\begin{aligned}
[x^n]\,4x(A-1)A'
&=4\sum_{j=1}^{n-1}j\,a_j a_{n-j}\\
&=4\sum_{j=1}^{n-1}j^2c_j a_{n-j}\\
&=4a_{n-1}
  +\sum_{j=2}^{n-1}4j^2c_j a_{n-j}.
\end{aligned}
\]

Therefore

\[
c_n+\sum_{j=2}^{n-1}c_j a_{n-j}
=
4a_{n-1}
+\sum_{j=2}^{n-1}4j^2c_j a_{n-j},
\]

that is,

\[
\boxed{
c_n
=4a_{n-1}
+\sum_{j=2}^{n-1}(4j^2-1)c_j a_{n-j},
\qquad
a_n=nc_n.
} \tag{4.7}
\]

The initial report wrote the same recurrence as

\[
c_n=a_{n-1}
 +\sum_{j=1}^{n-1}(4j^2-1)c_ja_{n-j}.
\tag{4.7a}
\]

The \(j=1\) term is
\((4-1)c_1a_{n-1}=3a_{n-1}\), and since \(c_1=1\), combining it with the
outer \(a_{n-1}\) gives \(4a_{n-1}\). Hence (4.7a) is exactly the same
equation as (4.7). In the detailed derivations below we use (4.7), whose
starting point of summation and triangular structure are clearer, as the
canonical notation.
The generating-function notation of the initial report,
\[
C=xA+(4xA'-C)(A-1),
\]
also becomes, after rearranging both sides, \(AC=xA+4x(A-1)A'\), i.e.
(4.3), so it is the same content.

This recurrence is triangular. On the right-hand side of \(c_n\) only

\[
a_{n-1},\quad c_j\ (j<n),\quad a_{n-j}\ (n-j<n)
\]

appear.

We now apply induction on \(n\). At \(n=1\),

\[
c_1=a_1=1,
\]

which is an integer. Assuming \(c_k,a_k\in\mathbb Z\) for all \(k<n\),
the right-hand side of (4.7) consists entirely of integers, so
\(c_n\in\mathbb Z\). Then

\[
a_n=nc_n,
\]

so \(a_n\in\mathbb Z\). Therefore for all \(n\ge1\),

\[
\boxed{c_n=\frac{a_n}{n}\in\mathbb Z,\qquad a_n\in\mathbb Z.} \tag{4.8}
\]

In particular this argument shows, more strongly than merely that
\(a_n\) is an integer,

\[
n\mid a_n.
\]

Moreover, (4.7) determines the next coefficient uniquely at each step,
so the formal solution of (4.1) is also unique.

## 4.3. Uniqueness of the system over GF(3)

By (4.8), \(A,C\in\mathbb Z[[x]]\). Since \(A(0)=1\), we have
\(A^{-1}\in\mathbb Z[[x]]\), and therefore (4.4) can be reduced
coefficientwise to \(\mathbb F_3\). Below we denote the reduced images
by the same letters \(A,C\). Since \(4\equiv1\pmod3\),

\[
xC'=A-1,\qquad
C=x+x(A-1)\frac{A'}A. \tag{4.9}
\]

We now check that the solution of this system is unique. Write

\[
A=\sum_{n\ge0}\alpha_nx^n,\qquad
C=\sum_{n\ge1}\gamma_nx^n.
\]

From the first equation we obtain

\[
\alpha_n=n\gamma_n\qquad(n\ge1). \tag{4.10}
\]

However, if \(3\mid n\), then (4.10) only says \(\alpha_n=0\) and does
not determine \(\gamma_n\) directly. Hence the first equation alone
cannot give uniqueness, and the second equation is needed.

Reducing (4.7) mod 3, by \(4\equiv1\) and
\(4j^2-1\equiv j^2-1\),

\[
\boxed{
\gamma_n
=\alpha_{n-1}
+\sum_{j=2}^{n-1}(j^2-1)\gamma_j\alpha_{n-j},
\qquad
\alpha_n=n\gamma_n.
} \tag{4.11}
\]

The initial values are

\[
\alpha_0=1,\qquad \alpha_1=\gamma_1=1.
\]

For \(n\ge2\), the right-hand side of the first equation of (4.11)
involves only the already-determined
\(\alpha_0,\ldots,\alpha_{n-1}\) and
\(\gamma_1,\ldots,\gamma_{n-1}\). Hence the first equation determines
\(\gamma_n\) uniquely first, and the second equation determines
\(\alpha_n\) uniquely. This process involves no division by \(n\), so
there is no problem at steps with \(3\mid n\) either.

In conclusion, the solution \((A,C)\) of (4.9) satisfying the initial
values is at most one in \(\mathbb F_3[[x]]\).

## 4.4. The auxiliary series \(T\) and the candidate solution \(B\)

In \(\mathbb F_3[[x]]\), set

\[
T(x)=\sum_{j\ge0}x^{3^j}
=x+x^3+x^9+x^{27}+\cdots
\]

By the Frobenius identity in characteristic 3,

\[
T(x)^3
=\sum_{j\ge0}x^{3^{j+1}}
=T(x)-x. \tag{4.12}
\]

Therefore

\[
T^3=T-x,\qquad x=T-T^3=T(1-T^2). \tag{4.13}
\]

Now define

\[
B(x)=\frac{T+T^2-x}{x^2}. \tag{4.14}
\]

Since \(T=x+O(x^3)\), \(T^2=x^2+O(x^4)\), the numerator is

\[
T+T^2-x=x^2+O(x^3),
\]

and therefore \(B\in\mathbb F_3[[x]]\) with \(B(0)=1\).

Using (4.13), \(B\) can be rewritten as a quotient of units. First,

\[
T+T^2-x
=T+T^2-(T-T^3)
=T^2+T^3
=T^2(1+T),
\]

and

\[
\begin{aligned}
x^2
&=T^2(1-T^2)^2\\
&=T^2(1-T)^2(1+T)^2.
\end{aligned}
\]

Therefore

\[
B
=\frac1{(1-T)^2(1+T)}. \tag{4.15}
\]

Expanding the denominator,

\[
\begin{aligned}
(1-T)^2(1+T)
&=(1-2T+T^2)(1+T)\\
&=1-T-T^2+T^3\\
&=1-T-T^2+(T-x)\\
&=1-x-T^2.
\end{aligned}
\]

Therefore

\[
\boxed{
B=\frac1{1-x-T^2}.
} \tag{4.16}
\]

## 4.5. The algebraic equation satisfied by \(B\)

We will show the following.

\[
\boxed{B=1+xB^2+x^3B^3.} \tag{4.17}
\]

Setting \(F=1-x-T^2\), we have \(B=F^{-1}\). Denote the difference
between the left- and right-hand sides of the equation to be verified by

\[
E=B-1-xB^2-x^3B^3.
\]

Since \(F\) is a unit with constant term 1, to check whether \(E=0\) we
may compute \(F^3E\) instead. By \(BF=1\),

\[
F^3E=F^2-F^3-xF-x^3. \tag{4.18}
\]

In characteristic 3,

\[
F^3=(1-x-T^2)^3=1-x^3-T^6,
\]

and

\[
\begin{aligned}
F^2
&=(1-x-T^2)^2\\
&=1+x^2+T^4-2x-2T^2+2xT^2\\
&=1+x^2+T^4+x+T^2-xT^2.
\end{aligned}
\]

Also,

\[
-xF=-x+x^2+xT^2.
\]

Substituting these into (4.18),

\[
\begin{aligned}
F^3E
={}&
(1+x^2+T^4+x+T^2-xT^2)\\
&+(-1+x^3+T^6)\\
&+(-x+x^2+xT^2)-x^3\\
={}&T^6+T^4+T^2-x^2.
\end{aligned}
\]

In characteristic 3 we have \(-2=1\), so

\[
T^6+T^4+T^2=(T^3-T)^2.
\]

Therefore, by (4.12),

\[
F^3E=(T^3-T)^2-x^2=(-x)^2-x^2=0.
\]

Since \(F^3\) is a unit, \(E=0\), i.e. (4.17) is proved.

## 4.6. The differential identity and the candidate solution of the system

We differentiate (4.17) formally. In characteristic 3,

\[
(x^3B^3)'=3x^2B^3+3x^3B^2B'=0,
\]

and

\[
(xB^2)'=B^2+2xBB'.
\]

Therefore

\[
B'=B^2+2xBB'.
\]

Here \(2=-1\), so

\[
\boxed{(1+xB)B'=B^2.} \tag{4.19}
\]

Since \(1+xB\) is a unit with constant term 1,

\[
B'=\frac{B^2}{1+xB}. \tag{4.20}
\]

Now set

\[
D=x+x(B-1)\frac{B'}B. \tag{4.21}
\]

By definition, \((B,D)\) satisfies the second equation of (4.9). We
verify directly that the first equation,

\[
xD'=B-1, \tag{4.22}
\]

is also satisfied.

Set the following.

\[
q=1+xB,\qquad U=B(B-1).
\]

By (4.20),

\[
B'=\frac{B^2}{q},
\]

and (4.21) becomes

\[
D=x+\frac{xU}{q}.
\]

Also,

\[
U'=(2B-1)B'=(2B-1)\frac{B^2}{q}
\]

and

\[
q'=B+xB'=B+\frac{xB^2}{q}
=\frac{Bq+xB^2}{q}.
\]

Therefore

\[
D'
=1+\frac Uq+\frac{xU'}q-\frac{xUq'}{q^2},
\]

that is,

\[
\begin{aligned}
xD'-(B-1)
={}&x-B+1+\frac{xU}{q}\\
&+\frac{x^2(2B-1)B^2}{q^2}
-\frac{x^2U(Bq+xB^2)}{q^3}.
\end{aligned}
\]

Multiplying both sides by \(q^3\), the numerator is

\[
\begin{aligned}
N={}&(x-B+1)q^3+xUq^2\\
&+x^2(2B-1)B^2q
-x^2U(Bq+xB^2).
\end{aligned} \tag{4.23}
\]

In characteristic 3,

\[
q^2=1-xB+x^2B^2,\qquad q^3=1+x^3B^3.
\]

Expanding the four terms of (4.23) individually,

\[
\begin{aligned}
(x-B+1)q^3
={}&-B^4x^3+B^3x^4+B^3x^3-B+x+1,\\
xUq^2
={}&B^4x^3-B^3x^3-B^3x^2
 +B^2x^2+B^2x-xB,\\
x^2(2B-1)B^2q
={}&-B^4x^3-B^3x^3-B^3x^2-B^2x^2,\\
-x^2U(Bq+xB^2)
={}&B^4x^3-B^3x^3-B^3x^2+B^2x^2.
\end{aligned}
\]

Adding these four expressions, the \(B^4x^3\) terms and the \(B^3x^2\)
terms cancel, giving

\[
\begin{aligned}
N
&=B^3x^4+B^3x^3+B^2x^2+B^2x-xB-B+x+1\\
&=(x+1)(x^3B^3+xB^2-B+1).
\end{aligned}
\]

But (4.17) can be rewritten as exactly

\[
x^3B^3+xB^2-B+1=0,
\]

so \(N=0\). Since \(q\) is a unit,

\[
xD'-(B-1)=\frac{N}{q^3}=0.
\]

Therefore (4.22) holds.

In the end, \((B,D)\) satisfies

\[
xD'=B-1,\qquad
D=x+x(B-1)\frac{B'}B.
\]

Moreover, since \(B(0)=1\) and \(B-1\in x\mathbb F_3[[x]]\),

\[
D=x+O(x^2).
\]

That is, \((B,D)\) satisfies the same system and the same initial values
as the original reduced solution \((A,C)\). By the uniqueness of
Section 4.3,

\[
\boxed{
A(x)\equiv B(x)
=\frac{T+T^2-x}{x^2}
\pmod3.
} \tag{4.24}
\]

## 4.7. Classification of all coefficients via base 3

We now read off the coefficients of (4.24). First,

\[
T-x=\sum_{j\ge1}x^{3^j}.
\]

Also,

\[
\begin{aligned}
T^2
&=\left(\sum_{j\ge0}x^{3^j}\right)^2\\
&=\sum_{j\ge0}x^{2\cdot3^j}
 +2\sum_{0\le i<j}x^{3^i+3^j}.
\end{aligned}
\]

Therefore

\[
\boxed{
T+T^2-x
=
\sum_{j\ge1}x^{3^j}
+\sum_{j\ge0}x^{2\cdot3^j}
+2\sum_{0\le i<j}x^{3^i+3^j}.
} \tag{4.25}
\]

These three families of exponents are completely distinguished in
base 3.

- The base-3 representation of \(3^j\) has a \(1\) in exactly one digit
  and 0 everywhere else.
- The base-3 representation of \(2\cdot3^j\) has a \(2\) in exactly one
  digit and 0 everywhere else.
- The base-3 representation of \(3^i+3^j\), \(i<j\), has a \(1\) in two
  distinct digits and 0 everywhere else.

By the uniqueness of the base-3 representation there is no collision
between the three distinct kinds, and within each kind there are no
distinct index choices producing the same integer. Therefore the
coefficients of (4.25) involve no hidden summation or cancellation.

In (4.24) we divided by \(x^2\), so

\[
a_n\bmod3=[x^{n+2}](T+T^2-x).
\]

Writing \(m=n+2\), we obtain the following complete classification.

\[
a_n\equiv
\begin{cases}
1\pmod3,
 &m=3^j\ (j\ge1),\\
1\pmod3,
 &m=2\cdot3^j\ (j\ge0),\\
2\pmod3,
 &m=3^i+3^j\ (0\le i<j),\\
0\pmod3,
 &\text{all other cases}.
\end{cases} \tag{4.26}
\]

It is also fine to write \(j\ge0\) in the original first condition. For
\(n\ge0\) we have \(n+2\ge2\), so the case \(n+2=3^0=1\) does not exist
in the first place.

The boundary values also agree. At \(n=0\),

\[
n+2=2=2\cdot3^0,
\]

so \(a_0\equiv1\pmod3\), and at \(n=1\),

\[
n+2=3=3^1,
\]

so \(a_1\equiv1\pmod3\). Also, at \(n=2\),

\[
n+2=4=3^0+3^1,
\]

so \(a_2\equiv2\pmod3\); this indeed agrees with \(a_2=8\).
This proves both if-and-only-if statements and the \(0\) classification
of the remaining cases. \(\square\)
