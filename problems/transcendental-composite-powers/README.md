# A computable transcendental whose floored powers are all composite

This note gives an unreviewed answer to the transcendental-number part of the
open question in Section 7 of Hahn--Ismailescu--Kim--Kim, *Explicit Algebraic
Numbers all whose Integer Parts of Powers are Always Composite*,
arXiv:2608.05309v1.

Primary source:

- <https://arxiv.org/abs/2608.05309>
- <https://arxiv.org/html/2608.05309>

## Theorem

There is a computable transcendental real number
\(\alpha\in(10,11)\) such that

\[
\lfloor\alpha^n\rfloor
\]

is composite for every integer \(n\geq1\).

## An effective enumeration of the algebraic reals

For an integer polynomial

\[
f(x)=c_dx^d+\cdots+c_1x+c_0,
\]

write \(H(f)=\max_i|c_i|\). Take all primitive irreducible polynomials in
\(\mathbb Z[x]\) with positive leading coefficient. Enumerate the finite
strata \(d+H(f)=2,3,\ldots\), ordering within each stratum first by degree and
then lexicographically by coefficient tuple. For each polynomial, list its
distinct real roots in increasing order, representing each root by the
polynomial together with a rational-endpoint interval that isolates it.

This is a uniform effective procedure. Irreducibility over \(\mathbb Z\) is
decidable; Sturm's algorithm isolates all real roots; and Sturm sequences,
resultants, or gcd computations followed by interval refinement decide exact
comparisons, including equality, between two represented algebraic numbers.
Write the resulting sequence as

\[
\gamma_1,\gamma_2,\gamma_3,\ldots. \tag{1}
\]

Every real algebraic number occurs in (1): normalize its minimal polynomial
to be primitive with positive leading coefficient, then take the
corresponding isolated real root. Repetitions would not hurt the construction,
although this minimal-polynomial enumeration does not require them.

## Nested-interval construction

Set

\[
a_1=10,\qquad K_1=[10,11].
\]

After constructing the even integer \(a_n\), let

\[
K_n=[a_n^{1/n},(a_n+1)^{1/n}].
\]

Define \(a_{n+1}\) to be the least positive even integer \(b\) satisfying

\[
\begin{aligned}
b^n&>a_n^{n+1},\\
(b+1)^n&<(a_n+1)^{n+1},\\
\gamma_n&\notin
[b^{1/(n+1)},(b+1)^{1/(n+1)}].
\end{aligned} \tag{2}
\]

Then put

\[
K_{n+1}=[b^{1/(n+1)},(b+1)^{1/(n+1)}].
\]

The conditions in (2) are a finite algorithmic test, not an oracle choice:
the first two use integer powers, and the last uses exact comparison of real
algebraic numbers.

## Why a candidate always exists

Let

\[
L=a_n^{1+1/n},\qquad U=(a_n+1)^{1+1/n}.
\]

Inductively \(K_n\subset[10,11]\), so \(a_n^{1/n}\geq10\). Applying the mean
value theorem to \(x^{1+1/n}\) on \([a_n,a_n+1]\) gives

\[
U-L=(1+1/n)\xi^{1/n}>10
\]

for some \(\xi\in(a_n,a_n+1)\). Hence the open interval \((L,U-1)\) has
length greater than 9.

Any open interval of length greater than 9 contains at least four even
integers: the first even integer after its left endpoint is at distance at
most 2, and the fourth is only 6 farther away. Every even \(b\in(L,U-1)\)
satisfies the first two conditions in (2).

For distinct even candidates \(b_1<b_2\), we have \(b_2\geq b_1+2\), so

\[
(b_1+1)^{1/(n+1)}<b_2^{1/(n+1)}.
\]

Their corresponding closed root intervals are therefore pairwise disjoint
with positive gaps. The single point \(\gamma_n\) can lie in at most one of
them. At least three of the four candidates satisfy the final condition in
(2), proving that the least admissible positive even \(b\) exists.

The first two strict inequalities in (2) also imply

\[
a_n^{1/n}<b^{1/(n+1)}
<(b+1)^{1/(n+1)}<(a_n+1)^{1/n},
\]

and consequently

\[
K_{n+1}\subset\operatorname{int}K_n. \tag{3}
\]

This establishes the induction assumption \(K_n\subset[10,11]\) as well.

## The unique limiting number

By the mean value theorem applied to \(x^{1/n}\), for some
\(\eta\in(a_n,a_n+1)\),

\[
\begin{aligned}
|K_n|
&=(a_n+1)^{1/n}-a_n^{1/n}\\
&=\frac1n\eta^{1/n-1}\\
&\leq\frac1{n10^{n-1}}\longrightarrow0. \tag{4}
\end{aligned}
\]

The nonempty compact intervals are nested, so they have a common point; (4)
makes that point unique. Call it \(\alpha\). Relation (3) puts \(\alpha\)
in the interior of every \(K_n\), because
\(\alpha\in K_{n+1}\subset\operatorname{int}K_n\). Thus

\[
a_n<\alpha^n<a_n+1
\quad\Longrightarrow\quad
\lfloor\alpha^n\rfloor=a_n. \tag{5}
\]

Since \(a_n^{1/n}\geq10\), we have \(a_n\geq10^n\). Every \(a_n\) is
therefore an even integer at least 10, so (5) is composite for every
\(n\geq1\). Also \(K_2\subset\operatorname{int}K_1=(10,11)\), hence
\(\alpha\in(10,11)\).

At stage \(n\), condition (2) excludes \(\gamma_n\) from \(K_{n+1}\), while
\(\alpha\in K_{n+1}\). Therefore \(\alpha\ne\gamma_n\) for every \(n\).
The enumeration (1) contains all real algebraic numbers, so \(\alpha\) is
transcendental and, in particular, is not a Pisot number.

## Why the limiting number is computable

The search for \(a_{n+1}\) terminates effectively. Test positive even
\(b=2,4,6,\ldots\) in order. The first two conditions in (2) are exact
integer-power comparisons. The two endpoints in the last condition are the
unique positive roots of \(x^{n+1}-b\) and \(x^{n+1}-(b+1)\); rational
isolation plus exact algebraic-number comparison decides whether
\(\gamma_n\) lies in the closed interval, including endpoint equality. The
existence argument guarantees that a candidate is eventually found, so the
integer sequence \(a_1,a_2,\ldots\) is computable.

For an explicit Cauchy name, given \(N\geq0\), compute until

\[
\frac1{n10^{n-1}}<2^{-(N+2)}. \tag{6}
\]

Let \(K_n=[l,u]\), and approximate each algebraic endpoint by rationals
\(\widetilde l,\widetilde u\) with error less than
\(\epsilon=2^{-(N+2)}\). Output
\(Q=(\widetilde l+\widetilde u)/2\). Since \(\alpha\in[l,u]\), (4) and (6)
give

\[
|Q-\alpha|
<\epsilon+\frac{u-l}{2}
<\frac32\epsilon<2^{-N}.
\]

Thus a terminating arbitrary-precision algorithm computes \(\alpha\).

## Scope

The nested-even-interval mechanism is related to Baker--Harman (1996); the
effective diagonal step above forces this particular computable limit to
avoid every algebraic number. The word “explicit” is not formally defined in
the source question. This answers it in the computable-analysis sense, but it
does not provide an elementary closed-form constant.

No numerical implementation is included here: the proof itself specifies the
terminating construction and the required exact algebraic-number operations.
This result was developed separately from pre-existing work elsewhere in this
workspace. Targeted public searches through 2026-08-11 found no earlier posted
answer, but that is not a literature review or a priority claim; the argument
has not been peer reviewed.
