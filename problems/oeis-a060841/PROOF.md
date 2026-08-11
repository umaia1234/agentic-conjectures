**English** | [한국어](PROOF.ko.md)

# The two conjectures of OEIS A060841

All computational auxiliary claims use only integer arithmetic,
prime-factor exponents, and exact rational reduction.

## Definitions and conclusions

\[
R_n:=\prod_{k=1}^n\frac{k^2}{\varphi(k)}
=\frac{(n!)^2}{\prod_{k=1}^n\varphi(k)}, \tag{1}
\]

where \(\varphi\) is Euler's totient function.

**Theorem 1.**

\[
\boxed{R_n\in\mathbb Z\iff n\in\{1,2,\ldots,34,36,38\}.} \tag{2}
\]

**Theorem 2.** The claim that the reduced denominator of \(R_n\) is
always a power of 2 is false. The first index at which an odd prime
appears in the reduced denominator is \(n=1807\), and

\[
\boxed{\operatorname{den}(R_{1807})=2^{2342}\cdot3.} \tag{3}
\]

## Exponent formula for every prime

For a prime \(q\), set \(E_q(n):=v_q(R_n)\). By Legendre's formula,

\[
v_q(n!)=\sum_{j\ge1}\left\lfloor\frac{n}{q^j}\right\rfloor. \tag{4}
\]

If \(k=\prod_p p^{a_p}\), then

\[
\varphi(k)=\prod_{p\mid k}p^{a_p-1}(p-1),
\]

hence

\[
v_q(\varphi(k))
=\max(v_q(k)-1,0)
+\sum_{\substack{p\mid k\\p\ne q}}v_q(p-1). \tag{5}
\]

Summing the first term over \(1\le k\le n\),

\[
\sum_{k\le n}\max(v_q(k)-1,0)
=\sum_{j\ge2}\left\lfloor\frac{n}{q^j}\right\rfloor. \tag{6}
\]

In the second term, a prime \(p\) appears exactly once at each multiple
of \(p\), so

\[
\sum_{k\le n}\sum_{\substack{p\mid k\\p\ne q}}v_q(p-1)
=\sum_{\substack{p\le n\\p\text{ prime},\ p\ne q}}
v_q(p-1)\left\lfloor\frac np\right\rfloor. \tag{7}
\]

Combining (1), (4)--(7),

\[
\boxed{
E_q(n)=2\left\lfloor\frac nq\right\rfloor
+\sum_{j\ge2}\left\lfloor\frac n{q^j}\right\rfloor
-\sum_{\substack{p\le n\\p\text{ prime},\ p\ne q}}
v_q(p-1)\left\lfloor\frac np\right\rfloor.
} \tag{8}
\]

This formula is used in common by the global proof and by every finite
certification.

## 2-adic bound showing non-integrality for \(n\ge91\)

Substituting \(q=2\) into (8),

\[
E_2(n)=2\left\lfloor\frac n2\right\rfloor
+\sum_{j\ge2}\left\lfloor\frac n{2^j}\right\rfloor
-\sum_{\substack{p\le n\\p\text{ odd prime}}}
v_2(p-1)\left\lfloor\frac np\right\rfloor. \tag{9}
\]

The positive part is

\[
2\left\lfloor\frac n2\right\rfloor
+\sum_{j\ge2}\left\lfloor\frac n{2^j}\right\rfloor
\le n+n\sum_{j\ge2}\frac1{2^j}=\frac{3n}{2}. \tag{10}
\]

In the negative sum it suffices to keep only the odd primes
\(p\le79\). The weights \(w_p=v_2(p-1)\) are as follows.

| \(p\) | 3 | 5 | 7 | 11 | 13 | 17 | 19 | 23 | 29 | 31 | 37 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| \(w_p\) | 1 | 2 | 1 | 1 | 2 | 4 | 1 | 1 | 2 | 1 | 2 |

| \(p\) | 41 | 43 | 47 | 53 | 59 | 61 | 67 | 71 | 73 | 79 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| \(w_p\) | 3 | 1 | 1 | 2 | 1 | 2 | 1 | 1 | 3 | 1 |

The exact sums are

\[
W:=\sum_{\substack{3\le p\le79\\p\text{ prime}}}w_p=34, \tag{11}
\]

\[
\begin{aligned}
C:=\sum_{\substack{3\le p\le79\\p\text{ prime}}}\frac{w_p}{p}
&=\frac{3049629558983711743173310451026}
{1608822383670336453949542277065}\\
&>\frac{15}{8}.
\end{aligned} \tag{12}
\]

Using \(\lfloor x\rfloor>x-1\),

\[
\sum_{\substack{3\le p\le79\\p\text{ prime}}}
w_p\left\lfloor\frac np\right\rfloor
>nC-W>\frac{15n}{8}-34. \tag{13}
\]

From (9), (10), (13),

\[
E_2(n)<\frac{3n}{2}-\left(\frac{15n}{8}-34\right)
=34-\frac{3n}{8}. \tag{14}
\]

\[
n\ge91\implies34-\frac{3n}{8}
\le34-\frac{273}{8}=-\frac18<0.
\]

Hence \(E_2(n)<0\) for all \(n\ge91\). That is, in this range \(R_n\)
is never an integer.

## Exact finite certification for \(n\le90\)

Reducing the rational recurrence

\[
R_0=1,\qquad R_n=R_{n-1}\frac{n^2}{\varphi(n)} \tag{15}
\]

to lowest terms at every step gives

\[
\operatorname{den}(R_n)=1\qquad(1\le n\le34),
\]

\[
\operatorname{den}(R_{35})=2,
\quad\operatorname{den}(R_{36})=1,
\quad\operatorname{den}(R_{37})=2,
\quad\operatorname{den}(R_{38})=1. \tag{16}
\]

For \(39\le n\le90\), the exact integer values of (9) are all negative.

| \(n\) | \(E_2(n)\) | \(n\) | \(E_2(n)\) | \(n\) | \(E_2(n)\) | \(n\) | \(E_2(n)\) |
|---:|---:|---:|---:|---:|---:|---:|---:|
|39|-3|40|-1|41|-4|42|-4|
|43|-5|44|-3|45|-6|46|-5|
|47|-6|48|-2|49|-3|50|-3|
|51|-8|52|-7|53|-9|54|-8|
|55|-11|56|-8|57|-10|58|-10|
|59|-11|60|-11|61|-13|62|-12|
|63|-14|64|-7|65|-11|66|-11|
|67|-12|68|-13|69|-15|70|-16|
|71|-17|72|-14|73|-17|74|-17|
|75|-20|76|-18|77|-20|78|-21|
|79|-22|80|-19|81|-20|82|-21|
|83|-22|84|-21|85|-27|86|-26|
|87|-29|88|-26|89|-29|90|-30|

Hence throughout this interval a factor of 2 remains in the
denominator. Combining (14) and (16) proves Theorem 1.

## The first odd denominator \(n=1807\)

A one-step update rule equivalent to (8) is

\[
E_q(0)=0,
\qquad E_q(n)=E_q(n-1)+2v_q(n)-v_q(\varphi(n)). \tag{17}
\]

The exponent of a prime \(q\) in the reduced denominator is
\(\max(0,-E_q(n))\). Applying (17) exactly for all \(n\le1807\) and all
primes \(q\le n\) yields

\[
E_q(n)\ge0
\quad\text{for every odd prime }q\text{ and every }n\le1806, \tag{18}
\]

\[
E_3(1807)=-1,
\qquad E_q(1807)\ge0\quad(q\ge5\text{ prime}) \tag{19}
\]

If \(q>n\), then \(q\) divides neither any \(k\) in \(1,\ldots,n\) nor
\(\varphi(k)<k\), so \(E_q(n)=0\). Hence for the finite certification
of (18) it suffices to check only the primes \(q\le n\).

The 3-adic bound can also be seen directly from (8). At \(n=1806\) the
positive part is

\[
2\left\lfloor\frac{1806}{3}\right\rfloor
+\left\lfloor\frac{1806}{9}\right\rfloor
+\left\lfloor\frac{1806}{27}\right\rfloor
+\left\lfloor\frac{1806}{81}\right\rfloor
+\left\lfloor\frac{1806}{243}\right\rfloor
+\left\lfloor\frac{1806}{729}\right\rfloor
=1501,
\]

and the negative prime contribution is \(1500\), so

\[
E_3(1806)=1. \tag{20}
\]

Meanwhile,

\[
1807=13\cdot139,
\qquad \varphi(1807)=12\cdot138=1656=2^3\cdot3^2\cdot23.
\]

Hence the one-step change of (17) is

\[
2v_3(1807)-v_3(\varphi(1807))=0-2=-2,
\]

and

\[
E_3(1807)=1-2=-1. \tag{21}
\]

At the same time,

\[
E_2(1806)=-2339,
\]

\[
E_2(1807)=E_2(1806)-v_2(\varphi(1807))=-2339-3=-2342. \tag{22}
\]

By (18)--(22),

\[
\operatorname{den}(R_{1806})=2^{2339},
\qquad
\operatorname{den}(R_{1807})=2^{2342}\cdot3.
\]

Therefore \(1807\) is the smallest index at which an odd prime appears
in the reduced denominator, and Theorem 2 is proved.
