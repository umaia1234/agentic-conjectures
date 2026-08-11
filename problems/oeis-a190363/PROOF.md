**English** | [한국어](PROOF.ko.md)

# Disproof of the OEIS A190363 recurrence

All computational auxiliary claims use only integer arithmetic, integer
square comparisons, and integer square roots.

## Definition and theorem

Define the sequence by

\[
a(n)=2n+\left\lfloor\frac{n\sqrt5}{2}\right\rfloor
  +\left\lfloor\frac n4\right\rfloor\qquad(n\ge1).
\]

The recurrence under examination is

\[
a(n+21)=a(n+17)+a(n+4)-a(n). \tag{1}
\]

**Theorem.** The first failing base index of (1) is \(n=140\), i.e. the
first failing output term is \(a(161)\). Furthermore, (1) fails at
infinitely many indices.

## Simplification of the recurrence defect

Set

\[
\alpha=\frac{\sqrt5}{2},\qquad \delta=17\alpha-19.
\]

Since \(38^2<5\cdot17^2<40^2\),

\[
19<17\alpha<20,\qquad 0<\delta<1.
\]

For each \(k\ge1\), define \(\varepsilon_k\) by

\[
\left\lfloor(k+17)\alpha\right\rfloor
=\lfloor k\alpha\rfloor+19+\varepsilon_k; \tag{2}
\]

then \(\varepsilon_k\in\{0,1\}\) and

\[
\varepsilon_k=1
\iff \{k\alpha\}+\delta\ge1
\iff \{k\alpha\}\ge1-\delta. \tag{3}
\]

Define the recurrence defect as

\[
D(n):=a(n+21)-a(n+17)-a(n+4)+a(n).
\]

The linear terms cancel, since

\[
(n+21)-(n+17)-(n+4)+n=0.
\]

Moreover,

\[
\left\lfloor\frac{n+21}{4}\right\rfloor
-\left\lfloor\frac{n+17}{4}\right\rfloor=1,
\quad
\left\lfloor\frac{n+4}{4}\right\rfloor
-\left\lfloor\frac n4\right\rfloor=1,
\]

so the \(\lfloor n/4\rfloor\) terms cancel as well. Applying (2) twice to
the remaining Beatty terms gives

\[
\begin{aligned}
D(n)
&=\bigl(\lfloor(n+21)\alpha\rfloor-\lfloor(n+4)\alpha\rfloor\bigr)\\
&\quad-\bigl(\lfloor(n+17)\alpha\rfloor-\lfloor n\alpha\rfloor\bigr)\\
&=(19+\varepsilon_{n+4})-(19+\varepsilon_n)\\
&=\varepsilon_{n+4}-\varepsilon_n.
\end{aligned} \tag{4}
\]

Therefore (1) holds exactly when \(\varepsilon_{n+4}=\varepsilon_n\).

## Exact integer test for the floor function

Since \(\alpha\) is irrational,

\[
q_k:=\lfloor k\alpha\rfloor+1=\lceil k\alpha\rceil.
\]

By (3), \(\varepsilon_k=1\) holds if and only if

\[
q_k+19<(k+17)\alpha.
\]

Both sides are positive, so squaring preserves equivalence, and

\[
\varepsilon_k=1
\iff 4(q_k+19)^2<5(k+17)^2. \tag{5}
\]

Therefore it suffices to compute the integer

\[
H(k):=4(q_k+19)^2-5(k+17)^2. \tag{6}
\]

\(H(k)=0\) is impossible by the irrationality of \(\sqrt5\), and

\[
H(k)>0\iff\varepsilon_k=0,
\qquad H(k)<0\iff\varepsilon_k=1. \tag{7}
\]

The floor function itself can also be computed with integer square roots.

\[
\left\lfloor\frac{n\sqrt5}{2}\right\rfloor
=\left\lfloor\frac{\lfloor\sqrt{5n^2}\rfloor}{2}\right\rfloor. \tag{8}
\]

## First counterexample and minimality

Exact integer computation gives

\[
\min_{1\le k\le143}H(k)=H(127)=4>0, \tag{9}
\]

\[
H(144)=-5<0. \tag{10}
\]

Therefore \(\varepsilon_k=0\) for \(1\le k\le143\), and
\(\varepsilon_{144}=1\). If \(1\le n\le139\), then \(n,n+4\le143\), so
\(D(n)=0\) by (4). On the other hand,

\[
D(140)=\varepsilon_{144}-\varepsilon_{140}=1.
\]

Therefore \(140\) is the first failing base index. The exact certifications
of the four actual terms are as follows.

| \(m\) | \(\lfloor m\sqrt5/2\rfloor\) | Exact square certification | \(a(m)\) |
|---:|---:|---:|---:|
| \(140\) | \(156\) | \(312^2<5\cdot140^2<314^2\) | \(471\) |
| \(144\) | \(160\) | \(320^2<5\cdot144^2<322^2\) | \(484\) |
| \(157\) | \(175\) | \(350^2<5\cdot157^2<352^2\) | \(528\) |
| \(161\) | \(180\) | \(360^2<5\cdot161^2<362^2\) | \(542\) |

Therefore

\[
a(157)+a(144)-a(140)=528+484-471=541\ne542=a(161).
\]

## Infinite family of counterexamples from a Pell equation

Define the following integer pairs.

\[
(p_0,q_0)=(161,144), \tag{11}
\]

\[
p_{t+1}=9p_t+10q_t,
\qquad q_{t+1}=8p_t+9q_t. \tag{12}
\]

Direct expansion gives

\[
4p_{t+1}^2-5q_{t+1}^2=4p_t^2-5q_t^2.
\]

Since \(4\cdot161^2-5\cdot144^2=4\) at the initial term, for all \(t\ge0\)

\[
4p_t^2-5q_t^2=4. \tag{13}
\]

Moreover \(p_t,q_t>0\) and \(q_{t+1}=8p_t+9q_t>q_t\), so infinitely many
distinct solutions are generated.

Set

\[
\eta_t:=p_t-q_t\alpha.
\]

By (13),

\[
(p_t-q_t\alpha)(p_t+q_t\alpha)=1,
\]

so

\[
\eta_t=\frac1{p_t+q_t\alpha}
=\frac2{2p_t+q_t\sqrt5}>0. \tag{14}
\]

Using (12),

\[
\eta_{t+1}=(9-4\sqrt5)\eta_t. \tag{15}
\]

Since \(0<9-4\sqrt5<1\), \(\eta_t\) decreases while remaining positive. At
the initial term,

\[
\eta_0<\delta
\iff161-72\sqrt5<\frac{17\sqrt5}{2}-19
\iff360<161\sqrt5,
\]

and the last inequality is confirmed by

\[
360^2=129600<129605=5\cdot161^2.
\]

Therefore

\[
0<\eta_t<\delta\qquad(t\ge0). \tag{16}
\]

Now set

\[
\rho:=\{4\alpha\}=2\sqrt5-4.
\]

The following two inequalities hold.

\[
\delta<\rho\iff13\sqrt5<30,
\qquad
\delta+\rho<1\iff21\sqrt5<48.
\]

These are the square comparisons \(845<900\) and \(2205<2304\),
respectively. Therefore

\[
0<\eta_t<\delta<\rho,
\qquad \eta_t+\rho<1.
\]

By (14), \(q_t\alpha=p_t-\eta_t\), so

\[
\{q_t\alpha\}=1-\eta_t,
\]

\[
\{(q_t-4)\alpha\}=1-\eta_t-\rho,
\qquad
\{(q_t+4)\alpha\}=\rho-\eta_t.
\]

Applying (3) gives

\[
\varepsilon_{q_t}=1,
\qquad \varepsilon_{q_t-4}=0,
\qquad \varepsilon_{q_t+4}=0.
\]

Finally, by (4),

\[
D(q_t-4)=1,
\qquad D(q_t)=-1. \tag{17}
\]

Therefore \(q_t-4\) and \(q_t\) are counterexamples for every \(t\ge0\).
The first counterexamples are

\[
140,\ 144,\ 2580,\ 2584,\ 46364,\ 46368,\ldots
\]

and the same recurrence (1) never holds permanently beyond any index.
