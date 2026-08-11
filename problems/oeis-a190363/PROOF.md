# OEIS A190363 점화식의 반증

모든 계산 보조 명제는 정수의 사칙연산, 정수 제곱 비교와 정수 제곱근만
사용한다.

## 정의와 정리

수열을

\[
a(n)=2n+\left\lfloor\frac{n\sqrt5}{2}\right\rfloor
  +\left\lfloor\frac n4\right\rfloor\qquad(n\ge1)
\]

로 정의한다. 검토할 점화식은

\[
a(n+21)=a(n+17)+a(n+4)-a(n). \tag{1}
\]

**정리.** (1)의 첫 실패 기준 인덱스는 \(n=140\), 즉 첫 실패 출력항은
\(a(161)\)이다. 더 나아가 (1)은 무한히 많은 인덱스에서 실패한다.

## 점화식 결함의 단순화

\[
\alpha=\frac{\sqrt5}{2},\qquad \delta=17\alpha-19
\]

로 둔다. \(38^2<5\cdot17^2<40^2\)이므로

\[
19<17\alpha<20,\qquad 0<\delta<1.
\]

각 \(k\ge1\)에 대해

\[
\left\lfloor(k+17)\alpha\right\rfloor
=\lfloor k\alpha\rfloor+19+\varepsilon_k \tag{2}
\]

로 정의하면 \(\varepsilon_k\in\{0,1\}\)이고

\[
\varepsilon_k=1
\iff \{k\alpha\}+\delta\ge1
\iff \{k\alpha\}\ge1-\delta. \tag{3}
\]

점화식 결함을

\[
D(n):=a(n+21)-a(n+17)-a(n+4)+a(n)
\]

으로 둔다. 선형항은

\[
(n+21)-(n+17)-(n+4)+n=0
\]

으로 소거된다. 또한

\[
\left\lfloor\frac{n+21}{4}\right\rfloor
-\left\lfloor\frac{n+17}{4}\right\rfloor=1,
\quad
\left\lfloor\frac{n+4}{4}\right\rfloor
-\left\lfloor\frac n4\right\rfloor=1
\]

이므로 \(\lfloor n/4\rfloor\) 항도 소거된다. 남은 Beatty 항에 (2)를 두 번
적용하면

\[
\begin{aligned}
D(n)
&=\bigl(\lfloor(n+21)\alpha\rfloor-\lfloor(n+4)\alpha\rfloor\bigr)\\
&\quad-\bigl(\lfloor(n+17)\alpha\rfloor-\lfloor n\alpha\rfloor\bigr)\\
&=(19+\varepsilon_{n+4})-(19+\varepsilon_n)\\
&=\varepsilon_{n+4}-\varepsilon_n.
\end{aligned} \tag{4}
\]

따라서 (1)은 정확히 \(\varepsilon_{n+4}=\varepsilon_n\)일 때 성립한다.

## 바닥함수의 정확한 정수 판정

\(\alpha\)는 무리수이므로

\[
q_k:=\lfloor k\alpha\rfloor+1=\lceil k\alpha\rceil.
\]

(3)에서 \(\varepsilon_k=1\)일 필요충분조건은

\[
q_k+19<(k+17)\alpha
\]

이다. 양변이 양수이므로 제곱해도 동치이고,

\[
\varepsilon_k=1
\iff 4(q_k+19)^2<5(k+17)^2. \tag{5}
\]

따라서 정수

\[
H(k):=4(q_k+19)^2-5(k+17)^2 \tag{6}
\]

만 계산하면 된다. \(H(k)=0\)은 \(\sqrt5\)의 무리성 때문에 불가능하며

\[
H(k)>0\iff\varepsilon_k=0,
\qquad H(k)<0\iff\varepsilon_k=1. \tag{7}
\]

바닥함수 자체도 정수 제곱근으로 계산할 수 있다.

\[
\left\lfloor\frac{n\sqrt5}{2}\right\rfloor
=\left\lfloor\frac{\lfloor\sqrt{5n^2}\rfloor}{2}\right\rfloor. \tag{8}
\]

## 첫 반례와 최소성

정확 정수 계산은

\[
\min_{1\le k\le143}H(k)=H(127)=4>0, \tag{9}
\]

\[
H(144)=-5<0 \tag{10}
\]

을 준다. 따라서 \(1\le k\le143\)에서는 \(\varepsilon_k=0\)이고
\(\varepsilon_{144}=1\)이다. \(1\le n\le139\)이면 \(n,n+4\le143\)이므로
(4)에서 \(D(n)=0\)이다. 반면

\[
D(140)=\varepsilon_{144}-\varepsilon_{140}=1.
\]

그러므로 \(140\)이 첫 실패 기준 인덱스다. 실제 네 항의 정확 인증은
다음과 같다.

| \(m\) | \(\lfloor m\sqrt5/2\rfloor\) | 정확한 제곱 인증 | \(a(m)\) |
|---:|---:|---:|---:|
| \(140\) | \(156\) | \(312^2<5\cdot140^2<314^2\) | \(471\) |
| \(144\) | \(160\) | \(320^2<5\cdot144^2<322^2\) | \(484\) |
| \(157\) | \(175\) | \(350^2<5\cdot157^2<352^2\) | \(528\) |
| \(161\) | \(180\) | \(360^2<5\cdot161^2<362^2\) | \(542\) |

따라서

\[
a(157)+a(144)-a(140)=528+484-471=541\ne542=a(161).
\]

## Pell 방정식에서 나오는 무한 반례족

다음 정수쌍을 정의한다.

\[
(p_0,q_0)=(161,144), \tag{11}
\]

\[
p_{t+1}=9p_t+10q_t,
\qquad q_{t+1}=8p_t+9q_t. \tag{12}
\]

직접 전개하면

\[
4p_{t+1}^2-5q_{t+1}^2=4p_t^2-5q_t^2.
\]

초항에서 \(4\cdot161^2-5\cdot144^2=4\)이므로 모든 \(t\ge0\)에 대해

\[
4p_t^2-5q_t^2=4. \tag{13}
\]

또한 \(p_t,q_t>0\)이고 \(q_{t+1}=8p_t+9q_t>q_t\)이므로 서로 다른 해가
무한히 생성된다.

\[
\eta_t:=p_t-q_t\alpha
\]

로 둔다. (13)에서

\[
(p_t-q_t\alpha)(p_t+q_t\alpha)=1
\]

이므로

\[
\eta_t=\frac1{p_t+q_t\alpha}
=\frac2{2p_t+q_t\sqrt5}>0. \tag{14}
\]

(12)를 사용하면

\[
\eta_{t+1}=(9-4\sqrt5)\eta_t. \tag{15}
\]

\(0<9-4\sqrt5<1\)이므로 \(\eta_t\)는 양수인 채 감소한다. 초항에서

\[
\eta_0<\delta
\iff161-72\sqrt5<\frac{17\sqrt5}{2}-19
\iff360<161\sqrt5,
\]

마지막 부등식은

\[
360^2=129600<129605=5\cdot161^2
\]

로 확인된다. 따라서

\[
0<\eta_t<\delta\qquad(t\ge0). \tag{16}
\]

이제

\[
\rho:=\{4\alpha\}=2\sqrt5-4
\]

로 둔다. 다음 두 부등식이 성립한다.

\[
\delta<\rho\iff13\sqrt5<30,
\qquad
\delta+\rho<1\iff21\sqrt5<48.
\]

이는 각각 \(845<900\), \(2205<2304\)의 제곱 비교다. 따라서

\[
0<\eta_t<\delta<\rho,
\qquad \eta_t+\rho<1.
\]

(14)에서 \(q_t\alpha=p_t-\eta_t\)이므로

\[
\{q_t\alpha\}=1-\eta_t,
\]

\[
\{(q_t-4)\alpha\}=1-\eta_t-\rho,
\qquad
\{(q_t+4)\alpha\}=\rho-\eta_t.
\]

(3)을 적용하면

\[
\varepsilon_{q_t}=1,
\qquad \varepsilon_{q_t-4}=0,
\qquad \varepsilon_{q_t+4}=0.
\]

마지막으로 (4)에서

\[
D(q_t-4)=1,
\qquad D(q_t)=-1. \tag{17}
\]

따라서 \(q_t-4\)와 \(q_t\)는 모든 \(t\ge0\)에서 반례다. 첫 반례들은

\[
140,\ 144,\ 2580,\ 2584,\ 46364,\ 46368,\ldots
\]

이며, 동일한 점화식 (1)은 어느 인덱스 이후에도 계속 성립하지 않는다.
