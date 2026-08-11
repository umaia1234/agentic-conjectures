# OEIS A060841의 두 추측

모든 계산 보조 명제는 정수의 사칙연산, 소인수 지수와 정확한 유리수
약분만 사용한다.

## 정의와 결론

\[
R_n:=\prod_{k=1}^n\frac{k^2}{\varphi(k)}
=\frac{(n!)^2}{\prod_{k=1}^n\varphi(k)}, \tag{1}
\]

여기서 \(\varphi\)는 Euler의 토션트 함수다.

**정리 1.**

\[
\boxed{R_n\in\mathbb Z\iff n\in\{1,2,\ldots,34,36,38\}.} \tag{2}
\]

**정리 2.** \(R_n\)의 기약분모가 항상 2의 거듭제곱이라는 주장은
거짓이다. 홀수 소수가 기약분모에 처음 나타나는 인덱스는 \(n=1807\)이고

\[
\boxed{\operatorname{den}(R_{1807})=2^{2342}\cdot3.} \tag{3}
\]

## 모든 소수에 대한 지수 공식

소수 \(q\)에 대해 \(E_q(n):=v_q(R_n)\)로 둔다. Legendre 공식에 따라

\[
v_q(n!)=\sum_{j\ge1}\left\lfloor\frac{n}{q^j}\right\rfloor. \tag{4}
\]

\(k=\prod_p p^{a_p}\)이면

\[
\varphi(k)=\prod_{p\mid k}p^{a_p-1}(p-1),
\]

따라서

\[
v_q(\varphi(k))
=\max(v_q(k)-1,0)
+\sum_{\substack{p\mid k\\p\ne q}}v_q(p-1). \tag{5}
\]

첫 항을 \(1\le k\le n\)에서 합하면

\[
\sum_{k\le n}\max(v_q(k)-1,0)
=\sum_{j\ge2}\left\lfloor\frac{n}{q^j}\right\rfloor. \tag{6}
\]

두 번째 항에서 소수 \(p\)는 정확히 \(p\)의 배수마다 한 번씩 나타나므로

\[
\sum_{k\le n}\sum_{\substack{p\mid k\\p\ne q}}v_q(p-1)
=\sum_{\substack{p\le n\\p\text{ prime},\ p\ne q}}
v_q(p-1)\left\lfloor\frac np\right\rfloor. \tag{7}
\]

(1), (4)--(7)을 결합하면

\[
\boxed{
E_q(n)=2\left\lfloor\frac nq\right\rfloor
+\sum_{j\ge2}\left\lfloor\frac n{q^j}\right\rfloor
-\sum_{\substack{p\le n\\p\text{ prime},\ p\ne q}}
v_q(p-1)\left\lfloor\frac np\right\rfloor.
} \tag{8}
\]

이 공식은 전역 증명과 모든 유한 인증에 공통으로 쓰인다.

## \(n\ge91\)에서 정수가 아님을 보이는 2-adic 경계

\(q=2\)를 (8)에 대입하면

\[
E_2(n)=2\left\lfloor\frac n2\right\rfloor
+\sum_{j\ge2}\left\lfloor\frac n{2^j}\right\rfloor
-\sum_{\substack{p\le n\\p\text{ odd prime}}}
v_2(p-1)\left\lfloor\frac np\right\rfloor. \tag{9}
\]

양의 부분은

\[
2\left\lfloor\frac n2\right\rfloor
+\sum_{j\ge2}\left\lfloor\frac n{2^j}\right\rfloor
\le n+n\sum_{j\ge2}\frac1{2^j}=\frac{3n}{2}. \tag{10}
\]

음의 합에서는 홀수 소수 \(p\le79\)만 남겨도 충분하다. 가중치
\(w_p=v_2(p-1)\)는 다음과 같다.

| \(p\) | 3 | 5 | 7 | 11 | 13 | 17 | 19 | 23 | 29 | 31 | 37 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| \(w_p\) | 1 | 2 | 1 | 1 | 2 | 4 | 1 | 1 | 2 | 1 | 2 |

| \(p\) | 41 | 43 | 47 | 53 | 59 | 61 | 67 | 71 | 73 | 79 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| \(w_p\) | 3 | 1 | 1 | 2 | 1 | 2 | 1 | 1 | 3 | 1 |

정확한 합은

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

\(\lfloor x\rfloor>x-1\)을 사용하면

\[
\sum_{\substack{3\le p\le79\\p\text{ prime}}}
w_p\left\lfloor\frac np\right\rfloor
>nC-W>\frac{15n}{8}-34. \tag{13}
\]

(9), (10), (13)에서

\[
E_2(n)<\frac{3n}{2}-\left(\frac{15n}{8}-34\right)
=34-\frac{3n}{8}. \tag{14}
\]

\[
n\ge91\implies34-\frac{3n}{8}
\le34-\frac{273}{8}=-\frac18<0.
\]

따라서 \(E_2(n)<0\) for all \(n\ge91\). 즉 이 범위에서 \(R_n\)은
항상 정수가 아니다.

## \(n\le90\)의 정확 유한 인증

유리수 점화식

\[
R_0=1,\qquad R_n=R_{n-1}\frac{n^2}{\varphi(n)} \tag{15}
\]

을 매 단계 기약분수로 약분하면

\[
\operatorname{den}(R_n)=1\qquad(1\le n\le34),
\]

\[
\operatorname{den}(R_{35})=2,
\quad\operatorname{den}(R_{36})=1,
\quad\operatorname{den}(R_{37})=2,
\quad\operatorname{den}(R_{38})=1. \tag{16}
\]

\(39\le n\le90\)에서는 (9)의 정확 정수값이 모두 음수다.

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

따라서 이 구간에서는 모두 분모에 2가 남는다. (14)와 (16)을 결합하면
정리 1이 증명된다.

## 첫 홀수 분모 \(n=1807\)

(8)과 동치인 한 단계 갱신식은

\[
E_q(0)=0,
\qquad E_q(n)=E_q(n-1)+2v_q(n)-v_q(\varphi(n)). \tag{17}
\]

기약분모에서 소수 \(q\)의 지수는 \(\max(0,-E_q(n))\)이다. (17)을 모든
\(n\le1807\)과 모든 소수 \(q\le n\)에 정확히 적용하면

\[
E_q(n)\ge0
\quad\text{for every odd prime }q\text{ and every }n\le1806, \tag{18}
\]

\[
E_3(1807)=-1,
\qquad E_q(1807)\ge0\quad(q\ge5\text{ prime}) \tag{19}
\]

을 얻는다. \(q>n\)이면 \(q\)는 \(1,\ldots,n\)의 어떤 \(k\)나
\(\varphi(k)<k\)도 나누지 않으므로 \(E_q(n)=0\)이다. 따라서 (18)의 유한
인증에서는 \(q\le n\)인 소수만 검사하면 충분하다.

3-adic 경계는 (8)에서도 직접 보인다. \(n=1806\)에서 양의 부분은

\[
2\left\lfloor\frac{1806}{3}\right\rfloor
+\left\lfloor\frac{1806}{9}\right\rfloor
+\left\lfloor\frac{1806}{27}\right\rfloor
+\left\lfloor\frac{1806}{81}\right\rfloor
+\left\lfloor\frac{1806}{243}\right\rfloor
+\left\lfloor\frac{1806}{729}\right\rfloor
=1501,
\]

음의 소수 기여는 \(1500\)이므로

\[
E_3(1806)=1. \tag{20}
\]

한편

\[
1807=13\cdot139,
\qquad \varphi(1807)=12\cdot138=1656=2^3\cdot3^2\cdot23.
\]

따라서 (17)의 한 단계 변화는

\[
2v_3(1807)-v_3(\varphi(1807))=0-2=-2,
\]

이고

\[
E_3(1807)=1-2=-1. \tag{21}
\]

동시에

\[
E_2(1806)=-2339,
\]

\[
E_2(1807)=E_2(1806)-v_2(\varphi(1807))=-2339-3=-2342. \tag{22}
\]

(18)--(22)에 따라

\[
\operatorname{den}(R_{1806})=2^{2339},
\qquad
\operatorname{den}(R_{1807})=2^{2342}\cdot3.
\]

그러므로 \(1807\)이 홀수 소수가 기약분모에 나타나는 최소 인덱스이고
정리 2가 증명된다.
