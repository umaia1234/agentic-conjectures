[English](PROOF.md) | **한국어**

# A056777에서 \(n+12\)가 소수 거듭제곱인 경우의 배제

## 문제와 정리

합성수 \(n\ge4\)가

\[
\varphi(n+12)=\varphi(n)+12, \tag{1}
\]

\[
\sigma(n+12)=\sigma(n)+12 \tag{2}
\]

를 동시에 만족한다고 하자.

**정리.** (1), (2)를 만족하는 합성수 \(n\ge4\)에 대해 \(n+12\)는 소수
거듭제곱일 수 없다.

## 네 보조함수와 불변량

\[
N:=n+12
\]

로 두고

\[
A(m):=m-\varphi(m),
\qquad
B(m):=\sigma(m)-m,
\qquad
T(m):=B(m)-A(m)
\]

로 정의한다. (1)에서

\[
\begin{aligned}
A(N)&=N-\varphi(N)\\
&=(n+12)-(\varphi(n)+12)\\
&=n-\varphi(n)=A(n).
\end{aligned}
\]

마찬가지로 (2)에서 \(B(N)=B(n)\), 따라서

\[
A(N)=A(n),\qquad B(N)=B(n),\qquad T(N)=T(n). \tag{3}
\]

이제

\[
Q(m):=A(m)B(m)-mT(m)
\]

로 둔다. 정의를 전개하면

\[
\begin{aligned}
Q(m)
&=(m-\varphi(m))(\sigma(m)-m)\\
&\quad-m(\sigma(m)-m-(m-\varphi(m)))\\
&=m^2-\varphi(m)\sigma(m).
\end{aligned} \tag{4}
\]

(3)을 사용하면

\[
\begin{aligned}
Q(n)
&=A(n)B(n)-nT(n)\\
&=A(N)B(N)-(N-12)T(N)\\
&=Q(N)+12T(N).
\end{aligned} \tag{5}
\]

## 서로 다른 소인수가 둘 이상이면 \(Q(m)>m\)

\[
m=\prod_i r_i^{e_i}
\]

라 하자. 각 소수 거듭제곱에서

\[
\varphi(r^e)\sigma(r^e)
=r^{e-1}(r-1)\frac{r^{e+1}-1}{r-1}
=r^{2e}\left(1-\frac1{r^{e+1}}\right).
\]

곱셈성에 따라

\[
\varphi(m)\sigma(m)
=m^2\prod_i\left(1-\frac1{r_i^{e_i+1}}\right).
\]

따라서

\[
Q(m)=m^2\left[1-\prod_i\left(1-\frac1{r_i^{e_i+1}}\right)\right]. \tag{6}
\]

\(m\)에 서로 다른 소인수가 적어도 두 개 있다고 하자. 최소 소인수를
\(r\)라 하고

\[
r^e\parallel m,\qquad m=r^eu
\]

로 쓰면 다른 소인수가 있으므로 \(u>r\)이다. (6)에서

\[
1-\prod_i(1-x_i)>x_r=\frac1{r^{e+1}},
\]

따라서

\[
Q(m)>\frac{m^2}{r^{e+1}}=m\frac ur>m. \tag{7}
\]

## \(N=q^\ell\) 가정

모순을 위해

\[
N=q^\ell
\]

이라고 가정하자. 여기서 \(q\)는 소수이고 \(\ell\ge1\)이다.

먼저 \(n=r^a\)도 합성 소수 거듭제곱이라고 가정하면 \(a\ge2\)이고,
(3)에서

\[
r^{a-1}=A(n)=A(N)=q^{\ell-1}. \tag{8}
\]

\(\ell=1\)이면 우변이 \(1\)인데 좌변은 \(r^{a-1}>1\)이므로 모순이다.
\(\ell\ge2\)이면 유일분해에 따라 \(r=q,a=\ell\), 따라서 \(n=N\)이 되어
\(N=n+12\)와 모순이다.

그러므로 \(n\)에는 서로 다른 소인수가 적어도 두 개 있고, (7)에 따라

\[
Q(n)>n. \tag{9}
\]

한편 \(N=q^\ell\)에 대해서는

\[
A(N)=q^{\ell-1},
\qquad
B(N)=1+q+\cdots+q^{\ell-1},
\]

\[
T(N)=\frac{q^{\ell-1}-1}{q-1},
\qquad Q(N)=q^{\ell-1}.
\]

\(\ell=1\)이면 \(T(N)=0\)이고, \(\ell\ge2\)이면
\(T(N)=1+q+\cdots+q^{\ell-2}\)다. (5)에 대입하면

\[
Q(n)=q^{\ell-1}+12\frac{q^{\ell-1}-1}{q-1}. \tag{10}
\]

\(n=q^\ell-12\)이므로

\[
\boxed{
(q-1)(Q(n)-n)
=q^{\ell-1}\bigl(12-(q-1)^2\bigr)+12(q-2).
} \tag{11}
\]

(9)에 따라 (11)의 좌변은 양수여야 한다.

## 모든 소수 \(q\)의 배제

### 경우 1: \(\ell=1\)

\(N=q=n+12\ge16\)이고 \(q\)가 소수이므로 \(q\ge17\)이다. (11)의
우변은

\[
12-(q-1)^2+12(q-2)=-(q-1)(q-13)<0,
\]

모순이다. 이제부터 \(\ell\ge2\)라 하자.

### 경우 2: \(q\ge7\)

\(12-(q-1)^2<0\)이고 \(q^{\ell-1}\ge q\)이므로 (11)의 우변은

\[
\begin{aligned}
&q^{\ell-1}\bigl(12-(q-1)^2\bigr)+12(q-2)\\
&\le q\bigl(12-(q-1)^2\bigr)+12(q-2)\\
&=-(q-1)(q^2-q-24)<0.
\end{aligned}
\]

이는 좌변의 양수성과 모순이다.

### 경우 3: \(q=5\)

\(\ell=2\)이면 \(n=5^2-12=13\)으로 합성수 가정에 어긋난다.
\(\ell\ge3\)이면 (11)의 우변은

\[
-4\cdot5^{\ell-1}+36<0,
\]

모순이다.

### 경우 4: \(q=3\)

\(n=3^\ell-12\ge4\)이므로 \(\ell\ge3\)이다. 다음과 같이 둔다.

\[
m:=3^{\ell-1}-4.
\]

그러면

\[
n=3m,\qquad\gcd(3,m)=1,\qquad m\ge5,
\]

이고 \(m\)은 홀수다. 토션트 식 (1)은

\[
\varphi(n)=\varphi(3^\ell)-12=2\cdot3^{\ell-1}-12.
\]

한편 \(\gcd(3,m)=1\)이므로

\[
\varphi(n)=\varphi(3)\varphi(m)=2\varphi(m).
\]

따라서

\[
\varphi(m)=3^{\ell-1}-6=m-2,
\]

즉

\[
m-\varphi(m)=2. \tag{12}
\]

\(m\)이 소수이면 \(m-\varphi(m)=1\)이므로 모순이다. \(m\)이 합성수이면
최소 소인수를 \(p\)라 할 때 \(p\ge3,p\le\sqrt m\)이고, \(1,\ldots,m\)
중 \(p\)의 배수만 세어도

\[
m-\varphi(m)\ge\frac mp\ge p\ge3,
\]

이므로 역시 (12)에 모순이다.

### 경우 5: \(q=2\)

\(2^\ell-12\ge4\)이므로 \(\ell\ge4\)다. \(\ell=4\)이면 \(n=4\)이고,
이는 위에서 배제한 합성 소수 거듭제곱이다.

이제 \(\ell\ge5\)라 하자. 약수합 식 (2)에서

\[
\sigma(n)=\sigma(2^\ell)-12=2^{\ell+1}-13,
\]

따라서 \(\sigma(n)\)은 홀수다.

여기서 표준 보조사실을 직접 확인한다. \(m=\prod p^e\)에서 홀수 소수
\(p\)에 대해

\[
\sigma(p^e)=1+p+\cdots+p^e
\]

의 홀짝은 \(e+1\)의 홀짝과 같으므로, 이것이 홀수일 필요충분조건은
\(e\)가 짝수인 것이다. \(2^e\)의 약수합은 항상 홀수다. 따라서

\[
\sigma(m)\text{이 홀수}
\iff m\text{이 제곱수 또는 제곱수의 두 배}. \tag{13}
\]

그런데

\[
n=2^\ell-12=4(2^{\ell-2}-3),
\qquad v_2(n)=2.
\]

두 배의 제곱수는 2-adic 지수가 홀수이므로 \(n\)은 제곱수여야 한다.
따라서 \(2^{\ell-2}-3\)도 홀수 제곱이어야 한다. 그러나 \(\ell\ge5\)이므로

\[
2^{\ell-2}-3\equiv-3\equiv5\pmod8,
\]

반면 홀수 제곱은 \(1\pmod8\)이다. 모순이다.

모든 소수 \(q\)가 배제되었으므로 정리가 증명된다.
