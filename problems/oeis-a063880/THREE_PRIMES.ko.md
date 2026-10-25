[English](THREE_PRIMES.md) | **한국어**

# A063880: 소수 세 개로 이루어진 powerful core

## 결과

**정리.** \(p,q,r\)가 서로 다른 소수이고 \(a,b,c\ge2\)이면
\(n=p^aq^br^c\)는 \(\sigma(n)=2\sigma^*(n)\)을 만족하지 않는다.

[PROOF.md](PROOF.ko.md)의 두 소수 정리와 powerful core \(C(n)\)으로의
환원을 함께 쓰면 다음을 얻는다. **\(\omega(C(n))\le3\)인 모든 해에서
\(C(n)=108\)이다.** 즉 \(n=108s\)이고 \(s\)는 squarefree이며 \(108\)과
서로소이다. 따라서 이 부분족에서는 모든 항이 \(108\pmod{216}\)이고
\(108\)이 유일한 primitive 항이다. 여기 나오는 내용은 모두 Lean에서
커널 검사를 거쳤다(9절). 서로 다른 소수를 네 개 이상 가진 core는 다루지
않으므로 OEIS 추측은 여전히 미해결이다.

## 1. 기호와 경우 나누기

소수 \(p\)와 지수 \(e\ge2\)에 대해

\[
u_p=1+p^e,\qquad t_p=p+p^2+\dots+p^{e-1},\qquad
\sigma_p=\sigma(p^e)=u_p+t_p
\]

라 두자. 그러면 \((p-1)t_p=p^e-p\)이므로 \(u_p=(p+1)+(p-1)t_p\),
\(\sigma_p=(p+1)+p\,t_p\)이다. \(\sigma\)와 \(\sigma^*\)는 곱셈적이고
\(\sigma^*(p^e)=1+p^e\)이므로, \(n=p^aq^br^c\)에 대한 방정식은

\[
R(p,a)\,R(q,b)\,R(r,c)=2,\qquad R(p,e):=\frac{\sigma(p^e)}{1+p^e}
\]

이다. 국소 비율에 관한 다음 세 가지 기초 사실을 쓴다.

- (R1) \(R(p,e)\)는 \(e\)에 대해 증가한다.
- (R2) \(R(p,e)<p/(p-1)\)이다. 따라서 \(m+1\le p\)이면
  \(m\,\sigma(p^e)<(m+1)(1+p^e)\)이다.
- (R3) \(e\ge2\)이면 \(\sigma(p^e)>1+p^e\)이고,
  \(\sigma(p^e)\equiv1\pmod p\)이다.

소수를 \(p<q<r\)로 정렬하면 경우는 셋이다.

- **경우 B**: \(p\ge3\)(인수 \(2\)가 없음), 2절.
- **경우 \(\{2,3,r\}\)**: \(p=2\), \(q=3\), \(r\ge5\), 3절.
- **경우 A**: \(p=2\), \(5\le q<r\), 4–7절.

## 2. 경우 B: 세 홀수 소수

(R2)에 의해 다음이 성립한다.

1. \(p\ge5\): 각 비율이 \(5/4\)보다 작고 \(125/64<2\)이다.
2. \(p=3\), \(q\ge7\): 이때 \(r\ge11\)이고
   \(\tfrac32\cdot\tfrac76\cdot\tfrac{11}{10}=\tfrac{231}{120}<2\)이다.
3. \(p=3\), \(q=5\), \(r\ge17\):
   \(\tfrac32\cdot\tfrac54\cdot\tfrac{17}{16}=\tfrac{255}{128}<2\)이다.
4. \(p=3\), \(q=5\), \(r\in\{7,11,13\}\): 유한 상자 세 개로 처리한다(7절).

## 3. 경우 \(\{2,3,r\}\)

\(R(2,2)=7/5\), \(R(2,3)=15/9\), \(R(3,2)=13/10\), \(R(3,3)=40/28\),
\(R(3,4)=121/82\)이다. (R1)과 (R3)에 의해 다음이 성립한다.

- \(a\ge3\): 곱은 \(\tfrac{15}{9}\cdot\tfrac{13}{10}=\tfrac{13}{6}\)보다 크고, \(13/6>2\)이다.
- \(a=2\), \(b\ge4\): 곱은 \(\tfrac75\cdot\tfrac{121}{82}=\tfrac{847}{410}\)보다 크고,
  \(847/410>2\)이다.
- \(a=2\), \(b=3\): \(\tfrac75\cdot\tfrac{40}{28}=2\)이므로 \(R(r,c)=1\)이어야
  하는데, 이는 (R3)에 모순이다.
- \(a=2\), \(b=2\): \(91\,\sigma(r^c)=100\,(1+r^c)\)이다. \(r\)을 법으로
  보면 \(\sigma(r^c)\)와 \(1+r^c\)가 모두 \(1\)이므로 \(r\mid9\)이다.
  \(r\ge5\)에서는 불가능하다.

## 4. 경우 A: 정수 방정식과 \(q\)의 범위

\(n=2^aq^br^c\), \(a,b,c\ge2\), \(5\le q<r\)가 소수라 하자. 따라서
\(r\ge q+2\)이다. \(K=\sigma(2^a)=2^{a+1}-1\)로 두면 \(K\)는 홀수이고
\(K\ge7\)이며 \(2(1+2^a)=K+3\)이다. 방정식은

\[
K\,\sigma_q\sigma_r=(K+3)\,u_qu_r \tag{A}
\]

이다. \(p\in\{q,r\}\)에 대해 \(\delta_p=3p-3-K\)(홀수인 정수),
\(W_p=3u_p-Kt_p=3(p+1)+\delta_pt_p\)로 둔다.

**4.1.** (A)는

\[
W_qW_r=K(K+3)\,t_qt_r \tag{A'}
\]

과 동치이다. \(\sigma=u+t\)를 대입하면 (A)는
\(3u_qu_r=K(t_qu_r+u_qt_r+t_qt_r)\)가 된다. 이제
\((3u_q-Kt_q)(3u_r-Kt_r)\)를 전개하면 된다.

**4.2. 양수성.** \(W_q>0\), \(W_r>0\)이다. (A')에 의해 두 값의 부호는
같다. 둘 다 음수라면 \(Kt_qu_r>3u_qu_r\)가 되어 4.1의 식에 모순이다.

**4.3. \(q\)의 범위.**

- (a) \(K\le3q\).
- (b) \(b\ge3\)이면 \(\delta_q\ge1\), 즉 \(K\le3q-4\)이고, 따라서
  \(K(K+3)<9q^2\)이다.
- (c) \(3q\le2K+4\).

(a): \(\delta_q<0\)이면 \(t_q\ge q\)에서 \(0<W_q\le3+3q^2-Kq\)이므로
\(K\le3q\)이다. (b): \(t_q\ge q(q+1)\)에서
\(0<W_q\le(q+1)(3+\delta_qq)\)이므로 \(\delta_q>-3/q\)이다. 따라서
\(\delta_q\ge0\)이고, \(\delta_q\)가 홀수이므로 \(\delta_q\ge1\)이다.
(c): \(\delta_q\le0\)이면 \(3q\le K+3\)이다. 그렇지 않으면
\(\delta_r\ge\delta_q+6>0\)이고, (A')에 \(W_p>\delta_pt_p\)를 쓰면
\(\delta_q(\delta_q+6)\le\delta_q\delta_r<K(K+3)\)이다. 따라서
\(\delta_q<K\), 즉 \(3q<2K+3\)이다.

따라서 \(K/3\le q\le(2K+4)/3\)이고, 각 \(a\)에 대해 가능한 \(q\)는
유한 개뿐이다.

**4.4. 탐색 환원**(8절의 스크립트에서만 쓴다). (A)와
\(\sigma_r=u_r+t_r\)에서 \(u_rW_q=K\sigma_qt_r\)를 얻으므로

\[
\mu_r:=\frac{u_r}{t_r}=\frac{K\sigma_q}{W_q}
\]

이다. \(u_r/t_r=r-1+(r+1)/t_r\)이므로 이 값은 \(c=2\)일 때
\(r+1/r\)이다. \(c\ge3\)일 때는 \((r-1,\,r-1+1/r]\)에 속하고 \(c\)에
대해 감소한다. 서로 다른 홀수 소수 \(r\)에 대한 구간
\((r-1,\,r+1/r]\)는 서로소이므로, \((a,q,b)\)가 정해지면 후보
\((r,c)\)는 많아야 하나이다. 또
\(\mu_r=K\bigl((q+1)+qt_q\bigr)/\bigl(3(q+1)+\delta_qt_q\bigr)\)는
\(t_q\)에 대해 순증가한다(교차항이 \((q+1)(K+3)>0\)). \(\delta_q\)는
홀수이므로 \(\delta_q\ne0\)이다.

- \(\delta_q<0\)이면 \(W_q>0\)인 유한 개의 \(b\)만 보면 된다.
- \(\delta_q>0\)이면 \(\mu_r\)는 \(\mu_\infty=Kq/\delta_q\)로 증가한다.
  \(\mu_r\)가 \(\mu_\infty\)보다 작은 \(u_r/t_r\) 값 중 가장 큰 값을
  넘어서면, 그보다 큰 \(b\)에서는 해가 나올 수 없다.

## 5. 경우 A: 2진 제약

\(p\)를 홀수 소수라 하자.

- \(e\)가 짝수이면 \(\sigma(p^e)\)는 홀수이고 \(1+p^e\equiv2\pmod8\)이다.
- \(e=2m+1\)이면 \(\sigma(p^e)=(1+p)(1+p^2+\dots+p^{2m})\)이고,
  \(1+p^e=(1+p)(1-p+\dots+p^{2m})\)에서 두 번째 인수는 홀수이다.
  \(y\equiv1\pmod4\)이면 \(v_2(1+y+\dots+y^{m})=v_2(m+1)\)이다. 항의
  개수를 반으로 줄이며 귀납하면 된다.

\(\varepsilon(e):=v_2\sigma(p^e)-v_2(1+p^e)\)로 정의하자. 그러면 짝수
\(e\)에 대해 \(\varepsilon(e)=-1\)이고 \(\varepsilon(2m+1)=v_2(m+1)\)이며,
어느 값도 \(p\)에 의존하지 않는다. \(K\)와 \(1+2^a\)는 홀수이므로 원래
방정식 \(\sigma(2^a)\sigma_q\sigma_r=2(1+2^a)u_qu_r\)에서
\(\varepsilon(b)+\varepsilon(c)=1\)을 얻는다. 따라서 다음이 성립한다.

- \(c\)가 짝수이면 \(\varepsilon(b)=2\)이므로 \(b\equiv7\pmod{16}\)이고,
  특히 \(b\ge7\)이다.
- \(c=3\)(\(\varepsilon=1\))이면 \(b\equiv1\pmod4\)이므로 \(b=5\)이거나
  \(b\ge9\)이다.
- \(c=5\)(\(\varepsilon=0\))이면 \(b\equiv3\pmod8\)이므로 \(b=3\)이거나
  \(b\ge11\)이다.

## 6. 경우 A: 크기 부등식과 \(c\)에 따른 경우 나누기

\(\Omega=K(K+3)-\delta_q\delta_r\),
\(H=K(K+3)t_r-\delta_qW_r\), \(G=K(K+3)t_q-\delta_rW_q\)로 두자. (A')와
\(W_p=3(p+1)+\delta_pt_p\)에서

\[
\Omega\,t_qt_r=3(q+1)W_r+3(r+1)\delta_qt_q=3(r+1)W_q+3(q+1)\delta_rt_r,
\tag{I}
\]

\[
Ht_q=3(q+1)W_r,\quad Gt_r=3(r+1)W_q,\quad HG=9(q+1)(r+1)K(K+3),\quad
\Omega t_r=H+3(r+1)\delta_q \tag{II}
\]

를 얻는다. 여기서 다음 세 가지가 따라 나온다.

- \(K(K+3)\)은 짝수이고 \(\delta_q\delta_r\)는 홀수이므로 \(\Omega\)는
  홀수이다. 또 \(\Omega\ge1\)이다. \(\delta_q\ge0\)이거나
  \(\delta_r\ge0\)이면 (I)에서 바로 나오고, 둘 다 음수이면
  \(0<-\delta_p<K\)이므로 \(\delta_q\delta_r<K^2\)이다.
- (II)와 4.2에 의해 \(H\)와 \(G\)는 양의 정수이다. 따라서
  \(t_q\le3(q+1)W_r\)이고 \(t_r\le\Omega t_r\le HG+3(r+1)\delta_q\),
  즉
  \[
  t_r\le9(q+1)(r+1)K(K+3)+3(r+1)\delta_q \tag{M}
  \]
  이다.
- \(W_q>\delta_qt_q\)이므로 (A')에서
  \(\delta_qW_r<K(K+3)\,t_r\)이다. \(\quad\)(D)

이제 \(b\)에 대해서는 5절을 쓰면서 \(c\)에 따라 나눈다.

**\(c\ge7\).** 이때 \(t_r\ge r^6\)이다. (M)에 \(q+1\le r-1\),
\(K\le3q\le3r-6\), \(\delta_q<3r\)를 쓰면 \(r^6<81r^4+9r(r+1)\)이므로
\(r\le9\)이다. 그러면 \(r=7\), \(q=5\)이고 \(K\le15\)이므로
\(a\in\{2,3\}\)이다. 이 경우들은 상자로 처리한다(7절).

**\(c\in\{4,6\}\).** 이때 \(b\ge7\)이므로
\(t_q\ge q^6\ge\frac{2700}{26}(q+1)q^2\)이다. (I)과 \(\Omega\ge1\)에서
\(t_qt_r\le3(q+1)W_r+3(r+1)\delta_qt_q\)이다. (D)와 4.3(b)에서
\(W_r\le\delta_qW_r<9q^2t_r\)이므로
\(3(q+1)W_r<27(q+1)q^2t_r\le0.26\,t_qt_r\)이다. 따라서

\[
74\,t_r<300(r+1)\delta_q<900\,r(r+1) \tag{C}
\]

이다. \(t_r\ge r+r^2+r^3\)을 쓰면 \(r\le12\), 즉 \(r\in\{7,11\}\)이다.
범위 \(K+4\le3q\le2K+4\)를 적용하면
\((a,q,r)\in\{(2,5,7),(2,5,11),(3,7,11)\}\)만 남고, 이들은 상자로
처리한다.

**\(c=5\).** \(b\ge11\)이면 \(t_r\ge r^4\)과 (C)가 양립할 수 없다.
\(b=3\)이면 \(t_q=q(q+1)\)이고, (I)의 두 번째 식은
\(M=q\Omega-3\delta_r\)에 대해 \((q+1)t_r\,M=3(r+1)W_q\)가 된다. 여기서
\(M\)은 양의 짝수이고 \(W_q=(q+1)(3+\delta_qq)\)이다. 따라서
\(2t_r\le3(r+1)(3+\delta_qq)<9r^2(r+1)\)인데, 이는
\(t_r=r+r^2+r^3+r^4\)에 모순이다.

**\(c=2\).** 이때 \(b\ge7\)이고 \(t_r=r\)이다. (I)의 첫 번째 식에서
\(J=\Omega-3\delta_q\)에 대해 \(J\,t_qr=3(q+1)W_r+3\delta_qt_q\)이고,
\(J\)는 양의 짝수이다. 따라서
\(2t_qr\le3(q+1)W_r+3\delta_qt_q\)이다. \(c\in\{4,6\}\)인 경우와
마찬가지로 \(3(q+1)W_r<0.26\,t_qr\)이므로
\(r<\frac{50}{29}\delta_q\)이다. \(t_q\le3(q+1)W_r\)와 (D)를 합치면
\(\delta_qt_q<3(q+1)K(K+3)\,r<\frac{150}{29}(q+1)K(K+3)\,\delta_q\)이다.
따라서 \(t_q<47(q+1)q^2\)인데, 이는 \(t_q\ge q^6\)에 모순이다.

**\(c=3\).** 이때 \(t_r=r(r+1)\), \(W_r=(r+1)(3+r\delta_r)\)이다. (I)의
첫 번째 식은 \(L=r\Omega-3\delta_q\)에 대해
\(L\,t_q=3(q+1)(3+r\delta_r)\)가 되고 \(L\)은 양의 짝수이다. 따라서

\[
2t_q\le3(q+1)(3+r\delta_r) \tag{L}
\]

이다.

- \(b\ge9\). \(\Omega\ge1\)이고 \(\delta_q\ge1\)이므로
  \(\delta_r<K(K+3)<9q^2\)이다. 또
  \(3r=\delta_r+3+K<(K+2)^2\le(3q-2)^2\)이므로 \(r<3q^2\)이다. 그러면
  (L)에서 \(2t_q<3(q+1)(3+27q^4)\)인데, 이는 \(t_q\ge q^8\)에 모순이다.
- \(b=5\). 이때 \(P=q^3+q\)에 대해 \(t_q=(q+1)P\)이고
  \(W_q=(q+1)(3+\delta_qP)\)이다. 따라서 (A')는 이차방정식

  \[
  (3+\delta_qP)(3+r\delta_r)=K(K+3)\,P\,r \tag{Q}
  \]

  로 줄어든다. \(A=3+\delta_qP\), \(E=3+r\delta_r\), \(M=K(K+3)\)라
  쓰자. (L)은 \(LP=3E\)이므로 \(2P\le3E\)이다. 또 (I)에서
  \(\Omega\ge1\)을 쓰면 \(Pr\le3E+3\delta_qP\)이다. 두 부등식에 \(A\)를
  곱하고 \(AE=MPr\)를 쓰면 \(2A\le3Mr\)와 \(rA\le3Mr+3\delta_qA\)를
  얻는다.

  \(2P\ge15M\)이라 가정하자. 그러면 \(A-3M>0\)이다.
  \(r(A-3M)\le3\delta_qA\)와 \(2A\le3Mr\)를 합치면
  \(2(A-3M)\le9M\delta_q\)이다. 따라서
  \(2\delta_qP<9M\delta_q+6M\le15M\delta_q\), 즉 \(2P<15M\)이 되어
  모순이다. 그러므로

  \[
  2(q^3+q)<15\,K(K+3)
  \]

  이다. \(K\le3q-4\)와 합치면 \(q\le67\)이고, 따라서 \(a\le6\)이다.
  범위 조건까지 적용하면 \(q\)가 홀수인 쌍 \((a,q)\) 16개가 남는다(7절).

## 7. 유한 검사

**상자.** 각 상자에서는 세 소수를 고정하고, 지수는 구간(일부는 위로
유계가 아님)을 움직인다. (R1)과 극한값 \(p/(p-1)\)을 써서 지수 범위를
잘게 나누면, 모든 조각에서 하한만으로 곱이 \(2\)보다 커지거나 상한만으로
곱이 \(2\)보다 작아진다. 상자는 모두 여덟 개이다.

| 소수 | 지수 | 출처 |
|---|---|---|
| \(3,5,7\) | \(a,b,c\ge2\) | 경우 B |
| \(3,5,11\) | \(a,b,c\ge2\) | 경우 B |
| \(3,5,13\) | \(a,b,c\ge2\) | 경우 B |
| \(2,5,7\) | \(a=2\), \(b\ge2\), \(c\ge7\) | 경우 A, \(c\ge7\) |
| \(2,5,7\) | \(a=3\), \(b,c\ge2\) | 경우 A, \(c\ge7\) |
| \(2,5,7\) | \(a=2\), \(b\ge7\), \(c\ge4\) | 경우 A, \(c\in\{4,6\}\) |
| \(2,5,11\) | \(a=2\), \(b,c\ge2\) | 경우 A, \(c\in\{4,6\}\) |
| \(2,7,11\) | \(a=3\), \(b,c\ge2\) | 경우 A, \(c\in\{4,6\}\) |

**이차방정식 (Q).** \((a,q)\)를 고정하면 (Q)는 \(B=A(K+3)+MP\)에 대해
\(3Ar^2-Br+3A=0\)이다. 두 근의 곱이 \(1\)이므로 \(r>1\)인 근은
\(r=B/(3A)-1/r\)를 만족한다. \(3A\nmid B\)이면 가능한 정수근은
\(r_0=\lfloor B/(3A)\rfloor\) 하나뿐이다.
\(K+4\le3q\le2K+4\)와 \(2(q^3+q)<15K(K+3)\)를 만족하는 16개의 쌍(\(q\)는
홀수이며 소수일 필요는 없다)을 아래에 적었다. 모든 경우에 \(3A\nmid B\)이고
\(r_0\)는 (Q)의 근이 아니다(\(q=11\)에서는 \(r_0<q+2\)이기도 하다).

| \(a\) | \(K\) | \(q\) 값 | \(r_0\) |
|---|---|---|---|
| 2 | 7 | 5 | 7 |
| 3 | 15 | 7, 9, 11 | 35, 15, 11 |
| 4 | 31 | 13, 15, 17, 19 | 81, 43, 31, 26 |
| 5 | 63 | 23, 25, 27, 29, 31 | 483, 175, 114, 87, 73 |
| 6 | 127 | 45, 47, 49 | 1143, 543, 367 |

## 8. 계산 교차 검증

서로 독립적인 두 정확 탐색(둘 다 표준 라이브러리만 쓰는 Python)이
\(2\)부터 `AMAX`까지의 모든 \(a\)와 모든 \(q,b,r,c\)에 대해 경우 A를
조사한다. 두 탐색은 4.4의 환원에 의존하고, 첫 번째 탐색은 4.3의 범위에도
의존한다. 5–7절은 쓰지 않는다. 두 탐색 모두 탐색에 앞서 인위적으로 심어
둔 해를 다시 찾아내는지 자체 시험한다.

- [`three_prime_search.py`](three_prime_search.py)는
  `fractions.Fraction`으로 정확히 계산한다. 경우 B와 경우
  \(\{2,3,r\}\)도 중첩 단조 부등식으로 다시 확인한다.
- [`three_prime_search_int.py`](three_prime_search_int.py)는 정수만
  쓰고, \(r\)을 다른 방식으로 읽어 내며, 더 넓은 범위
  \(\max(3,\lfloor K/3\rfloor-6)\le q\le K+6\)를 조사한다.

두 탐색 모두 \(2\le a\le28\)에서 해를 찾지 못했다. 이 탐색은 그 범위에서
Lean으로 증명한 명제와의 일관성 확인일 뿐 증명의 일부가 아니다. 개발
기기에서 잰 실행 시간은 다음과 같다.

| 명령(이 폴더에서 실행) | 시간 |
|---|---|
| `python3 three_prime_search.py --amax 22` | 4.0초 |
| `python3 three_prime_search_int.py --amax 22` | 8.3초 |
| `python3 three_prime_search.py --amax 28` | 5분 06초(기기 부하 상태) |
| `python3 three_prime_search_int.py --amax 28` | 16분 08초(기기 부하 상태) |

## 9. Lean 형식화

위 내용은 모두
[`AgenticConjectures/OeisA063880.lean`](../../AgenticConjectures/OeisA063880.lean)의
*Three-prime cores* 절에 있다. 주요 선언은 다음과 같다.

| 선언 | 내용 |
|---|---|
| `not_a_three_prime_pow` | 위 정리(상류 술어 `A`에 대해) |
| `three_prime_sorted`, `caseB`, `case23`, `caseA` | 1절의 경우 나누기와 세 경우 |
| `two_adic_rel`, `caseA_two_adic` | 5절 |
| `caseA_pos`, `caseA_K_le`, `caseA_K_le'`, `caseA_range` | 4.2, 4.3 |
| `caseA_Om`, `caseA_H`, `caseA_dWr`, `caseA_KK` | 6절: (I), 홀수 \(\Omega\ge1\), \(t_q\le3(q+1)W_r\), (D), \(K(K+3)<9q^2\) |
| `caseA_c7`, `caseA_c46`, `caseA_c2`, `caseA_c5b`, `caseA_c3a`, `caseA_c3b` | \(c\ge7\), (C), \(c=2\), \(c=5\), \(c=3\)인 경우 |
| `quad_root`, `caseA_c3b_finite` | 7절의 표 |
| `box_3_5_7`, `box_3_5_11`, `box_3_5_13`, `box_2_5_7_c7`, `box_2_5_7_a3`, `box_2_5_7_b7`, `box_2_5_11`, `box_2_7_11` | 상자 여덟 개 |
| `eq_108_of_powerful_of_card_le_three` | 소인수가 세 개 이하인 powerful 해는 \(108\)이다 |
| `exists_eq_108_mul_of_card_le_three` | `A n`이고 \(p^2\mid n\)인 소수 \(p\)가 세 개 이하이면 `n = 108 * s`이고 `s`는 squarefree이며 \(108\)과 서로소이다 |
| `mod_216_of_card_le_three`, `eq_108_of_isPrimitiveTerm_of_card_le_three` | \(\omega(C(n))\le3\)에 대한 두 따름정리 |

본문과 표현상 다른 점은 다음과 같다. Lean에서 \(t_p\)는
\(\sigma(p^e)-1-p^e\)이고 \((p-1)t_p=p^e-p\)로 특징지어지며(`t_key`),
경우 A는 \(\mathbb Z\) 위에서 논증한다. 상자와 표는 `norm_num`,
`interval_cases`, `omega`로 검사한다(`decide`나 `native_decide`는 쓰지
않는다). 또 `exists_eq_108_mul_of_card_le_two`의 squarefree 부분 귀납법을
임의의 상한 \(k\)에 대해 다시 진술했으며(`exists_eq_108_mul_of_card_le`),
기존 정리는 바꾸지 않았다.

## 10. 주장하지 않는 것

- 서로 다른 소수를 네 개 이상 가진 core는 다루지 않는다. OEIS 항목의
  두 추측(유일한 primitive 항, 모든 항이 \(108\pmod{216}\))은 여전히
  미해결이다.
- primitive 항을 \(10^{18}\)까지 조사한 OEIS의 탐색은 다시 실행하지
  않았다.
- 새로움은 주장하지 않는다.
