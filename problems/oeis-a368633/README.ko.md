[English](README.md) | **한국어**

# OEIS A368633 — 홀짝성 추측

## 판정

추측은 참이다. 즉,

\[
A(x)=\sum_{n\geq 0}a_nx^n
\quad\text{이고}\quad
A(x)=1+2xA(x)^2-xA(-x)^2
\]

이면

\[
a_n\text{이 홀수}\quad\Longleftrightarrow\quad
n+1\text{이 2의 거듭제곱}
\]

이다.

OEIS에 적힌 추측 원문은 다음과 같다.

> “Conjecture: a(n) is odd when n = 2^k - 1 for k >= 0 and even elsewhere.”

2026-08-12에 정식 [OEIS A368633](https://oeis.org/A368633) revision 26과
대조했다. 이 수열의 offset은 0이다.

## 증명

다음과 같이 놓자.

\[
b_m=[x^m]A(x)^2=\sum_{i=0}^{m}a_i a_{m-i}.
\]

\([x^m]A(-x)^2\)에 기여하는 모든 항의 전체 부호는
\((-1)^{i+m-i}=(-1)^m\)이므로

\[
[x^m]A(-x)^2=(-1)^m b_m.
\]

상수항은 \(a_0=1\)이다. \(n\geq1\)일 때 정의식의 계수를 비교하면 다음의
정확한 점화식을 얻는다.

\[
a_n=\bigl(2-(-1)^{n-1}\bigr)
    \sum_{i=0}^{n-1}a_i a_{n-1-i}
=
\begin{cases}
\displaystyle\sum_{i=0}^{n-1}a_i a_{n-1-i},&n\text{이 홀수},\\[6pt]
\displaystyle3\sum_{i=0}^{n-1}a_i a_{n-1-i},&n\text{이 짝수}.
\end{cases}
\]

이 점화식으로 형식적 멱급수 해의 유일성도 알 수 있다. 두 경우의 계수
1과 3은 모두 홀수다. 따라서 \(p_n=a_n\bmod2\)라 놓으면

\[
p_0=1,
\qquad
p_n=\sum_{i=0}^{n-1}p_i p_{n-1-i}\pmod2.
\]

이는 2를 법으로 한 Catalan 점화식이다. 이를 바로 분류할 수도 있다.
\(n>0\)이 짝수이면 모든 항이 \(i\leftrightarrow n-1-i\)로 짝지어져
\(p_n=0\)이다. \(n=2r+1\)이면 같은 방식으로 가운데 항을 제외한 항들이
소거되므로 \(p_{2r+1}=p_r^2=p_r\)이다. 따라서 \(k=0\)일 때의
\(p_0=1\)을 포함하여 귀납적으로

\[
p_n=1
\Longleftrightarrow
n=2r+1\text{이고 }p_r=1
\Longleftrightarrow
n=2^k-1.
\]

즉 \(n+1\)이 2의 거듭제곱인 경우와 정확히 일치한다.

이는 Catalan 수열([OEIS A000108](https://oeis.org/A000108))의 고전적인
홀짝성 분류와 정확히 같다. 논증은 이 표준 결과로 직접 환원되므로 신규성이나
우선권을 주장하지 않는다.

## 기계 검증

[`a368633_certificate.py`](a368633_certificate.py)는 Python 표준
라이브러리만 사용한다. 함수 방정식의 부호 있는 두 Cauchy 곱으로부터 계수를
직접 만드는 구현과 위에서 단순화한 정확한 점화식 구현을 독립적으로 실행한다.
그 뒤 다음을 확인한다.

- 두 구현이 \(n=600\)까지 일치함;
- 정식 OEIS JSON `data` 필드에 \(n=0,\ldots,24\)로 공개된 25개 값을
  정확히 모두 재현함;
- \(n=600\)까지 계수의 홀짝성이 독립적인 Catalan 닫힌꼴
  \(C_n=\binom{2n}{n}/(n+1)\) 및 2의 거듭제곱 분류와 모두 일치함.

저장소 루트에서 다음을 실행한다.

```bash
python3 problems/oeis-a368633/a368633_certificate.py
```

2026-08-12 반복 실행 시간은 0.3–0.7초였다. 유한 검사는 구현과 원문 전사를
뒷받침하며, 모든 \(n\)에 대한 주장은 위 증명과 Lean 정리가 담당한다.

## 명제 충실성과 Lean 범위

Lean 정의는 정수 계수 형식적 멱급수 위에서 위 방정식을 직접 표현하며,
\(A(-x)\)에는 `PowerSeries.rescale (-1) A`를 사용한다. 정리는 이 방정식을
만족하는 모든 정수 계수 형식적 멱급수를 대상으로 하므로 OEIS 수열에 적용되며,
원문의 비음수 계수 서술보다 조금 더 강하다. 또한 자연수 \(k\)에 대해
\(n+1=2^k\)라는 동치인 뺄셈 없는 조건을 사용한다. 따라서 OEIS의 offset-0
표현 \(n=2^k-1\)과 차이가 없고 경계값이나 자연수 뺄셈 때문에 빠지는 경우도
없다. “홀수”는 정수의 홀짝성을 뜻한다.

이 문제는 OEIS에서 직접 수집했다. 이 문제 디렉터리에는 상류 Lean 스냅샷이
없으며, 새 형식화는 위의 정식 OEIS 명제와 직접 대조했다.
