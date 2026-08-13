[English](README.md) | **한국어**

# ‘골드바흐를 증명하자’ 상금 문제 2

공식 [상금 페이지](https://www.dimostriamogoldbach.it/en/prizes/)는 문제
2에 **€100**를 걸고 있다. 2026-08-12에 표시된 상태는
**“No solutions received”**였고, 2026-08-13에는
**“Solution under review”**로 표시되었다. 이 페이지에는 제출자의 신원이나
제출된 해답의 내용이 공개되어 있지 않다.

고정된 정수 \(1<n_1<n_2<n_3\)에 대해
\(\mathrm{t\_space}_{(n_1,n_2,n_3)}(x)\)를
\(n_1,n_2,n_3\) 어느 것으로도 나누어지지 않는 \(x\)번째 양의 정수라 하자.
게시된 문제는 다음을 만족하는 유한 경우 공식 \(f\)를 요구한다.

\[
 \left|f(x)-\mathrm{t\_space}_{(n_1,n_2,n_3)}(x)\right|
 \leq \frac{n_3^2}{2}
 \qquad(x>0).
\]

원문의 공식 언어 조건은 다음과 같이 적혀 있다.

> “includes only operators of sum, difference, product, division and
> distinction between a finite number of cases.”

## 결과

오차가 0인 정확한 주기 공식이 존재한다. 다음과 같이 둔다.

\[
 P=n_1n_2n_3.
\]

반열린 한 주기 안의 허용 잔여를 증가하는 순서로 나열한다.

\[
 R=(r_0,r_1,\ldots,r_{A-1})
   =\operatorname{sort}\{r:0\leq r<P,\ r>0,\
       n_1\nmid r,\ n_2\nmid r,\ n_3\nmid r\}.
\]

\(r=1\)이 허용되므로 이 리스트는 비어 있지 않다. \(x>0\)에 대해

\[
 m=x-1,\qquad q=\left\lfloor\frac mA\right\rfloor,\qquad
 j=m-Aq=m\bmod A
\]

로 놓으면

\[
 f(x)=Pq+r_j \tag{1}
\]

이다. 각 가분성 조건의 주기는 \(P\)이므로 허용되는 양의 정수의 증가
순서열은 정확히

\[
 r_0,\ldots,r_{A-1},\quad
 P+r_0,\ldots,P+r_{A-1},\quad
 2P+r_0,\ldots
\]

이다. 공식 (1)은 이 순서열의 요구된 원소를 선택한다. 따라서 모든 양의
\(x\)에 대해

\[
 f(x)=\mathrm{t\_space}_{(n_1,n_2,n_3)}(x)
\]

이고, 이는 요구된 근사 부등식보다 강하다.

## 명제 충실성과 유한 경우 단서

형식화된 `Allowed` 술어는 양수 조건과 세 법 각각에 대한 비가분성의
논리곱으로, 원문의 `t_space` 설명과 정확히 일치한다. 최소공배수 대신 곱
\(P\)를 쓴 이유는 편리한 공통 주기를 얻기 위해서일 뿐이다. 원문의
제곱의 절반 오차 한계는 분수를 피하여

\[
 2\,\operatorname{dist}(f(x),\mathrm{t\_space}(x))\leq n_3^2
\]

로 형식화했으며, 자연수 값을 대상으로 두 표현은 동치다.

수학적 증명만으로 정할 수 없는 명세 문제가 하나 있다. 각 고정된 삼중항에
대해 공식 (1)은 유한표 \(r_0,\ldots,r_{A-1}\)를 사용하는 몫 공식이므로
유한한 경우 구분이다. 나머지도
\(m-A\lfloor m/A\rfloor\)로 써서 차, 곱, 정수 나눗셈만으로 표현할 수
있다. 그러나 잔여 경우의 수와 내용은 \(n_1,n_2,n_3\)에 의존한다. 상금
페이지는 “유한한 수의 경우”가 고정된 매개변수에 따라 달라도 되는지, 아니면
매개변수와 독립적인 하나의 문법적 상한을 의도하여 생성된 조회표를 금지하는지
명시하지 않는다.

Lean의 `statement` 명제는 이 비형식적 공식 언어 제한을 표현하지 못한다.
Lean이 검증하는 것은 명시적으로 계산 가능한 잔여 리스트 정의와 부등식이다.
따라서 이 저장소는 각 고정 삼중항별 유한 경우라는 문언상 해석 아래에서의
증명을 기록한다. 더 엄격한 균일 닫힌형 해석은 아직 형식화되지 않은 별개의
명세다.

## 기계 검증

`sorry` 없는 모듈
[`GoldbachPrize2.lean`](../../AgenticConjectures/GoldbachPrize2.lean)은 다음을
증명한다.

- `exact_formula0`: 0부터 세는 잔여 공식이 허용 술어의 `Nat.nth`와 같음
- `exact_formula`: 원문의 1부터 세는 `formula`가 `tSpace`와 같음
- `proved`: 모든 허용 삼중항과 모든 양의 지표에 대해 거리가 0이므로 게시된
  오차 한계가 성립함

```bash
lake env lean AgenticConjectures/GoldbachPrize2.lean
```

증명 구조와 신뢰 경계는 [DETAILS.ko.md](DETAILS.ko.md)에 정리했다.

## 상금 및 연구 상태

2026-08-13의 **“Solution under review”**라는 문구는 승인이나 상금 지급을
뜻하지 않는다. 공식 페이지에 제출자나 해답의 세부사항이 없으므로, 이
저장소는 누가 제출했는지 또는 그 제출이 여기의 구성과 관련 있는지 추론하지
않는다.

이 형식화는 상금 제공자의 승인이나 검토를 받지 않았다. 신규성이나 우선권도
주장하지 않으며, 이 저장소에서 외부 제출을 하지 않았다. 외부 제출에는
사람의 승인이 필요하다.
