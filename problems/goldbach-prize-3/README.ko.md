[English](README.md) | **한국어**

# ‘골드바흐를 증명하자’ 상금 문제 3

공식 [상금 페이지](https://www.dimostriamogoldbach.it/en/prizes/)는
2026-08-12 조회 시 문제 3에 **€200**, 상태 **“No solutions received”**를
표시하고 있었다. 고정된 정수 (1<n_1<n_2<\cdots<n_k)에 대해 다음 집합을
정의한다.

\[
S=\{y>0:n_i\nmid y\text{ for every }i,\quad n_1\mid y+1\}
\]

그리고 다음과 같이 요구한다.

> “It is required to prove that this set can be expressed as”

\[
 S=\{f(x):g(x)\in
 \{n_2a_2+\cdots+n_ka_k:a_i\in I_i\}\}.
\]

(f,g:\mathbb N^\star\to\mathbb N)에는 산술, 나머지, 올림·내림, 유한한
경우 구분을 사용할 수 있고, 각 (I_i)에는 양의 정수의 유한 부분집합이라는
조건만 붙어 있다.

## 결과

게시된 표현은 항상 존재한다. 다음과 같이 둔다.

\[
 M=\prod_{j=2}^k n_j,qquad
 C=\sum_{j=3}^k n_j,qquad
 \rho(q)=1+((q-1)\bmod M).
\]

그러면 (1\leq\rho(q)\leq M)이다. 이제

\[
\begin{aligned}
 I_2&=\{r\in\{1,\ldots,M\}:n_j\nmid n_1r-1
       \text{ for every }j=2,\ldots,k\},\\
 I_j&=\{1\}\quad(3\leq j\leq k),\\
 f(q)&=n_1q-1,\\
 g(q)&=n_2\rho(q)+C
\end{aligned}
\]

로 택한다. (I_2)는 정의상 양의 유한집합이고 나머지는 양의 한원소집합이다.
이들의 유한 합집합은 정확히 다음과 같다.

\[
  \{n_2r+C:r\in I_2\}.
\]

모든 (q>0)에 대해 (q\equiv\rho(q)\pmod M)이다. (j\geq2)인 각
(n_j)가 (M)을 나누므로

\[
 n_j\mid n_1q-1\quad\Longleftrightarrow\quad
 n_j\mid n_1\rho(q)-1
\]

이다. 따라서 (g(q))가 유한 합집합에 속하는 것과 (f(q))가
(n_2,\ldots,n_k) 모두로 나누어지지 않는 것은 동치다. 또한
(f(q)+1=n_1q)이고 (f(q))는 양수이며 (n_1)로 나누어지지 않는다.
이로써 양방향 집합 등식이 증명된다. (k=2)인 경우도 (C=0)으로 포함된다.

## 명제 충실성과 범위

Lean의 리스트 `ns`는 정확히 ([n_2,\ldots,n_k])이다. 머리는 (n_2), 꼬리의
합은 (C), 리스트의 곱은 (M)을 나타낸다. 형식화된 목표에는 양수 조건,
(n_1)과 `ns`의 모든 원소에 대한 비가분성, (n_1\mid y+1)이 모두 포함된다.
정리는 실제로 필요한 더 약한 조건, 즉 (n_1>1), 리스트가 비어 있지 않음,
뒤의 모든 법이 (1)보다 큼만 가정한다. 따라서 원문의 엄격한 증가열은 이
정리의 특수한 경우다.

중요한 명세상 단서가 있다. 게시된 문구에는 (|I_i|)의 상한, 그 상한이
매개변수와 독립적이어야 한다는 조건, 유한집합의 원소 판정에 대한 별도의
공식 언어 제한이 없다. 이 구성은 그 자유를 사용해 한 주기 전체를 (I_2)에
저장한다. 출제자가 균일하게 작은 집합이나 더 제한된 닫힌형을 의도했다면,
그것은 게시문에 없는 조건을 추가한 더 강한 문제다. 이 저장소는 위의 문언상
명제만 증명했다고 주장한다.

## 기계 검증

`sorry` 없는 모듈
[`GoldbachPrize3.lean`](../../AgenticConjectures/GoldbachPrize3.lean)은 다음을
증명한다.

- `residueSet_finite`: 선택한 (I_2)가 유한함
- `proved`: 재사용 보조정리 `representation`을 통한 모든 허용 매개변수의
  정확한 양방향 집합 등식

```bash
lake env lean AgenticConjectures/GoldbachPrize3.lean
```

증명 구조와 신뢰 경계는 [DETAILS.ko.md](DETAILS.ko.md)에 정리했다.

## 연구 상태

게시된 정확한 표현과 핵심 문구를 대상으로 2026-08-12에 검색했으나 공식
상금 페이지 밖의 공개 해답을 찾지 못했다.

이 구성은 상금 제공자의 검토나 승인을 아직 받지 않았다. 따라서 이 저장소는
상금, 신규성, 우선권을 주장하지 않는다. 사람의 승인이 필요한 외부 제출도
하지 않았다.
