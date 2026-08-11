[English](README.md) | **한국어**

# OEIS A394666 — `n! mod (2n-1)`의 영인 항

## 원문 명제

오프셋이 1인 [OEIS A394666](https://oeis.org/A394666)은 다음과 같이
정의됩니다.

\[
a(n)=n!\bmod(2n-1).
\]

리비전 #38에는 다음 주석이 기록되어 있습니다.

> “Conjecturally, a(n) = 0 iff n > 5 and 2*n - 1 is not a prime.”

따라서 의도된 꼬리 명제는 모든 $n>5$에 대해 나머지가 0인 것과
$2n-1$이 합성수인 것이 동치라는 주장입니다.

## 결과

추측된 꼬리 분류는 참입니다.

\[
n!\bmod(2n-1)=0
\quad\Longleftrightarrow\quad
2n-1\text{은 합성수}
\qquad(n>5).
\]

원문의 문장을 제한 없는 동치로 읽으면 표에 있는 첫 값 $a(1)=0$을
빠뜨립니다. 양의 인덱스 전체에 대한 정확한 분류는

\[
a(n)=0
\quad\Longleftrightarrow\quad
n=1\quad\text{이거나}\quad
\bigl(n>5\text{이고 }2n-1\text{이 합성수}\bigr)
\]

입니다. mathlib 기반 Lean 4 모듈의
[`a_eq_zero_iff_not_prime`](../../AgenticConjectures/OeisA394666.lean)와
`zero_classification`이 두 명제를 미증명 자리표시자나 커널 밖 계산 없이
증명합니다.

## 증명

$m=2n-1$이라 둡니다.

$m$이 소수이고 $a(n)=0$이라면 $m\mid n!$입니다. $n!$의 모든 소수
약수는 $n$ 이하이지만 $n>1$에서 $m=2n-1>n$이므로 모순입니다.

반대로 $n>5$이고 $m$이 합성수라고 하겠습니다. $m=uv$, $u,v>1$로
씁니다. $m$이 홀수이므로 두 인수도 홀수이고 $u,v\ge3$입니다.
$u=v=3$이면 $m=9$, $n=5$가 되어 범위에서 제외됩니다. 따라서
$u=3$, $v\ge5$이거나 $u\ge5$, $v\ge3$이고, 두 경우 모두

\[
(u-2)(v-2)\ge3
\]

입니다. 그러므로 $2(u+v)\le uv+1=2n$, 즉 $u+v\le n$입니다. 이제

\[
2n-1=uv\mid u!v!\mid(u+v)!\mid n!
\]

이므로 나머지는 0입니다. Lean 커널이 $n=1,\ldots,5$의 값을 직접
계산하면 $(0,2,1,3,3)$이며, 이로써 보정된 전체 분류도 성립합니다.

## 명제 충실성

- 형식 수열은 `Nat.factorial`과 `Nat.mod`를 사용하여 OEIS의 팩토리얼과
  최소 비음수 나머지를 그대로 나타냅니다.
- OEIS 오프셋은 1입니다. 정의 자체는 모든 자연수에서 전함수이지만,
  등록된 명제는 모두 양의 인덱스에 관한 것입니다.
- 주장한 범위에서는 `2*n-1`의 자연수 뺄셈이 통상적인 정수 뺄셈과
  같습니다.
- `a_eq_zero_iff_not_prime`은 원문 주석을 일관되게 $n>5$의 꼬리
  명제로 형식화합니다. 추가 정리 `zero_classification`은 원문의 첫 예외
  $a(1)=0$을 숨기지 않고 기록합니다.
- 이 수열에는 Formal Conjectures Lean 스냅샷이 없습니다. 정의, 오프셋,
  값, 인용문은 2026년 8월 12일에 OEIS 리비전 #38과 직접 대조했습니다.

## 재현

저장소 루트에서 다음을 실행합니다.

```bash
lake env lean AgenticConjectures/OeisA394666.lean
lake build
python3 scripts/check_axioms.py
```

개발 환경에서 모듈 단독 검사는 약 17초 걸립니다. 전체 저장소 게이트는
두 등록 정리에 대해 미증명 자리표시자 검사와 커널 공리 감사도 수행합니다.

## 연구 상태와 선행 결과

2026년 8월 12일 현재, 2026년 5월 5일에 마지막으로 수정된 OEIS 리비전
#38은 이 분류를 여전히 추측으로 표시하며 참고문헌을 싣지 않습니다. 수열과
식을 정확히 사용해 공개 웹, arXiv, GitHub를 검색한 결과 JOEIS, LODA,
OEIS-Python의 수열 구현은 찾았지만 독립적인 증명은 찾지 못했습니다. 이
부정적 검색은 신규성의 근거가 아닙니다.

이 증명은 검토되지 않았고 OEIS 편집자의 확인을 받지 않았으며, OEIS나
다른 외부 채널에 제출하지 않았습니다.
