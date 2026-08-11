[English](README.md) | **한국어**

# OEIS A113249 — 전체 매개변수 족의 홀수 번째 항은 제곱수

## 원문 명제

[OEIS A113249](https://oeis.org/A113249)
[개정판 #29](https://oeis.org/history/view?seq=A113249&v=29)는 다음 4차
점화식 족을 정의한다.

\[
a_m(r)=m^4a_m(r-4)+(2m)^2a_m(r-3)-4a_m(r-1) \qquad (r\ge4)
\]

초기값은 다음과 같다.

\[
\begin{aligned}
a_m(0)&=-1, & a_m(1)&=4,\\
a_m(2)&=-13+6(m-1)+3(m-1)^2, &
a_m(3)&=(-8+m^2)^2.
\end{aligned}
\]

원문의 정확한 추측 문장은 다음과 같다.

> Conjecture: a(m, 2*n+1) is a perfect square for all m, n.

OEIS 항목 자체는 이 족에서 $m=3$인 행이며 오프셋은 0이다.

## 결과

추측은 참이다. 더 강하게, 임의의 정수 매개변수 $m$과 $n ≥ 0$에 대해

\[
Y_m(0)=2,\qquad Y_m(1)=8-m^2,\qquad
Y_m(n+2)=4Y_m(n+1)-m^2Y_m(n)
\]

으로 정의하면 다음 항등식이 성립한다.

\[
\boxed{a_m(2n+1)=Y_m(n)^2.}
\]

Lean 4 정리
[`odd_term_eq_aux_square`](../../AgenticConjectures/OeisA113249.lean)는 모든
$m ∈ ℤ$에 대해 이 항등식을 증명한다. 등록된 정리
`oeis_a113249_conjecture`는 원문의 자연수 매개변수 해석을 제시하고 정수
제곱근을 명시한다. 두 증명 모두 `sorry`, 추가 공리, `native_decide`를
사용하지 않는다.

## 증명

원래 점화식을 다음과 같이 0형으로 쓴다.

\[
R_k:\quad
a_m(k+4)+4a_m(k+3)-4m^2a_m(k+1)-m^4a_m(k)=0.
\]

선형결합 $R_{k+2}-4R_{k+1}+m^2R_k$을 취하면 홀수 간격의 항들이
소거되어 다음 6단계 관계를 얻는다.

\[
\begin{aligned}
a_m(k+6)={}&(16-m^2)a_m(k+4)
 +m^2(m^2-16)a_m(k+2)+m^6a_m(k).
\end{aligned}
\]

보조 수열의 제곱도 정확히 같은 점화식을 따른다. $A=Y_m(n+1)$,
$B=Y_m(n)$라 두면 Lean의 `ring` 전술이 다음 다항식 항등식을 검증한다.

\[
\begin{aligned}
\bigl(4(4A-m^2B)-m^2A\bigr)^2
={}&(16-m^2)(4A-m^2B)^2\\
&+m^2(m^2-16)A^2+m^6B^2.
\end{aligned}
\]

원문의 초기값을 직접 전개하면

\[
a_m(1)=Y_m(0)^2,\qquad
a_m(3)=Y_m(1)^2,\qquad
a_m(5)=Y_m(2)^2
\]

를 얻는다. 같은 점화식을 이용한 세 항 창 귀납법으로 모든 $n$에 대해
상자의 항등식을 증명한다.

## 명제 충실성

- Lean 정의는 네 초기값과 원문 점화식을 그대로 옮기되 `n+4` 번째 항을
  전방으로 정의한다. 따라서 자연수의 잘린 뺄셈을 쓰지 않는다.
- 이 족에는 음수인 짝수 번째 항이 있으므로 수열값과 일반 매개변수를
  `ℤ`로 표현한다. OEIS의 “모든 m, n”은 정의역을 명시하지 않는다. 등록된
  자연수 매개변수 해석은 `m n : ℕ`을 양화하고 `m`을 `ℤ`로 변환한다.
  닫힌꼴 정리는 더 강하여 음의 정수 매개변수까지 허용한다.
- 원문은 우변의 일부 `a`에서 매개변수를 생략한다. 형식화에서는 나열된
  행들과 양립하는 유일한 해석인, 같은 고정 $m$ 행의 항으로 읽는다.
- 원문의 $a_m(2)$ 식은 $3m^2-16$으로 정리되지만 Lean 정의에는 표시된
  식을 그대로 유지했다.
- `IsSquare`의 증인은 `ℤ`에 있다. 모든 홀수 번째 항을 정수의 제곱으로
  나타내므로 그 항들이 음이 아님도 함께 증명한다.
- 전체 A113249 족에 대한 Formal Conjectures 스냅샷은 없다. 정식 OEIS
  명제는 2026년 8월 12일에 직접 대조했다.

## 독립 유한 검사

[`a113249_certificate.py`](a113249_certificate.py)는 Python 표준 라이브러리만
사용하며, 다음 두 가지 정확한 정수 구현을 별도로 포함한다.

1. 원문의 4차 점화식
2. 보조 2차 점화식

$m=3$ 행에 공개된 29개 항을 확인한 뒤, 모든 정수 매개변수
$-25 ≤ m ≤ 25$에 대해 홀수 번째 항 2,091개를 비교한다. 이 유한 검사는
건전성 확인일 뿐이며, 무한한 전체 명제는 Lean 정리가 증명한다.

저장소 루트에서 다음을 실행한다.

```bash
python3 problems/oeis-a113249/a113249_certificate.py
lake env lean AgenticConjectures/OeisA113249.lean
```

개발 환경에서 인증 스크립트는 약 0.07초, Lean 모듈 직접 검사는 약
24초가 걸렸다. 인증 스크립트의 SHA-256은 다음과 같다.

```text
dd44727de17d1debc92a980cf2985f48c3cca37e4b3f6098e8ce87a1b5007590  problems/oeis-a113249/a113249_certificate.py
```

## 선행 연구와 범위

이 결과는 알려진 특수한 경우를 의도적으로 일반화한다.

- A113249에는 Robert Israel이 2017년에 제시한
  $a_3(2n+1)=b(n)^2$, $b(n)=4b(n-1)-9b(n-2)$ 공식이 있다.
- [OEIS A113254](https://oeis.org/A113254)는 $m=8$ 경우의 공개
  [AlphaProof Nexus Lean 증명](https://github.com/google-deepmind/alphaproof-nexus-results/blob/42f344cfa9d57154f36e6b9bef1f71760a438c54/APNOutputs/OEIS/oeis_113254_conjecture_0.lean)을
  연결한다. 그 증명은 보조 2차 점화식과 세 항 창 귀납법을 사용했다.
  여기의 증명은 그 공개된 구조를 따르되 $m$을 기호로 유지하여 전체
  족을 증명한다.

2026년 8월 12일 현재 A113249 개정판 #29는 여전히 전체 매개변수 명제를
추측으로 표시한다. 정확한 명제로 공개 웹, arXiv, GitHub, Formal
Conjectures와 OEIS 인용 자료를 검색했지만 일반 증명은 찾지 못했다. 그러나
이 부정적 검색 결과는 새로움을 입증하지 않는다. 이 형식화는 검토되지
않았고, 우선권을 주장하지 않으며, OEIS나 다른 외부 매체에 제출하지 않았다.
