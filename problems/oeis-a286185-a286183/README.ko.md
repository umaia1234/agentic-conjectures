[English](README.md) | **한국어**

# OEIS A286185 & A286183 — 뫼비우스 사다리와 엇각기둥의 연결 유도 부분그래프

## 결론

아래 두 개의 `2n`-꼭짓점 그래프에 대해, OEIS에 추측으로 올라와 있는 닫힌 형식은
**참**이며, 같은 항목에 함께 추측으로 올라와 있는 6차 선형 점화식과 생성함수도
참이다(둘 다 닫힌 형식에서 따라 나온다).

| | | 추측된 닫힌 형식 | 결과 |
|---|---|---|---|
| [A286185](https://oeis.org/A286185) | 뫼비우스 사다리 | `a(n) = A002203(n) + 3n·A000129(n) - n - 1` | 모든 `n ≥ 1`에 대해 **증명됨** |
| [A286183](https://oeis.org/A286183) | 엇각기둥 | `a(n) = A005248(n) - 2n + 2n·A001906(n)` | 모든 `n ≥ 1`에 대해 **증명됨** |

증명은 [PROOF.md](PROOF.md)에 있다. 하나의 열(column) 전이행렬 논증으로,
같은 계열의 세 번째 항목인 [A286182](https://oeis.org/A286182)(각기둥 그래프)도
함께 유도한다 — 다만 그 경우의 닫힌 형식은 **이미 출판된 정리**이므로, 여기서는
방법의 검증용으로만 쓰인다. 아래 *선행 연구*를 보라.

## 원문 진술

세 항목 모두 2017년 5월 4일 Giovanni Resta가 만들었다. [`upstream/`](upstream/README.md)에
보존된 스냅숏(OEIS 버전 #26–#27, 2026-08-12 기준)을 인용하면, 각 공식에는 여전히
`(conjectured)`라는 표시가 붙어 있다.

> **A286185** — Number of connected induced (non-null) subgraphs of the Möbius
> ladder graph with 2n nodes.
> `a(n) = 6*a(n-1) - 11*a(n-2) + 4*a(n-3) + 5*a(n-4) - 2*a(n-5) - a(n-6), for n>6 (conjectured).`
> `a(n) = Lucas(n, 2) + 3*n*Fibonacci(n, 2) - n - 1, where Lucas(n, 2) = A002203(n) and Fibonacci(n, 2) = A000129(n) (conjectured). - Eric W. Weisstein, May 08 2017`
> `G.f. (subject to the above conjectures. In fact all three conjectures are equivalent): (3*x-3*x^2-2*x^3-4*x^4+3*x^5-x^6)/(1-3*x+x^2+x^3)^2. - Robert Israel, May 08 2017`

> **A286183** — Number of connected induced (non-null) subgraphs of the
> antiprism graph with 2n nodes.
> `a(n) = 8*a(n-1) - 24*a(n-2) + 34*a(n-3) - 24*a(n-4) + 8*a(n-5) - a(n-6), for n > 6 (conjectured).`
> `a(n) = A005248(n) - 2*n + 2*n*A001906(n) (conjectured). - Eric W. Weisstein, May 08 2017`
> `G.f.: x*(3 - 9*x + 12*x^2 - 15*x^3 + 9*x^4 - 2*x^5) / ((1 - x)^2*(1 - 3*x + x^2)^2) (conjectured). - Colin Barker, May 30 2017`

## 방법 요약

꼭짓점 부분집합 `S`를 `n`개의 *열* `c_i = {r : (i,r) ∈ S}`로 나눈다. 비어 있지
않은 열은 그 자체로 연결되어 있고 나머지 모든 변은 순환적으로 인접한 두 열을
잇기 때문에, `S`가 연결일 필요충분조건은 *열 그래프*가 연결인 것이다
([PROOF.md](PROOF.md)의 보조정리 0). 어떤 열이 비어 있으면 채워진 열들은 반드시
호(arc)를 이루며, 호의 개수는 `3×3` 전이행렬의 거듭제곱으로 세어진다. 모든 열이
채워져 있으면 열 그래프는 `n`-순환에서 연결되지 않은 인접쌍을 제거한 것이고,
이는 제거된 인접쌍이 많아야 하나일 때만 연결이므로, 대각합 항과 행렬 성분 하나의
`n`배의 합이 된다. 세 계열의 차이는 전이행렬뿐이다: 각기둥은
`M = [[1,0,1],[0,1,1],[1,1,1]]`, 뫼비우스 사다리는 이음매에 행 교환 `P_σ`를 끼운
같은 `M`, 엇각기둥은 `Mₐ = [[1,1,1],[0,1,1],[1,1,1]]`. 이들의 스펙트럼
(`1, 1±√2` 및 `0, (3±√5)/2`)에서 펠 수와 피보나치 수가 나온다.

## 범위와 정직성

* [PROOF.md](PROOF.md) §3의 논증은 `n ≥ 3`을 필요로 한다(`n = 1, 2`에서는 "열
  순환"이 퇴화한다). `n = 1, 2`는 직접 확인으로 해결되며 — 각각 `K₂`, 그리고 두
  계열 모두 `K₄` — 같은 공식과 일치하므로, 결과는 모든 `n ≥ 1`에서 성립한다.
* 점화식은 OEIS가 명시한 대로 `n ≥ 7`에서 성립한다. `n = 6`에서는 실패하며,
  거기서는 조합적 값이 아닌 `a(0)`이 필요하다.
* 증명은 Lean이 아니라 보통의 수학으로 쓰였다. CI가 재검증하는 것은 아래의
  인증서와 Lean 진술 및 "닫힌 형식 ⟹ 점화식" 함의뿐이며, **그래프 이론적 핵심은
  기계검증되지 않았다**.
* 동료평가를 받지 않았다. OEIS에 제출하지 않았다(철칙 7). **독창성을 주장하지 않는다.**

## 선행 연구

증명 작성 전후로 의도적인 검색을 수행했다(OEIS 항목 본문과 전체 개정 이력, arXiv
전문 API, Google Scholar, MathWorld, 그리고 아래 논문들).

* **각기둥 A286182는 이미 증명되어 있다.** A. Vince, *The average size of a
  connected vertex set of a graph — explicit formulas and open problems*,
  J. Graph Theory **97** (2021) 82–103,
  [doi:10.1002/jgt.22643](https://doi.org/10.1002/jgt.22643); 저자 공개본
  [JGTfinal2.pdf](https://people.clas.ufl.edu/avince/files/JGTfinal2.pdf).
  **보조정리 7.2**가 `N(CL_n) = 1 - 3n + 2β(n) + 3n·β̄(n)`을 주는데, 여기서
  `β = A001333 = A002203/2`, `β̄ = A000129`이므로 이는 Weisstein이 추측한 닫힌
  형식과 문자 그대로 같다. J. Haslegrave, *The number and average size of
  connected sets in graphs with degree constraints*,
  [arXiv:2105.13332](https://arxiv.org/abs/2105.13332) §2에서도 그렇게 인용된다.
  Vince의 증명은 전이행렬이 아니라 합성(composition)/이항계수 논증이다.
  **OEIS 항목이 갱신되지 않았을 뿐이며**, 참고문헌이 아예 없다. Vince의 §6은
  같은 방식으로 보통 사다리([A059020](https://oeis.org/A059020))를 다룬다.
* **뫼비우스 사다리(A286185)와 엇각기둥(A286183)에 대한 증명은 찾지 못했다.**
  Vince의 논문은 사다리, 원형 사다리, 바퀴, 목걸이를 다루며 이 둘은 다루지
  않는다. arXiv 전문 API는 두 A-번호 모두에 대해 아무것도 반환하지 않고, OEIS
  항목에는 참고문헌이 없으며 어떤 개정도 `(conjectured)` 표시를 지운 적이 없다.
  검색이 아무것도 찾지 못한 것은 독창성의 증거가 아니며, 독창성을 주장하지 않는다.

## OEIS 항목에 대한 충실성

여기서 쓰는 그래프는 `Z_n × {0,1}` 위에 가로대 `(i,0)~(i,1)`와 이웃한 열 사이의
세로대(뫼비우스는 이음매 하나가 꼬임, 엇각기둥은 대각선 추가)로 만들어진다
([PROOF.md](PROOF.md) §0). 이것이 OEIS가 실제로 세는 대상과 같음을 두 가지 독립적
검사로 확인한다.

1. `certificate.py`는 각 그래프를 **OEIS 항목 자신의 Mathematica `%t` 프로그램이
   만드는 방식 그대로**도 구성하고(A286185는 `CirculantGraph[2n, {1,n}]`,
   A286182/A286183은 명시적 변 목록), 두 구성의 계수가 `n = 1..9`에서 일치함을
   검증한다. 엇각기둥의 경우 두 구성은 대각선 방향이 반대인데, 두 그래프는
   동형이며(행 교환) 검사가 계수 일치를 확인한다.
2. 두 구성 모두 퇴화 경우 `n = 1, 2`를 포함해 OEIS의 모든 데이터 항(항목당
   27–28개)을 재현한다.

세 항목 모두 OEIS의 오프셋은 1이고 여기서도 동일하다. 인덱스 이동은 없다.

## 재현

이 디렉터리에서 실행한다. 순수 파이썬 표준 라이브러리이며 네트워크가 필요 없다.

```bash
python3 certificate.py
```

36개 검사, 약 38초(2026-08-12 측정. 전수 열거 상한은 CI의 명령당 180초 제한
안쪽에 충분히 들어오도록 정했다). `python3 certificate.py --full`은 전수 열거
범위를 `n ≤ 10`에서 `n ≤ 13`으로 올리며 몇 분이 걸린다.
`python3 certificate.py --print-edges`는 변 목록을 출력한다.

Lean 쪽은 저장소 루트에서:

```bash
lake build && python3 scripts/check_sorry.py && python3 scripts/check_axioms.py
```

Lean 정의와 인증서 사이의 그래프 정의 대조를 다시 돌리려면, 저장소 루트에서:

```bash
lake env lean problems/oeis-a286185-a286183/lean_graph_check.lean
```

를 실행하고 `python3 problems/oeis-a286185-a286183/certificate.py --print-edges`와
비교한다(2026-08-12 기준 세 그래프 모두 `n = 1..6`에서 변 집합이 정확히 일치했다).

## Lean에 들어 있는 것

[`AgenticConjectures/OeisA286185A286183.lean`](../../AgenticConjectures/OeisA286185A286183.lean)은
세 그래프와 `connectedInducedCount`를 정의하고, 세 닫힌 형식 추측을
`statementPrism`, `statementMoebius`, `statementAntiprism`으로 진술하며, 다음을
`sorry` 없이 증명한다.

* `aMoebius_linear_recurrence`, `aAntiprism_linear_recurrence`,
  `aPrism_linear_recurrence` — 각 닫힌 형식이 해당 항목에 추측된 6차 점화식을
  모든 `n`에 대해 만족한다.
* `statementMoebius_imp_linear_recurrence`와 그 두 형제 — 따라서 각 닫힌 형식
  추측은 그래프 계수 자체에 대한 점화식 추측을 함의한다.
* `aMoebius_initial_values`, `aAntiprism_initial_values`,
  `aPrism_initial_values` — 닫힌 형식이 OEIS의 처음 여섯 항을 재현한다.

항등식 `connectedInducedCount _ n = a n` 자체는 Lean에서 진술만 되어 있고 증명되어
있지 않다. 그것이 [PROOF.md](PROOF.md)의 내용이다.
