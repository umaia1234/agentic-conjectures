[English](README.md) | **한국어**

# 에르되시 문제 #385: 홀수 지표 정리와 10억까지의 정확한 검증

합성수 $m$의 최소 소인수를 $p(m)$이라 하고

\[
F(n)=\max_{\substack{m<n\\m\text{ 합성수}}}\bigl(m+p(m)\bigr)
\]

으로 둡니다. 1979년 논문은 원래 질문을 다음과 같이 제시합니다(인쇄본
73쪽).

> “$F(n)\le n$인 $n$이 무한히 많은가?”

바로 뒤에서는 소수에 관한 그럴듯한 추측들을 가정하면 그런 값이 유한
개뿐일 것이라고 설명합니다. 이에 따라 [현재 공식 문제
페이지](https://www.erdosproblems.com/385)는 논리적으로 반대인 궁극적
형태와 더 강한 발산 질문을 함께 묻습니다.

> 충분히 큰 모든 $n$에 대해 $F(n)>n$인가? $n\to\infty$일 때
> $F(n)-n\to\infty$인가?

두 질문은 모두 여전히 미해결입니다. 이 디렉터리는 하나의 무한한
초등적 부분족과 정확한 유한 범위 분류를 기록하지만, 두 점근적 질문 중
어느 것도 해결했다고 주장하지 않으며 새로움도 주장하지 않습니다.

## 검증된 결과

Lean 모듈 [`Erdos385.lean`](../../AgenticConjectures/Erdos385.lean)은
`sorry`, 추가 공리, `native_decide` 없이 다음 명제를 커널로 검증합니다.

\[
n\ge5\Longrightarrow F(n)\ge n,
\]

그리고 홀수 지표에서는 더 강하게

\[
n\ge5,\quad n\text{이 홀수}\Longrightarrow F(n)>n
\]

이 성립합니다. 정확한 계산은 다음 유한 명제를 증명합니다.

\[
\boxed{267681\le n\le10^9\Longrightarrow F(n)>n.}
\]

$6\le n\le10^9$에서 $F(n)=n$인 경우는 정확히 100개이며, 마지막
세 값은 $8742,267672,267680$입니다. 정렬된 전체 목록과 검증된 여유값
문턱 기록은 [`billion_result.json`](billion_result.json)에 있습니다.

## 독립 검증

[`verify_billion.py`](verify_billion.py)는 전체 구간에서 알고리즘이 서로
다른 두 프로그램을 컴파일하고 교차 검증합니다.

- [`ep430_experiment.cpp`](ep430_experiment.cpp)는 조밀한 선형 최소 소인수
  체를 구성합니다.
- [`ep430_segmented.cpp`](ep430_segmented.cpp)는 홀수만 다루는 분할 체를
  유지하며, 덮임 점화식을 독립적으로 유도합니다.

래퍼는 두 구현의 완전한 등호 사례 목록과 기록된 모든 문턱값이 일치해야
통과하며, 그 뒤 커밋된 JSON 결과와도 대조합니다. 저장소 루트에서 다음을
실행하십시오.

```bash
python3 problems/erdos-385/verify_billion.py
```

2026-08-12 실행에서 조밀 체와 분할 체는 각각 8.87초와 6.67초가
걸렸습니다. 래퍼 전체는 16.31초가 걸렸고, 의도적으로 메모리를 많이 쓰는
조밀 교차 검증 때문에 최대 4,108,120 KiB를 사용했습니다. 분할 구현
단독으로는 약 20 MiB를 사용했습니다. 결합 검증기는 CI 실행 가능 항목으로
등록되어 있습니다.

증명과 두 프로그램이 구현한 정확한 환원은 [수학 상세](DETAILS.ko.md)에
설명되어 있습니다.

## 명제 충실성과 upstream 상태

로컬 Lean 정의는 유한 범위 $m<n$의 상한을 취하고 “합성수”를
$1<m$이면서 $m$이 소수가 아닌 경우로 명시합니다. 따라서 후보 범위가
비어 있지 않을 때 공식 최대값과 같으며, 작은 지표에서 범위가 비었을 때
정의상 0이라는 점만 다릅니다. 여기의 모든 정리는 $n=5$부터 시작하므로
이 경계 규약은 결과에 영향을 주지 않습니다. 지표 시작점이나 자연수 뺄셈
의미의 모호성도 없습니다. $n-1$, $n-2$를 쓰는 모든 곳에는 필요한
하한이 있습니다.

정확한 FormalConjectures 선언은 로컬 [upstream
스냅샷](upstream/README.md)에 보존되어 있습니다. 연구 명제들은 `sorry`를
포함하며, 해당 스냅샷에서 증명된 것은 초등적 상한뿐입니다. part (i)가
에르되시 #430의 첫 질문과 동치이므로 기존 `ep430_*` 파일명은 재현 이력을
위해 유지했습니다.

Google DeepMind의 AlphaProof Nexus `science-submission` 스냅샷 커밋
[`0647711a71183c1ea492ad60860776617ce1ea88`](https://github.com/google-deepmind/alphaproof-nexus-results/tree/0647711a71183c1ea492ad60860776617ce1ea88)은
FormalConjectures의 세 선언을 모두 시도 목록에 기록하지만 #385의 성공
결과는 포함하지 않습니다. 이는 시도 이력일 뿐입니다.

## 확인한 출처

- [Erdős Problems #385](https://www.erdosproblems.com/385), 2026-08-12
  확인. 점근적 질문들은 여전히 미해결로 표시되어 있습니다.
- P. Erdős, [*Some unconventional problems in number
  theory*](https://users.renyi.hu/~p_erdos/1979-23.pdf), *Acta Math. Acad.
  Sci. Hungar.* 33 (1979), 71--80. 원래 질문은 인쇄본 73쪽에 있습니다.
- P. Erdős와 R. L. Graham, [*Old and New Problems and Results in
  Combinatorial Number
  Theory*](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf),
  1980, 74쪽.
- [OEIS A322292](https://oeis.org/A322292), 수열 $F(n)$. 연결된 표의 기존
  범위는 $n\le10000$입니다.
