[English](README.md) | **한국어**

# 에르되시 문제 #385: 초등적 부분족과 $10^{11}$까지의 정확한 검증

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

두 질문은 모두 여전히 미해결입니다. 이 디렉터리는 무한한 초등적
부분족들과 정확한 유한 범위 분류를 기록하지만, 두 점근적 질문 중
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

이 성립합니다. 같은 모듈은 $n\ge5$이고 $n-1$이 소수가 아니면 $F(n)>n$임도
증명하며, 특히 $n\equiv4\pmod 6$인 모든 $n\ge5$에서 그렇습니다. 따라서
등호 사례의 형태는 다음과 같이 제한됩니다.

\[
n\ge5,\ F(n)=n\Longrightarrow n\text{은 짝수이고 }n-1\text{은 소수}.
\]

정확한 계산은 다음 유한 명제를 증명합니다.

\[
\boxed{267681\le n\le10^{11}\Longrightarrow F(n)>n.}
\]

$6\le n\le10^{11}$에서 $F(n)=n$인 경우는 정확히 100개이고 모두 $10^9$보다
작으며, 마지막 세 값은 $8742,267672,267680$입니다. 정렬된 전체 목록과
검증된 여유값 문턱 기록은 [`billion_result.json`](billion_result.json)과
[`extended_result.json`](extended_result.json)에 있습니다.

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

## $10^{11}$까지의 확장 (2026-10-24)

새로운 두 다중 스레드 프로그램이 모든 지표 $6\le n\le10^{11}$을
분류합니다.

- [`allint_segments.cpp`](allint_segments.cpp)는 모든 정수를 체로
  거릅니다. 소수를 큰 것부터 기록하여 가장 작은 소수가 마지막에
  덮어쓰게 하고, 모든 합성수에 대해 $F(n)$을 직접 계산합니다. $10^9$
  크기의 지표 구간마다 명시적인 예열 구간을 둔 뒤 독립적으로 처리합니다.
- [`odd_carry.cpp`](odd_carry.cpp)는 홀수만 체로 거릅니다. 각 칸에 처음
  도달한 (가장 작은) 소수를 유지하고 홀짝 환원을 사용합니다. $m=3$부터
  $10^{11}$까지 한 번의 정확한 탐색으로 누적 최댓값을 이어 갑니다.

두 프로그램이 공유하는 것은 출력 형식뿐입니다. 각 프로그램은 지표 구간
$(k\cdot10^9,(k+1)\cdot10^9]$마다 기록 하나씩, 모두 100개를 씁니다. 기록에는
등호 사례, $F(n)-n$의 최솟값, 18개 문턱 $t$ 각각에 대해
$F(n)-n\le t$인 마지막 $n$이 들어 있습니다. 또한 $F(n)-n$의 정확한 합과
수열 $(n,F(n)-n)$ 전체의 64비트 지문도 들어 있습니다. 커밋된 두 로그는
모든 기록에서 일치합니다. 방법, 예열 보조정리, 지문은
[수학 상세](DETAILS.ko.md) 8절에 설명되어 있습니다.

**결과.** $6\le n\le10^{11}$에서 $F(n)=n$인 경우는 정확히 100개이며,
$10^9$ 아래에서 찾은 100개 값과 같습니다. 따라서

\[
\boxed{267681\le n\le10^{11}\Longrightarrow F(n)>n.}
\]

$(10^9,10^{11}]$에는 $F(n)-n\le20000$인 지표가 없습니다. $F(n)-n$의
최솟값은 $(10^9,10^{10}]$에서 23331이고 $n=1009345789$에서 처음 나타나며,
$(10^{10},10^{11}]$에서는 81881이고 $n=10119571529$에서 처음 나타납니다.
특히 [`billion_result.json`](billion_result.json)에 있는 $t\le1000$의 열두
여유값 문턱 기록은 $10^{11}$까지 그대로입니다. 18개 기록 전체는
[수학 상세](DETAILS.ko.md) 8.5절에 있습니다.

요약은 [`extended_result.json`](extended_result.json)에 있습니다. 구간별
원본 로그는 [`logs/allint_segments_6_1e11.jsonl`](logs/allint_segments_6_1e11.jsonl)과
[`logs/odd_carry_6_1e11.jsonl`](logs/odd_carry_6_1e11.jsonl)이며, 두 파일의
SHA-256 값이 요약에 기록되어 있습니다.

**재현.** 저장소 루트에서 다음을 실행하십시오.

```bash
python3 problems/erdos-385/verify_extended.py          # CI 모드
python3 problems/erdos-385/verify_extended.py --full   # 100개 구간 전체 재계산
```

커밋된 로그는 2026-10-24에 각 프로그램을 한 번씩 실행해 얻었습니다.
Apple clang 21의 `-O3`로 컴파일했고, 다른 작업과 함께 쓰는 Apple M5
Max(부하 평균 40 이상)에서 두 프로그램을 스레드 2개씩으로 동시에
실행했습니다. `allint_segments`는 벽시계 시간 447초(CPU 419초),
`odd_carry`는 443초(CPU 298초)가 걸렸고, 둘 다 메모리를 7 MB 미만으로
사용했습니다. CI 모드는 로그 해시, 100개 기록 전체의 일치, 재결합한
요약을 확인합니다. 이어서 두 프로그램을 다시 컴파일하여 각각 첫 $10^9$
구간과 마지막 $10^9$ 구간을 재계산하고, $[6,30000]$에서 두 프로그램을
시행 나눗셈과 비교합니다. 이 환경에서는 벽시계 시간 약 10초, 최대 메모리
118 MB가 들었습니다. `--full`은 두 프로그램으로 100개 구간 전체를
재계산하며(이 환경에서 스레드 4개로 벽시계 시간 10.3분), CI 실행 가능
항목으로 등록하지 않았습니다.

**주장하지 않는 것.** 이것은 유한 범위 검증이며 두 점근적 질문 중 어느
것도 결정하지 않습니다. 지문은 두 프로그램 사이의 교차 확인일 뿐 그
자체로 인증서가 아닙니다. 정확한 객체(등호 사례, 문턱 기록, 최솟값, 합)는
정확히 비교합니다.

## 명제 충실성과 upstream 상태

로컬 Lean 정의는 유한 범위 $m<n$의 상한을 취하고 “합성수”를
$1<m$이면서 $m$이 소수가 아닌 경우로 명시합니다. 따라서 후보 범위가
비어 있지 않을 때 공식 최대값과 같으며, 작은 지표에서 범위가 비었을 때
정의상 0이라는 점만 다릅니다. 덮임 판정 기준 `lt_F_iff`를 제외한 모든
정리는 $n=5$부터 시작하므로 이 경계 규약은 결과에 영향을 주지 않습니다.
`lt_F_iff`는 모든 $n$에서 성립하며, 범위가 빈 $n\le4$에서는 양쪽 모두
거짓입니다. Lean의 `Nat.minFac`은 $m\ge2$인 모든 수의 최소 소인수이므로
합성수에서는 $p(m)$과 같습니다. 지표 시작점이나 자연수 뺄셈 의미의
모호성도 없습니다. $n-1$, $n-2$를 쓰는 모든 곳에는 필요한 하한이
있습니다.

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
