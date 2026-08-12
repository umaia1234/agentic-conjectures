[English](README.md) | **한국어**

# 에르되시 #671 — 모든 점에서 비유계인 라그랑주 배열

공식 [에르되시 문제 #671](https://www.erdosproblems.com/671)은 라그랑주
보간 절점의 삼각 배열에 관한 두 존재 문제를 묻는다. 2026-08-12 현재 공식
페이지에는 여전히 **미해결(OPEN)** 및 **상금 $250**으로 표시되어 있었다.
그러나 완전한 해법과 형식화는 이미 2026-06-22 공개 토론 스레드에 게시되어
있었다. 이 디렉터리는 그 해법을 독립적으로 다시 빌드하고 보존한다. 신규성이나
상금은 주장하지 않으며 외부 제출도 하지 않는다.

## 공식 명제

각 행 크기 \(n\geq1\)마다 서로 다른 절점
\(a_1^n,\ldots,a_n^n\in[-1,1]\)을 택한다. \(p_i^n\)을 절점
\(a_i^n\)에 대한 기본 라그랑주 다항식이라 하고

\[
  \mathcal L^n f(x)=\sum_{i=1}^n f(a_i^n)p_i^n(x),
  \qquad
  \Lambda_n(x)=\sum_{i=1}^n |p_i^n(x)|
\]

로 둔다. 첫 질문은 모든 연속함수 \(f:[-1,1]\to\mathbb R\)마다 어떤
\(x\)가 존재하여 \(\limsup_n\Lambda_n(x)=\infty\)이면서 동시에
\(\mathcal L^n f(x)\to f(x)\)인지 묻는다. 더 강한 둘째 질문은 르베그
함수의 비유계성을 **모든** \(x\in[-1,1]\)에서 요구하면서도 각 \(f\)에
대해 적어도 한 수렴점이 존재하는지를 묻는다.

## 결과

두 질문 모두 긍정적으로 해결된다. Lean 정리
[`erdos_671`](../../AgenticConjectures/Erdos671.lean)은 각 \(n\)번째 행에
정확히 \(n\)개의 서로 다른 절점을 갖는 하나의 배열을 구성하여 다음을 증명한다.

- 모든 \(x\in[-1,1]\), 실수 문턱값 \(A\), 행 하한 \(N\)에 대해 어떤
  \(n\geq N\)이 존재하여 \(\Lambda_n(x)\geq A\)이다.
- 모든 연속함수 \(f\)에 대해 어떤 \(x_f\in[-1,1]\)가 존재하여 전체 열
  \(\mathcal L^n f(x_f)\)가 \(f(x_f)\)로 수렴한다.

첫 조건은 \(\limsup_n\Lambda_n(x)=\infty\)의 공종적 표현이므로 더 강한
둘째 질문을 그대로 증명한다. 첫 질문은 각 \(f\)에 대해 얻은 \(x_f\)를
택하면 즉시 따른다.

## 명제 충실성

Lean의 `Row (n + 1)`은 공식 명제의 1부터 시작하는 크기 \(n+1\) 행을
나타낸다. `nodeSet`과 `card_nodeSet`은 정확한 원소 수를 보장하고 `Embedding`
필드는 절점들이 서로 다름을 보장한다. `Interval`은 정확히 닫힌 실구간
`Set.Icc (-1) 1`이다. `fundamental`, `interpolant`, `lebesgue`는 표준 곱
형식의 라그랑주 기저, 보간 다항식, 르베그 함수이다.

정리는 비유계성을 `∀ A N, ∃ n ≥ N, A ≤ lebesgue ...`로 표현한다. 이는
비음수 실수열에 대한 공식 페이지의 무한 `limsup`과 동치이며 확장실수 관련
형식화만 피한다. 수렴은 `Tendsto ... atTop`이므로 부분열이 아니라 전체 열의
수렴이다. 끝점, 뺄셈, 행 크기에 관한 완화는 없다.

구성과 증명 구조는 [DETAILS.ko.md](DETAILS.ko.md)에 설명한다.

## 기계 검증

Lean 소스는 2,800줄 이상이며 `sorry`, 추가 공리, `native_decide`를 사용하지
않는다. 저장소 루트에서 다음을 실행한다.

```bash
python3 scripts/check_imports.py
python3 scripts/check_sorry.py
lake build
python3 scripts/check_axioms.py
(cd problems/erdos-671/upstream && sha256sum -c SHA256SUMS)
```

공리 감사 결과는 허용된 Lean 표준 공리 세 개 `propext`,
`Classical.choice`, `Quot.sound`뿐이다. 전체 저장소 검증 단계에서는 기존
인증서와 문서 검사도 함께 실행한다.

## 출처와 선행 연구

[공개 토론 게시물](https://www.erdosproblems.com/forum/thread/671#post-7142)은 증명 논증을
“GPT Pro”에 귀속하고 “Lean formalisation by Codex” 링크를 제공하지만 정확한
모델명과 하네스명은 밝히지 않는다. 따라서 이 저장소는 해당 표기를 그대로
기록하며 더 구체적인 귀속을 만들어 내지 않는다. 로컬 `GPT-5.6 Sol` 귀속은
독립 컴파일, 명제 비교, 저장소 통합, 문서화로 한정한다.

공개 Lean 원문의 SHA-256과 복원 방법은
[upstream/README.md](upstream/README.md)에 보존했다. 검사되는 모듈에서는
저장소에 필요한 네임스페이스·명제 포장과 출처·충실성 문서만 바꾸었으며 증명
본체는 바꾸지 않았다. 공식 페이지가 인용하는 Bernstein의 정리와
Erdős–Vértesi의 거의 모든 점 발산 결과, 그리고 2026년 2월
Zeraoulia–Cáceres의 Baire 범주 장애물 논문은 이 구성의 선행 배경이다. 이
저장소는 외부 심사를 받았다고 주장하지 않는다.
