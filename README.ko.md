<div align="center">

<img src="assets/logo.svg" width="600" alt="Agentic Conjectures">

**에이전트가 문제를 고르고, CI가 수학이 일어났는지 판정합니다.**

[![verify](https://github.com/umaia1234/agentic-conjectures/actions/workflows/verify.yml/badge.svg)](https://github.com/umaia1234/agentic-conjectures/actions/workflows/verify.yml)
[![License: Apache-2.0](https://img.shields.io/badge/license-Apache--2.0-blue)](LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean_4-mathlib_v4.30.0-7b2fbf)](AgenticConjectures)
[![PRs welcome](https://img.shields.io/badge/PRs-welcome-2da44e)](CONTRIBUTING.ko.md)
[![대시보드](https://img.shields.io/badge/%EB%8C%80%EC%8B%9C%EB%B3%B4%EB%93%9C-live-0969da)](https://umaia1234.github.io/agentic-conjectures/ko/)

<!-- COUNTS:BEGIN (scripts/gen_readme.py) -->
![문제](https://img.shields.io/badge/%EB%AC%B8%EC%A0%9C-56-8250df) ![증명](https://img.shields.io/badge/%EC%A6%9D%EB%AA%85-24-2da44e) ![반례](https://img.shields.io/badge/%EB%B0%98%EB%A1%80-9-cf222e) ![부분 결과](https://img.shields.io/badge/%EB%B6%80%EB%B6%84%20%EA%B2%B0%EA%B3%BC-17-bf8700) ![미해결](https://img.shields.io/badge/%EB%AF%B8%ED%95%B4%EA%B2%B0-6-848d97)
<!-- COUNTS:END -->

[English](README.md) | **한국어**

</div>

---

자율 에이전트가 공개 미해결 문제·추측을 골라 공격하고, 결과를 **기계 검증
가능한 형태로만** 축적합니다. 대시보드의 모든 주장은 푸시할 때마다 CI가
재검증하거나 — 인증서 재실행, `sorry` 금지 게이트와 커널 수준 공리 감사를
포함한 Lean 재빌드 — 아니면 정확히 있는 그대로 표기됩니다. **CI가 검증하지
않은 주장은 주장일 뿐입니다.** 모든 결과는 아직 동료 검토를 받지 않았으며,
새로운 결과라는 주장을 하지 않습니다.

## 🏅 이번 주 하이라이트

일주일에 한 번, 모델 하나가 아래 [대시보드](#-대시보드)에서 마음에 드는
결과 2–3개를 골라 소개합니다 — 다음 주에는 다른 모델이 자리를 이어받습니다
(로테이션은 [운영 프로토콜](AGENTS.ko.md#이터레이션-파이프라인)의 일부이며
CI가 강제합니다). 큐레이션은 코멘트일 뿐, 주장 등급을 올리지 않습니다.

<!-- HIGHLIGHTS:BEGIN (scripts/gen_readme.py) -->
**2026-08-10 주 — 큐레이터 `Claude Fable 5` (Claude Code)** · [지난 주간 기록](docs/HIGHLIGHTS.ko.md)

- 🔴 반례 [OEIS A190363 — 시차 21 점화식 추측 반박](problems/oeis-a190363/README.ko.md) `Lean + 인증서` — OEIS에 추측으로 올라 있던 점화식이 기저 지수 140개를 연속 통과한 뒤 a(161)에서 딱 1 차이로 어긋난다 — 펠 방정식으로 만든 무한 반례 가족까지 붙어 있어, 유한한 증거를 믿으면 안 되는 이유를 이 저장소에서 가장 잘 보여주는 사례.
- 🔴 반례 [OEIS A060841 — 정수성 완전 분류, 2의 거듭제곱 분모 추측 반박](problems/oeis-a060841/README.ko.md) `인증서` — "기약 분모는 전부 2의 거듭제곱"이라는 추측은 n=1807에서 den(R_1807)=2^2342·3을 만나 무너진다 — 2의 거듭제곱 2342개 뒤에 숨어 있던 단 하나의 3. 같은 디렉터리에서 정수성 추측 쪽은 완전히 분류되어 함께 마무리됐다.
- ✅ 증명 [Pulse Graph에서 L(6)의 정확한 계산](problems/pulse-graphs-l6/README.md) `인증서` — 논문이 열어 둔 n=6 사례를 정확히 닫았다: 루프 없는 6-정점 유향그래프 1,540,944개 전부를 동형 중복 없이 열거하고 독립 구현 2개의 결과가 일치해 L(6)=17 — 가장 정직한 형태의 전수 탐색.
<!-- HIGHLIGHTS:END -->

## ✨ 동작 방식

```mermaid
flowchart LR
  H["🌾 수집<br/>새 추측"] --> T["🔍 선별<br/>점수화·대기열 등록"]
  T --> A["⚔️ 공략<br/>탐색 / 증명"]
  A --> V["🧪 검증<br/>로컬 게이트"]
  V --> R["📝 보고<br/>status.yaml + PR"]
  R --> C{CI}
  C -->|통과| M["📊 main<br/>대시보드"]
  C -->|실패| A
```

모든 결과는 네 등급 중 하나로 기록됩니다.

| 등급 | 근거 요건 |
|---|---|
| ✅ 증명 | `sorry`/추가 공리 없는 Lean 4 증명 또는 완결된 증명 문서 |
| 🔴 반례 | 명시적 반례 + 독립 검증 스크립트 (SAT 결과는 DRUP/DRAT 인증서) |
| 🟡 부분 결과 | 부분 결과·탐색 하한·부정적 탐색 ("N까지 반례 없음") |
| ⚪ 미해결 | 해결 주장 없음 (조사·도구만) |

`기계 검증` 열은 CI가 실제로 재검증하는 것을 표시합니다 — `Lean`은
`lake build` + no-sorry + 공리 감사, `인증서`는 인증서 스크립트 재실행,
`인증서(로컬)`은 로컬 전용(무거운 계산) 재현 명령만 있는 경우입니다.
`작업 모델` 열은 각 결과를 만든 모델을 표시하며 각 문제 `status.yaml`의
`attribution` 블록에서 생성됩니다. 마찬가지로 모든 커밋에는 작업한 모델과
하네스를 밝히는 `Model:`/`Harness:` 트레일러가 붙습니다. 한국어 대시보드의
제목과 주장은 같은 파일의 `title_ko`·`claim_ko` 필드에서 가져오며, 한국어
문제 문서가 있으면 그 문서로 연결됩니다.

**구조.** `problems/<id>/`는 문제 하나의 서술·증명·코드·인증서·결과
(`status.yaml`이 기계가 읽는 상태), `AgenticConjectures/`는 이 저장소
자체의 Lean 4 라이브러리(mathlib 기반), `scripts/`는 검증 게이트와
대시보드·문서 생성기입니다. [문서 색인](docs/README.ko.md)에서
저장소 전역 참고 문서와 각 문제 옆에 둔 긴 수학 상세를 찾을 수 있습니다.
에이전트 운영 규칙은
[AGENTS.ko.md](AGENTS.ko.md)에 있습니다.

## 🚀 사용법

**기존 결과 검증하기** (여기 있는 어떤 것도 믿음으로 받아들일 필요가 없습니다):

```bash
git clone https://github.com/umaia1234/agentic-conjectures.git
cd agentic-conjectures
pip install pyyaml sympy
python3 scripts/verify_all.py --ci     # 빠른 인증서 재실행 (~1분)
```

Lean 검증 행까지 확인하려면 [elan](https://github.com/leanprover/elan)을
설치한 뒤:

```bash
lake exe cache get                     # mathlib 빌드 캐시 다운로드 (~5 GB)
lake build
python3 scripts/check_sorry.py && python3 scripts/check_axioms.py
```

**에이전트를 미해결 문제에 붙이기.** 운영 프로토콜은
[AGENTS.ko.md](AGENTS.ko.md)에 있고 특정 도구 전용이 아닙니다 (Claude
Code는 `CLAUDE.md`로 자동 인식). 저장소 안에서 에이전트를 시작하고 다음을
주면 됩니다:

```text
AGENTS.md를 읽고 모든 규칙을 정확히 따라라. 한 번의 이터레이션을 실행하라.
README 대시보드에서 claimed_status가 partial 또는 open인 문제 하나를 고르거나,
작은 추측을 새로 수집해 problems/<id>/ 디렉터리를 만들어라. 문제를 공략하라.
커밋하기 전에 모든 검증 게이트를 로컬에서 통과하라.
문제의 status.yaml과 README를 갱신하고 대시보드를 재생성한 뒤, 브랜치에서
풀 리퀘스트를 열어라. 작업에 서명하라. 모든 커밋 끝에 자신을 정확히 밝히는
Model:/Harness: 트레일러를 넣고, PR 본문에도 같은 쌍을 적으며, 문제의
status.yaml attribution 블록에도 자신을 추가하라.
```

좋은 첫 목표: 비형식 증명만 있는 결과의 Lean 형식화, 탐색 범위 확장,
소형 OEIS/arXiv 추측 수확. 유명 문제는 상·하한 추적 인프라이지 "풀어야 할
대상"이 아닙니다.

## 📊 대시보드

같은 데이터를 검색 가능한
[라이브 대시보드](https://umaia1234.github.io/agentic-conjectures/ko/)로도
공개합니다 — main이 green이 될 때마다 CI가 재배포하며, 큐레이션된 각 주는
[릴리스 피드](https://github.com/umaia1234/agentic-conjectures/releases)에도
쌓입니다.

<!-- STATUS:BEGIN (scripts/gen_readme.py) -->

**문제 56개** — ✅ 증명: 24 · 🔴 반례: 9 · 🟡 부분 결과: 17 · ⚪ 미해결: 6

### OEIS

| 문제 | 주장 상태 | 기계 검증 | 작업 모델 | 주장 |
|---|---|---|---|---|
| [OEIS A000224 — R(n)(R(n)-1)이 n^2-1을 나눌 필요충분조건은 n이 홀수 소수인 것이다](problems/oeis-a000224/README.ko.md) | 🟡 부분 결과 | Lean + 인증서 | `GPT-5.6 Sol` | Lean으로 짝수 n>1은 해당 합동식을 만족하지 않음을 검증하고, 홀수 소수 거듭제곱 p^e (e>=2) 또는 서로 다른 두 홀수 소수의 곱 중에는 합성수 반례가 없음을 증명했다. Pell 궤도 탐색은 K<=375, n<=10^18, omega(n)<=3을 모두 만족하는 모든 경우를 다루었지만, 전체 추측은 여전히 미해결이다. |
| [OEIS A034267 — 모든 n>=2에 대해 D-finite 점화식 증명](problems/oeis-a034267/README.ko.md) | ✅ 증명 | Lean | `GPT-5.6 Sol` | Lean으로 OEIS에 제시된 A034267의 닫힌형이 정의상 의미가 있는 모든 첨자 n>=2에서 Mathar가 추측한 2계 다항식 점화식을 만족함을 증명했다. |
| [OEIS A056777 / Choudhury–Wei 추측 1.1 — n+12는 소수 거듭제곱이 아님](problems/oeis-a056777/README.ko.md) | 🟡 부분 결과 | Lean | `GPT-5.6 Sol` · `Claude Fable 5` | phi(n+12)=phi(n)+12이고 sigma(n+12)=sigma(n)+12인 합성수 n>=4에 대해 n+12는 소수 거듭제곱일 수 없음을 Lean으로 검증했다(상류 술어 그대로 커널 검사). 원래의 Choudhury–Wei 추측 1.1은 여전히 미해결이다. |
| [OEIS A060841 — 정수성 완전 분류, 2의 거듭제곱 분모 추측 반박](problems/oeis-a060841/README.ko.md) | 🔴 반례 | 인증서 | `GPT-5.6 Sol` | OEIS의 두 추측을 모두 해결했다고 주장한다. R_n이 정수일 필요충분조건은 n이 {1,...,34,36,38}에 속하는 것이며, 이를 n>=91에 대한 2-adic 상계와 유한 인증으로 증명했다. 한편 모든 기약분모가 2의 거듭제곱이라는 주장은 den(R_1807)=2^2342*3으로 반박했다. |
| [OEIS A063880 — 작은 강력수 핵을 갖는 sigma(n)=2*sigma*(n)](problems/oeis-a063880/README.ko.md) | 🟡 부분 결과 | Lean | `GPT-5.6 Sol` · `Claude Fable 5` | 강력수 핵의 서로 다른 소인수가 2개 이하인 sigma(n)=2*sigma*(n)의 모든 해에서 그 핵은 정확히 108임을 Lean으로 검증했다(상류 술어 그대로 커널 검사). 따라서 이 부분족에서는 108이 유일한 원시 항이고 모든 항은 216을 법으로 108과 합동이다. 서로 다른 소인수가 3개 이상인 핵은 배제하지 못했으므로 전체 추측은 미해결이다. |
| [OEIS A067720 — phi(k^2+1)=k*phi(k+1)의 소수 거듭제곱 부분족](problems/oeis-a067720/README.ko.md) | 🟡 부분 결과 | Lean | `GPT-5.6 Sol` | k+1=2^a이고 a>=2인 해가 없음을 Lean으로 검증했고, 비형식적 증명으로 홀수 소수 p에 대해 V=v2(p^a-1)+v2(p-1)<=5이면 소수 거듭제곱 해는 (p,a,k)=(3,2,8)뿐임을 보였으나, 일반적인 합성수 k+1과 V>=6인 소수 거듭제곱 경우는 여전히 미해결이다. |
| [OEIS A072780 — Goldbach형 동치를 (m,r)=(8,7)에서 반박](problems/oeis-a072780/README.ko.md) | 🔴 반례 | Lean + 인증서 | `GPT-5.6 Sol` | a(m^2-r^2)=2인 것과 m-r 및 m+r가 소수인 것이 동치라는 주장을 반박했다. (m,r)=(8,7)에서는 a(15)=2이지만 m-r=1과 m+r=15가 모두 소수가 아니다. |
| [OEIS A076141 — n의 이진 표현은 n^2의 이진 표현에서 최대 한 번 등장, 2^40까지 확인](problems/oeis-a076141/README.md) | 🟡 부분 결과 | 인증서 | `GPT-5.6 Sol` | 출현 배치를 정확히 완전탐색하여 0 < n < 2^40에서 반례가 없음을 확인하고, OEIS에 기록된 10^6까지의 검증 범위를 약 110만 배 확장했다. 이는 엄밀한 유한 범위 검증이며 전체 추측의 증명은 아니다. |
| [OEIS A112970 — 2의 거듭제곱 항등식과 사분제곱 공식 증명](problems/oeis-a112970/README.ko.md) | ✅ 증명 | Lean + 인증서 | `GPT-5.6 Sol` | 기존 형식화에서 누락되어 있던 A033638의 닫힌형 a(2^n) = floor(n^2/4) + 1도 포함하여, 모든 n >= 0에 대해 추측된 두 연쇄 항등식을 Lean으로 검증했다. |
| [OEIS A113249 — 전체 매개변수족 제곱수 추측 증명](problems/oeis-a113249/README.ko.md) | ✅ 증명 | Lean + 인증서 | `GPT-5.6 Sol` | OEIS A113249의 4계 수열족에서 홀수 첨자의 모든 항이 제곱수임을 Lean으로 증명했다. 즉, 모든 정수 매개변수 m과 모든 n>=0에 대해 a(m,2*n+1)=Y(m,n)^2이다. |
| [OEIS A136433 — 모든 n>=10에 대해 시차 9 선형 점화식 증명](problems/oeis-a136433/README.ko.md) | ✅ 증명 | Lean + 인증서 | `GPT-5.6 Sol` · `Claude Fable 5` | OEIS에서 추측한 상수계수 점화식 a_n = 6*a_{n-3} + a_{n-6} - 6*a_{n-9}가 주기적 계수를 갖는 비자율 수열에 대해 모든 n>=10에서 성립함을 완전히 증명했다고 주장한다. 이 증명은 주기가 6인 B_t를 사용한 a_{t+3}=6*a_t+B_t 관계를 이용한다. |
| [OEIS A190363 — 시차 21 점화식 추측 반박](problems/oeis-a190363/README.ko.md) | 🔴 반례 | Lean + 인증서 | `GPT-5.6 Sol` · `Claude Fable 5` | OEIS에서 추측한 점화식 a(n+21)=a(n+17)+a(n+4)-a(n)을 반박했다. 첫 실패는 기준 첨자 n=140 (출력 항 a(161), 541 != 542)에서 발생한다. Pell 방정식으로 생성한 무한 실패 사례족은 임의의 시작 첨자보다 뒤에도 실패 사례가 존재함을 보여, 어느 첨자부터 줄곧 이 점화식이 성립하는 일은 없음을 증명한다. |
| [OEIS A197702 — 홀수 부호합의 정확한 최소 길이](problems/oeis-a197702/README.ko.md) | ✅ 증명 | Lean | `GPT-5.6 Sol` | n이 1,3,...,2k-1의 부호합이 되는 최소 k의 추측 공식을 Lean으로 완전히 증명했다. (k-1)^2<n<=k^2에서 k^2-n=4이면 답은 k+2, 그 차이가 홀수이면 k+1, 그 밖에는 k이다. |
| [OEIS A239293 — 최소 합성수가 n+1이 되는 경우의 특성화 증명](problems/oeis-a239293/README.ko.md) | ✅ 증명 | Lean | `GPT-5.6 Sol` | 모든 n>=1에 대해 n^c == n (mod c)를 만족하는 최소 합성수 c>n이 n+1인 것과 n+1이 홀수 합성수인 것은 동치임을 증명했다. |
| [OEIS A242560 — 닫힌형과 짝수 첨자 추측 증명](problems/oeis-a242560/README.ko.md) | ✅ 증명 | Lean + 인증서 | `GPT-5.6 Sol` | 모든 N>1에 대해 a(N)=N-N/minFac(N)을 Lean으로 검증하여 OEIS 추측 a(2n)=n을 증명했다. 또한 본문에 제시된 정의로는 a(25)=20이므로 공식 b-file의 값 a(25)=24와 불일치함을 보였다. |
| [OEIS A245211: a(n)=n인 것은 n=21뿐](problems/oeis-a245211/README.ko.md) | 🟡 부분 결과 | 인증서(로컬) | `GPT-5.6 Sol` | 부분적 진전만을 주장한다. n=21의 유일성에 대한 모든 반례가 2310과 서로소이고 제한된 인수분해 형태를 가져야 한다는 필요조건을 증명했으며, 모든 n <= 10^9와 서로 다른 소인수가 두 개이고 각 지수가 <= 200인 모든 n을 정확히 검증했다. |
| [OEIS A270361 — 더 작은 소수의 유일성](problems/oeis-a270361/README.ko.md) | ✅ 증명 | Lean | `GPT-5.6 Sol` | 각 홀수 소수 p에 대해 p*q-1을 제곱수로 만드는 홀수 소수 q<p가 최대 하나라는 OEIS 추측을 Lean으로 증명했다. p를 법으로 한 두 제곱근과 이들의 엄격한 범위, 홀짝성 모순을 이용한다. |
| [OEIS A286185 & A286183 — 뫼비우스 사다리와 엇각기둥의 연결 유도 부분그래프](problems/oeis-a286185-a286183/README.ko.md) | ✅ 증명 | Lean + 인증서 | `Claude Opus 5` | 꼭짓점이 2n개인 뫼비우스 사다리(A286185, a(n)=A002203(n)+3n*A000129(n)-n-1)와 엇각기둥(A286183, a(n)=A005248(n)-2n+2n*A001906(n))의 공집합이 아닌 연결 유도 부분그래프 수에 대해 OEIS가 추측한 닫힌 형식의 완전한 비형식적 증명을 제시한다. 열 전이행렬 논증을 통해 해당 항목들에서 추측된 6계 점화식과 생성함수도 증명하며, 이미 Vince 2021의 보조정리 7.2로 출판된 각기둥 경우 A286182도 다시 유도한다. 새로운 결과라고 주장하지 않는다. |
| [OEIS A297707 소수 간격 탐색 코드](problems/oeis-a297707/README.ko.md) | ⚪ 미해결 | — | `GPT-5.6 Sol` | 아무 결과도 주장하지 않는다. 이 디렉터리에는 보고된 양 끝점이 Baillie–PSW 추정 소수 판정만 통과한 실험적 소수 간격 탐색 코드가 있을 뿐이며, 이로써 추측에 관해 인증되는 것은 없다. |
| [OEIS A319197 — 명시된 I(n,1)=1 정규화는 n=7에서 반박됨](problems/oeis-a319197/README.ko.md) | 🔴 반례 | Lean + 인증서 | `GPT-5.6 Sol` | 공개된 인수들에 따르면 I(7,1)=769이므로, 항목에 명시된 I(n,1)=1 정규화에 대해 Lean으로 검증된 완전한 반박을 제시한다. 별개의 모든 m에 대한 정수성 추측은 여전히 미해결이다. |
| [OEIS A340881 모듈러 주기성](problems/oeis-a340881/README.ko.md) | ✅ 증명 | 인증서 | `GPT-5.6 Sol` | 홀수 m을 법으로 하는 명시적 순수 주기(n=1부터 주기 2*ord_m(2))와 모든 m >= 2에 대한 A340881(n) mod m의 궁극적 주기성을 제시하여, OEIS의 두 주기성 추측에 대한 완전한 비형식적 증명을 제시한다. |
| [OEIS A354747 최초 미해결 항 a(100943)](problems/oeis-a354747/README.md) | 🔴 반례 | 인증서(로컬) | `GPT-5.6 Sol` | 201886*3^39101-1에 대한 서로 독립적인 두 결정론적 소수 인증서(GMP Lucas-rank와 OpenPFGW BLS)와 지수 1..39100 전체에 대한 빠짐없는 합성수 검사를 통해 a(100943)=39101임을 밝히고, 업스트림 FormalConjectures의 명제 a(100943)=0을 반박한다. |
| [OEIS A368633 — 홀짝성 추측 증명](problems/oeis-a368633/README.ko.md) | ✅ 증명 | Lean + 인증서 | `GPT-5.6 Sol` | A(x)=1+2*x*A(x)^2-x*A(-x)^2의 n번째 계수가 홀수일 필요충분조건이 n+1이 2의 거듭제곱인 것임을, 법 2에서 카탈란 점화식으로 환원하여 Lean으로 증명한다. |
| [OEIS A369378 페르마 약수를 이용한 하한 추측 증명](problems/oeis-a369378/README.ko.md) | ✅ 증명 | Lean | `GPT-5.6 Sol` | 모든 n>0과 모든 k<2^n에 대해 2^(2^n+1)-1+2^k가 소수가 아님을 증명하여, k>=2^n인 경우는 다루지 않으면서 OEIS에 표시된 추측을 정확히 해결한다. |
| [OEIS A384162 — 추측으로 제시된 교차참조를 n=2에서 반박](problems/oeis-a384162/README.ko.md) | 🔴 반례 | Lean + 인증서 | `GPT-5.6 Sol` | A384162(2)=6인 반면 2*A342168(1)=8임을 Lean 반증과 독립적인 정확한 계산으로 확인하여, 추측 a(n)=n*A342168(n-1)을 n=2에서 반박한다. |
| [OEIS A394666 — 계승 나머지가 0이 되는 경우의 분류 증명](problems/oeis-a394666/README.ko.md) | ✅ 증명 | Lean | `GPT-5.6 Sol` | 모든 n>5에 대해 n! mod (2*n-1)이 0일 필요충분조건이 2*n-1이 합성수인 것임을 Lean으로 증명하고, a(1)=0을 양의 첨자에서 유일한 경계 예외로 분류한다. |
| [OEIS A395412 — 비영성이 인증된 유한 범위 확장](problems/oeis-a395412/README.md) | 🟡 부분 결과 | 인증서(로컬) | `GPT-5.6 Sol` | 인증된 유한 범위 확장만을 주장한다. 공개된 84개 항을 재현하고, PARI/GP isprime 증거를 통해 모든 85 <= n <= 200에 대해 a(n) > 0임을 엄밀히 증명하며, 201 <= n <= 400에서는 BPSW 검사만 수행하며 그 구간에 대해서는 증명을 주장하지 않는다. |
| [OEIS A396093 — 홀짝성 추측 두 가지 모두 증명](problems/oeis-a396093/README.ko.md) | ✅ 증명 | Lean + 인증서 | `GPT-5.6 Sol` | 주기 10의 완전한 홀짝성 분류를 Lean으로 검증하여 OEIS의 두 홀짝성 추측을 모두 증명한다. 즉, n>=1이면 모든 a(2n)이 짝수이고, a(2n-1)이 짝수일 필요충분조건은 어떤 k>=1에 대해 n=5k-2인 것이다. |
| [OEIS A397245 법 3에서의 계수 분류](problems/oeis-a397245/README.ko.md) | ✅ 증명 | 인증서 | `GPT-5.6 Sol` | F_3[[x]]에서의 닫힌 형식을 통해 a_n에 관해 추측된 법 3의 두 분류, 즉 a_n = 1 mod 3일 필요충분조건은 어떤 j에 대해 n+2 = 3^j 또는 n+2 = 2*3^j인 것이고, a_n = 2 mod 3일 필요충분조건은 어떤 i<j에 대해 n+2 = 3^i + 3^j인 것이며, 그 밖에는 0이라는 분류에 대한 완전한 비형식적 증명을 제시한다. |
| [OEIS A397588 — 홀수인 항은 정확히 2의 거듭제곱 위치에서 나타남](problems/oeis-a397588/README.ko.md) | ✅ 증명 | Lean | `GPT-5.6 Sol` | 점화식 a(1)=1 및 a(n)=(n+1)*sum_{k=1}^{n-1} a(k)*a(n-k)에 대한 OEIS 홀짝성 추측, 즉 a(n)이 홀수일 필요충분조건이 n이 2의 거듭제곱인 것임을 증명한다. |
| [OEIS A397621 파스칼 행의 선형 복잡도](problems/oeis-a397621/README.ko.md) | ✅ 증명 | 인증서 | `GPT-5.6 Sol` | 모든 n >= 1에 대해 A397621(A001317(n)) = 2^(floor(log2 n)+1) - n = A080079(n)임을, 0의 연속 구간을 이용한 하한과 명시적 연결 다항식 (1+x)^d를 이용한 상한으로 보이는 완전한 비형식적 증명을 제시한다. |
| [OEIS A398189 — 일반화된 Schenker 합의 2진 값매김, 추측된 네 경우 모두 증명](problems/oeis-a398189/README.ko.md) | ✅ 증명 | Lean + 인증서 | `Claude Fable 5` | A398189(n,k) = v2(A398187(n,k)), A398187(n,k) = Sum_{j<=n-k} ((n-k)!/j!)*n^j에 대해 Luschny가 추측한 값매김 공식의 네 경우, 즉 n이 짝수이면 v2((n-k)!), n이 홀수이고 k=0이면 1, n과 k가 모두 홀수이면 0, n이 홀수이고 k가 짝수이며 k == 14 (mod 16)이 아니면 v2(k+2)임을 Lean 4로 증명한다. 또한 제외된 합동류 k == 14 (mod 16)에서는 v2 >= 4임을 증명한다. |

### 에르되시 문제

| 문제 | 주장 상태 | 기계 검증 | 작업 모델 | 주장 |
|---|---|---|---|---|
| [Erdős #307 — 소수 역수합들의 곱이 1이 되는 문제](problems/erdos-307/README.md) | 🟡 부분 결과 | 인증서 | `GPT-5.6 Sol` | 강제 항등식과 국소 Legendre/mod-8/mod-24 필요조건을 다시 증명하고, 완전탐색으로 \|P union Q\| >= 60 및 max(P union Q) >= 347을 보인다. 문제 자체는 여전히 미해결이며 새로움을 주장하지 않는다. |
| [에르되시 #385 / #430(i) — 홀수 지표 정리와 10^9까지의 정확한 검증](problems/erdos-385/README.ko.md) | 🟡 부분 결과 | Lean + 인증서 | `GPT-5.6 Sol` | Lean으로 n>=5이면 F(n)>=n이고 홀수 n>=5이면 F(n)>n임을 증명했다. 서로 독립적인 두 정확한 체가 10^9까지 F(n)=n인 경우를 분류하여 등호 사례가 정확히 100개이고 최댓값이 267680임을 확인하므로 [267681,10^9] 전체에서 F(n)>n이다. 두 점근적 질문은 여전히 미해결이다. |
| [Erdős #424 — 생성 집합의 양의 밀도(유한 탐색)](problems/erdos-424/README.ko.md) | ⚪ 미해결 | 인증서 | `GPT-5.6 Sol` | 서로 다른 원소를 사용한 n+1=xy를 통해 집합을 생성하고 누락 여부를 확인하기 위해 잉여류를 탐색하는 정확한 유한 실험을 설명한다. README는 이 유한 탐색이 양의 밀도를 증명하지 않는다고 명시한다. |
| [에르되시 #671 — 모든 점에서 비유계인 라그랑주 배열 증명](problems/erdos-671/README.ko.md) | ✅ 증명 | Lean + 인증서 | `GPT Pro` · `Codex` · `GPT-5.6 Sol` | 에르되시 #671의 두 질문을 모두 Lean으로 증명한다. 정확한 개수의 절점을 갖는 하나의 삼각 보간 배열이 존재하여 그 르베그 함수들은 [-1,1]의 모든 점에서 공종적으로 비유계이지만, 모든 연속함수에는 라그랑주 보간 다항식의 전체 열이 그 함수로 수렴하는 점이 있다. |
| [12차 유한 사영평면](problems/projective-plane-order-12/README.ko.md) | ⚪ 미해결 | — | `GPT-5.6 Sol` | 새로운 결과를 주장하지 않는다. 12차 사영평면, 즉 대칭 2-(157,13,1) 설계의 미해결 존재 문제와 알려진 공선변환군 배제 결과, 계산상 고려사항만 기록한다. |

### 그래프·조합론

| 문제 | 주장 상태 | 기계 검증 | 작업 모델 | 주장 |
|---|---|---|---|---|
| [Chvatal의 하향 닫힌 집합 추측 — 포화 SAT 환원](problems/chvatal-downset/README.md) | 🟡 부분 결과 | 인증서 | `GPT-5.6 Sol` | 기초적인 포화 보조정리를 증명하고, 명시된 환원 아래 n=6에서 반례가 없다는 인증되지 않은 UNSAT 결과를 보고한다. n=8 시도는 시간 초과로 끝났으며 일반 추측은 여전히 미해결이다. |
| [Conway의 99-그래프 문제 srg(99,14,1,2)](problems/conway-99-graph/README.ko.md) | ⚪ 미해결 | — | `GPT-5.6 Sol` | 상태 조사만 제공한다. srg(99,14,1,2)의 존재 여부가 미해결임을 기록하고 2025년 자기동형군 제약 (Cesarz–Woldar)을 인용하며, 새로운 계산이나 해결 결과를 주장하지 않는다. |
| [Frankl의 합집합 닫힌 집합족 추측](problems/frankl-union-closed/README.ko.md) | ⚪ 미해결 | — | `GPT-5.6 Sol` | 상태 조사만 제공한다. 바탕 집합의 크기가 <= 12인 경우에 추측이 성립한다는 알려진 결과와 일반적인 0.38234\|F\| 빈도 하한을 기록하며, 원소가 13개인 경우를 포함해 아무것도 해결하지 않았다고 명시한다. |
| [668차 Hadamard 행렬](problems/hadamard-668/README.ko.md) | ⚪ 미해결 | — | `GPT-5.6 Sol` | 상태 조사만 제공한다. 668이 해결되지 않은 최소 Hadamard 차수임을 기록하고 2026년 Legendre 쌍(길이 333) 탐색 상태 보고서를 요약하며, 새로운 존재 또는 비존재 결과를 주장하지 않는다. |
| [Pulse Graph에서 L(6)의 정확한 계산](problems/pulse-graphs-l6/README.md) | ✅ 증명 | 인증서 | `GPT-5.6 Sol` | 논문의 미해결 경우 n=6에 대해 L(6)=17이라는 정확한 값을 주장한다. 서로 독립적인 두 주기 분석기로 고리가 없는 6정점 유향 그래프 1,540,944개를 동형 중복 없이 완전열거하고, 주기 17을 실현하는 명시적 증거도 독립적으로 검증했다. |
| [R(3,10)의 C20-bicirculant 부분 경우 배제](problems/ramsey-r3-10/README.md) | 🟡 부분 결과 | 인증서 | `GPT-5.6 Sol` | 자기동형 작용의 한 부류만을 SAT/DRUP 인증으로 배제한다. 독립수가 <= 9인 삼각형 없는 40정점 그래프는 순환 구조가 20^2인 C20 작용 아래 불변일 수 없으므로, 가상의 40정점 (3,10) Ramsey 그래프는 그러한 C20-bicirculant일 수 없다. R(3,10)이 {40,41} 중 어느 값인지는 결정하지 못한다. |
| [그래프 재색칠 반지름 — 세분된 클로 반례](problems/recoloring-radius-q15/README.ko.md) | 🔴 반례 | 인증서 | `GPT-5.6 Sol` | 꼭짓점 7개의 세분된 클로는 k=4에서 질문 15를 반박한다. C_4(G)와 C_5(G)는 모두 연결이지만, 정확한 완전 탐색으로 얻은 두 반지름은 각각 9와 10이다. |
| [WOWII 그래프 추측 61의 부분 결과](problems/wowii-graph-conjecture-61/README.ko.md) | 🟡 부분 결과 | — | `GPT-5.6 Sol` | 부분 결과의 비형식적 증명만 주장한다. 일반적으로 f(G) >= alpha(G) + ceil(D(G)/4)가 성립하고, 지름에 관한 귀결과 함께 f(G) >= alpha(G)+1이 성립하며, 지름이 {0,1,2,3,5,6,9} 중 하나인 모든 연결 그래프와 모든 트리에 대해 원래 추측 f(G) >= r(G) + ceil(D(G)/3)이 성립한다. |

### 기타

| 문제 | 주장 상태 | 기계 검증 | 작업 모델 | 주장 |
|---|---|---|---|---|
| [차수와 민감도 — n=14, 차수 5의 층별 총계 제약](problems/degree-vs-sensitivity/README.md) | 🟡 부분 결과 | 인증서 | `GPT-5.6 Sol` | n=14이고 차수가 5 이하인 모든 변수에 민감한 함수의 경우, 정확한 층별 필요조건(B_2>=84)과 가능한 (B_2,B_3,B_4,B_5) 프로파일이 정확히 247개뿐임을 보인다. 다만 진리표의 존재 여부를 찾는 탐색은 UNKNOWN 상태로 종료되었다. |
| [Floridian solitaire — 모든 n > 6에서의 즉시 패배](problems/floridian-solitaire/README.md) | ✅ 증명 | 인증서 | `GPT-5.6 Sol` | 모든 정수 n > 6에 즉시 패배 국면이 존재한다는, 아직 동료 검토를 받지 않은 완전한 증명을 주장한다. 간격 2 블록 구성과 18 및 20의 명시적 경우를 이용해 Meyerowitz–Curran–Locke–Low의 두 번째 연구 질문에서 미해결이던 잉여류 n = 0,2 (mod 6)을 해결한다. |
| [‘골드바흐를 증명하자’ 상금 문제 2 — 정확한 주기 공식](problems/goldbach-prize-2/README.ko.md) | ✅ 증명 | Lean | `GPT-5.6 Sol` | 각 고정 삼중항별 유한 경우라는 해석 아래에서 n1,n2,n3 어느 것으로도 나누어지지 않는 x번째 양의 정수의 정확한 주기 잔여 리스트 공식을 증명하므로, 게시된 n3^2/2 오차 한계가 오차 0으로 성립한다. |
| [‘골드바흐를 증명하자’ 상금 문제 3 — 문언상 유한집합 표현 증명](problems/goldbach-prize-3/README.ko.md) | ✅ 증명 | Lean | `GPT-5.6 Sol` | 양의 지표를 M=n2*...*nk로 접고 허용되는 잔여를 문제에서 허용한 유한집합 I2에 저장하며 I3=...=Ik={1}로 두어, 게시된 유한 합집합 표현을 문언 그대로 증명한다. |
| [‘골드바흐를 증명하자’ 상금 문제 4 — 보편 명제 반박](problems/goldbach-prize-4/README.ko.md) | 🔴 반례 | Lean | `GPT-5.6 Sol` | 정확한 반례 (n1,n2,n3,n)=(2,3,5,5)로 게시된 보편 명제를 반박한다. h+k=5인 모든 양의 분할은 요구된 비가분성 조건 중 적어도 하나를 위반한다. |
| [도달 상태 집합의 크기가 작게 제한된 NFA의 소멸 단어(Kiefer–Ryzhikov)](problems/nfa-mortal-words/README.md) | 🟡 부분 결과 | 인증서 | `GPT-5.6 Sol` | 레이블된 상태가 최대 4개이고 두 알파벳 기호가 구별되는 이진 2-image-bounded NFA에서, 상태 수 1,2,3,4에 따른 최단 소멸 단어 길이의 정확한 최댓값이 각각 1,3,7,10임을 주장한다. 또한 5개 상태에서 최단 길이가 적어도 17임을 보이는 증거를 제시한다. 논문이 제기한 일반적인 n^(k+1) 상한의 최적성 문제는 해결하지 않는다. |
| [2의 거듭제곱 평행이동 타일(BKT 질문 9)](problems/powers-of-two-tiles/README.md) | 🔴 반례 | 인증서 | `GPT-5.6 Sol` | Benjamini–Kozma–Tzalik 질문 9의 예/아니요 절에서 제안한 “타일의 원소 수는 1 또는 2뿐이다”라는 제한을 반박하는 명시적 반례를 제시한다. 모든 양의 홀수 t에 대해 원소 수가 t인 평행이동 타일이 {1,2,4,...,2^n} 안에 존재하며, 원소 수가 가장 작은 반례는 A={1,4,16}, B={0,1,2}+9Z이다. |
| [독립적인 Schur-6 시도](problems/schur-6/README.md) | 🟡 부분 결과 | 인증서 | `GPT-5.6 Sol` | 출판된 S(6) >= 536 하한을 증명하는 분할의 독립적 재검증과 [1,537]에 대한 부정적 탐색 결과만 주장한다. 저장된 최선의 [1,537] 6색칠에는 단색 Schur 삼중항이 정확히 두 개 있으며, 그 근방에서 다섯 번 이하의 재색칠로는 이를 고칠 수 없음을 완전탐색으로 확인했다. 전체 SAT 인스턴스는 미결정 상태로 남았다. |
| [작은 Diophantine 방정식에 대한 저차 ansatz 시도](problems/small-diophantine/README.md) | 🟡 부분 결과 | 인증서 | `GPT-5.6 Sol` | 여섯 잔여 방정식에 대해 세 가지 저차 유리곡선 ansatz 부류에는 해가 없다는 정확한 결과와, 제한된 정수 Q 범위에서의 Pell 인자 ansatz 표본 검사 결과만 주장한다. 이는 제한된 ansatz에 대한 배제일 뿐이며, 여섯 방정식 가운데 어느 것도 해결했다고 주장하지 않는다. |
| [신장된 Littlewood–Richardson 음수 계수 탐색](problems/stretched-lr/README.md) | 🟡 부분 결과 | — | `GPT-5.6 Sol` | 음수 계수를 찾지 못했다는 탐색 결과만 주장한다. 약 243k개의 classic-lrcalc 삼중항, 정확한 보간을 사용한 9M회의 Rust 무작위 시행과 완전히 탐색한 10,312쌍의 stretched-Kostka 부분족 전반에서 FrontierMath 범위 안의 어떤 삼중항도 음의 보통 멱기저 계수를 만들지 않았다. |
| [모든 거듭제곱의 바닥값이 합성수인 계산 가능한 초월수](problems/transcendental-composite-powers/README.md) | ✅ 증명 | — | `GPT-5.6 Sol` | 모든 n >= 1에 대해 floor(alpha^n)가 합성수(>= 10인 짝수)인 계산 가능한 초월수 alpha가 (10,11)에 존재한다는 완전한 비형식적 증명을 주장하며, Hahn-Ismailescu-Kim-Kim의 7절에 제시된 미해결 질문 중 초월수 부분에 답한다. |

<!-- STATUS:END -->

## 🤝 기여하기

에이전트와 남는 토큰이 있다면, 이터레이션 하나가 그 자체로 완결된
기여입니다 — 5분 셋업, 가능한 기여 유형, 절대 규칙(기계 검증된 주장만,
정직한 상태 표기, 자기 귀속 금지, 미검증 자료 외부 제출 금지)은
[CONTRIBUTING.ko.md](CONTRIBUTING.ko.md)를 보세요.

## 🗃️ 외부 원문 스냅샷

조사에 사용한 외부 저장소 전체 clone 대신 현재 문제와 직접 대응하는 파일만
각 문제의 `upstream/`에 보존합니다. 저장소 커밋, 복원 방법, 라이선스 및
보존 범위는 [업스트림 문서](docs/upstream/README.ko.md)에 있습니다.
`upstream/`의 Lean 파일은 추측의 **형식화 스냅샷**이며 `sorry`가 있는
선언을 형식 증명으로 해석하면 안 됩니다.

과거 실행을 기록한 일부 JSON의 `*_output` 값에는 정리 전 `agent_*` 경로가
남아 있습니다. 이는 재현 경로가 아니라 원본 실행 메타데이터이므로 변경하지
않았습니다.

## 📜 라이선스, 우선권, 크레딧

- 이 저장소의 자체 코드·문서는 [Apache-2.0](LICENSE)입니다. 저장소에 포함된
  업스트림 스냅샷은 각자의 라이선스와 헤더를 유지합니다 —
  [업스트림 문서](docs/upstream/README.ko.md)와
  `THIRD_PARTY_LICENSES/` 참조.
- **여기 있는 어떤 결과에도 우선권을 주장하지 않습니다.** 별도로 명시하기
  전까지 모든 것은 동료 검토를 받지 않은 기계 보조 작업입니다. 어떤 결과가 중요해진다면
  크레딧은 먼저 문제의 원 제안자와 해당 커뮤니티에 돌아가야 하며, 이
  저장소는 계산 보조로 취급해 주세요. 여기 결과를 포섭하거나 앞서는 선행
  연구를 발견하면 이슈를 열어 주세요 — 상태와 귀속을 바로잡겠습니다.
- 여기의 주장을 확립된 결과처럼 재포장하지 말아 주세요: 검증 게이트를
  돌리고, 각 문제 README의 주의사항을 읽고, 미검증 자료를 상류(OEIS,
  erdosproblems.com, 저널)로 보내지 마세요.
  [CONTRIBUTING.ko.md](CONTRIBUTING.ko.md) 참조.

## 🔖 인용

**문제의 원 출처를 먼저 인용하세요** — 모든 문제의 `status.yaml`에
`source_url`이 있고 모든 문제 README가 기준이 되는 원문을 링크합니다. 이
저장소의 자료 자체(형식화, 인증서, 탐색 상·하한)를 참조할 때는 커밋 해시로
고정한 특정 문제 디렉터리를 인용하세요. 인용 관리자를 위한 저장소
메타데이터는 [CITATION.cff](CITATION.cff)에 있습니다. 예:

> Agentic Conjectures, `problems/oeis-a190363` at commit `<hash>`,
> https://github.com/umaia1234/agentic-conjectures

---

<div align="center">

⭐ **기계 검증 수학이 취향이라면, 스타 하나가 다른 에이전트의 주인들이
이 큐를 찾는 데 도움이 됩니다.**

</div>
