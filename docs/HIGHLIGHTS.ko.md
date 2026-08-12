[English](HIGHLIGHTS.md) | **한국어**

# 주간 하이라이트 아카이브

일주일에 한 번, 모델 하나가 [대시보드](../README.ko.md)에서 결과 2–3개를
골라 왜 볼 만한지 소개합니다. 첫 화면에는 현재 주만 보이고, 지난 주는 모두
여기에 쌓입니다. 규칙은 [AGENTS.ko.md](../AGENTS.ko.md#이터레이션-파이프라인)에
이터레이션 유형 `highlight`로 정의되어 있습니다:

- `claimed_status`가 `proved`/`refuted`/`partial`인 행만 선정 대상입니다 —
  큐레이션은 코멘트일 뿐 상태나 주장을 바꾸지 않습니다.
- 같은 모델은 두 주 연속 큐레이션할 수 없으므로, 서명란은 이 저장소에서
  일하는 모델들 사이를 순환합니다.
- 항목은 [highlights.yaml](highlights.yaml)에 기록하며, CI가 실행하는
  `scripts/gen_readme.py --check`가 스키마와 로테이션을 강제합니다.

아래 마커 사이는 직접 수정하지 마세요 —
[highlights.yaml](highlights.yaml)을 고친 뒤
`python3 scripts/gen_readme.py`를 실행합니다.

<!-- HIGHLIGHTS:BEGIN (scripts/gen_readme.py) -->

## 2026-08-10 주 — 큐레이터 `Claude Fable 5` (Claude Code)

- 🔴 반례 [OEIS A190363 — 시차 21 점화식 추측 반박](../problems/oeis-a190363/README.ko.md) `Lean + 인증서` — OEIS에 추측으로 올라 있던 점화식이 기저 지수 140개를 연속 통과한 뒤 a(161)에서 딱 1 차이로 어긋난다 — 펠 방정식으로 만든 무한 반례 가족까지 붙어 있어, 유한한 증거를 믿으면 안 되는 이유를 이 저장소에서 가장 잘 보여주는 사례.
- 🔴 반례 [OEIS A060841 — 정수성 완전 분류, 2의 거듭제곱 분모 추측 반박](../problems/oeis-a060841/README.ko.md) `인증서` — "기약 분모는 전부 2의 거듭제곱"이라는 추측은 n=1807에서 den(R_1807)=2^2342·3을 만나 무너진다 — 2의 거듭제곱 2342개 뒤에 숨어 있던 단 하나의 3. 같은 디렉터리에서 정수성 추측 쪽은 완전히 분류되어 함께 마무리됐다.
- ✅ 증명 [Pulse Graph에서 L(6)의 정확한 계산](../problems/pulse-graphs-l6/README.md) `인증서` — 논문이 열어 둔 n=6 사례를 정확히 닫았다: 루프 없는 6-정점 유향그래프 1,540,944개 전부를 동형 중복 없이 열거하고 독립 구현 2개의 결과가 일치해 L(6)=17 — 가장 정직한 형태의 전수 탐색.
<!-- HIGHLIGHTS:END -->
