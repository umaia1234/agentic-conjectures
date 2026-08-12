[English](CONTRIBUTING.md) | **한국어**

# 기여하기

에이전트와 남는 토큰이 있다면 미해결 문제에 붙여보세요. 이 저장소는 자율
에이전트(Claude Code, Codex, 프로토콜 파일을 읽고 셸 명령을 실행할 수 있는
어떤 도구든)가 문제를 골라 공격하고, **기계 검증된 결과만** 남기도록
설계되어 있습니다.

## 5분 요약

1. 저장소를 fork하고 clone합니다.
2. 저장소 안에서 에이전트를 시작하고 이 킥오프 프롬프트를 줍니다:

   ```text
   Read AGENTS.md and follow it exactly. Run one iteration: pick one problem
   from the README dashboard whose claimed_status is partial or open (or
   harvest a new small conjecture into a new problems/<id>/ directory).
   Attack it. Before committing, pass every verification gate locally. Update
   the problem's status.yaml and README,
   regenerate the dashboard, and open a pull request from a branch.
   Sign your work: end every commit with Model:/Harness: trailers naming
   yourself, state the same pair in the PR body, and add yourself to the
   problem's status.yaml attribution block.
   ```

3. 에이전트가 작업하고, CI가 PR을 판정합니다. CI가 green이면 PR의 주장이
   기계 검증된 것이고, CI가 못 보는 부분은 `status.yaml`에 정직하게
   표기되어야 합니다 (리뷰에서 강제).

Claude Code는 `CLAUDE.md`를 통해 프로토콜을 자동으로 읽고, 다른 도구는
관례상 `AGENTS.md`를 읽습니다. 특정 벤더 전용 요소는 없습니다.

## 어떤 기여가 가능한가

대체로 실현 가능성이 높은 순서로:

- **Lean 형식화**: 현재 비형식 증명만 있는 결과(`proved`/`refuted`인데
  Machine checks에 `lean`이 없는 행)의 형식화. 가치 대비 위험이 가장 낮은
  작업입니다.
- **탐색 범위 확장**: 재현 가능한 코드와 실행 시간 기록을 동반한
  "N까지 반례 없음" — 이 저장소의 정상 산출물입니다.
- **새 소형 문제 수확**: 자동 형식화된 OEIS 추측, 소규모 조합론, 최근
  논문의 마이너 추측을 새 `problems/<id>/`로 — 정직한 `status.yaml`과 함께.
- **기존 `open`/`partial` 문제의 반례나 증명.**
- **독립 재검증**: 기존 인증서에 대한 독립 구현 검증기 추가.

유명 문제(Frankl, Conway 99-graph, Hadamard 668, 12차 사영평면, R(3,10) 등)는
bound 추적 인프라입니다 — "해결" 주장 금지, 인증된 점진적 배제는 환영.

## 절대 규칙 ([AGENTS.md](AGENTS.ko.md) 요약)

- 모든 클레임은 기계 재검증 가능해야 합니다: 반례는 독립 스크립트, SAT은
  DRUP/DRAT, 증명은 sorry 없는 Lean 4 (`sorry`·추가 공리·`native_decide`
  금지, CI가 검사).
- 정직한 상태 표기. 외부 리뷰 전 novelty 주장 금지. 부정적 결과도 결과.
- 작업에 서명: 모든 커밋은 `Model:`/`Harness:` 트레일러로 끝나고
  (예: `Model: GPT-5.6 Sol` / `Harness: Codex CLI`), PR 본문에 같은 쌍을
  적고, 문제 `status.yaml`의 `attribution`에 자신을 추가합니다 —
  대시보드의 `Solved by` 열이 여기서 생성됩니다. 하지 않은 작업에 태그
  금지. 커밋 author는 저장소 로컬 신원 유지, `Co-Authored-By` 트레일러
  금지(contributor 그래프를 바꿉니다).
- 문서는 영어 기본. 한국어 `.ko.md` 병행은 환영하지만 문제 문서에서는
  선택 (원문을 고치면 기존 병행본도 갱신). 문제별 자료는
  `problems/<id>/`에 두고, `docs/`는 저장소 전역 참고 문서에만
  사용하며, 계속 바뀌는 색인은 수동 복사 대신 구조화된 정보에서 생성.
- 이 저장소에서 파생된 것을 외부(OEIS, erdosproblems.com, 저널, upstream
  저장소)에 제출하려면 먼저 여기에 이슈를 여세요. 미검증 기계 산출물을
  상류로 보내는 것은 스팸이고 모두에게 해가 됩니다 — 우리가 적극적으로
  막는 유일한 오용 형태입니다.

## 로컬 검증 게이트 (CI와 동일)

```bash
pip install pyyaml sympy
python3 scripts/verify_all.py --ci        # 인증서 재실행
lake exe cache get && lake build          # Lean 라이브러리 (첫 실행은 ~5 GB 다운로드)
python3 scripts/check_imports.py
python3 scripts/check_sorry.py
python3 scripts/check_axioms.py
python3 scripts/gen_readme.py --check
python3 scripts/gen_upstream_docs.py --check
python3 scripts/check_docs.py
```

## 리뷰 기준

PR은 정확히 두 가지를 봅니다: (1) CI green, (2) `status.yaml`의 주장이
실제 검증된 내용·주의사항과 일치하는가. Lean 형식화의 문장 충실성(형식
문장이 인용된 출처와 일치하는가)은 특별히 꼼꼼히 봅니다 — 문제 README에
원문을 인용하고 시맨틱 차이를 기록하세요.
