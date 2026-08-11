[English](AGENTS.md) | **한국어**

# AGENTS.md — 자율 이터레이션 운영 프로토콜

이 저장소에서 작업하는 모든 에이전트 세션이 따르는 규칙이다. 목표는 공개
미해결 문제·추측을 골라 공격하고, **기계 검증 가능한 결과만** 축적하는 것.

## 철칙

1. **자기 모델·하네스 이름으로 작업에 서명한다 — 사람 신원은 계속 배제.**
   모델 귀속은 의무이며 정직해야 한다:
   - 모든 커밋 메시지는 작업 주체를 밝히는 트레일러 두 줄로 끝난다.
     예: `Model: GPT-5.6 Sol` + `Harness: Codex CLI`, 또는
     `Model: Claude Fable 5` + `Harness: Claude Code`.
   - PR 본문에도 같은 모델/하네스를 적는다.
   - 문제의 결과를 만들거나 바꾸면 해당 문제 `status.yaml`의
     `attribution:`(model, harness, scope)에 기록한다. 대시보드의
     "Solved by" 열이 여기서 생성된다.
   - **하지 않은 작업에 태그를 달거나 다른 모델을 사칭하지 않는다.**
     귀속도 수학과 같은 정직성 기준을 따른다.
   - 커밋 author/committer는 계속 **저장소 로컬 git 설정(umaia1234
     noreply)만** 사용 — 개인 계정·이메일 금지, `Co-Authored-By:` 트레일러
     금지(GitHub contributor 그래프를 바꾼다). 모델 귀속은 위의
     `Model:`/`Harness:` 트레일러로 한다.
   - push 전 반드시 `git log --format='%an <%ae>%n%B' -1`로 author가 저장소
     신원인지, 트레일러가 있는지 확인한다.
2. **모든 클레임은 기계가 재검증할 수 있어야 한다.** 반례는 독립 검증
   스크립트(가능하면 독립 구현 2개), SAT 결과는 DRUP/DRAT 인증서, 증명은
   Lean 4 (`sorry`·추가 공리·`native_decide` 금지). CI가 재검증하지 못하는
   주장은 `status.yaml`에서 그렇게 보이게 둔다 — 포장 금지.
3. **정직한 상태 표기.** `proved`/`refuted`는 완결 주장에만. 부분 결과·부정적
   탐색은 `partial`. 결과가 없어도 기록한다 — "N까지 반례 없음 + 코드 + 로그"는
   이 저장소의 정상 산출물이다. novelty는 외부 리뷰 전에는 절대 주장하지 않는다.
4. **main 직행 금지(자율 루프에서).** 작업은 `agent/<날짜>-<slug>` 브랜치 →
   push → PR → CI green 후 merge. force-push 금지 (사람이 명시 지시한 경우 제외).
5. **검증된 결과의 하향·삭제 금지.** 기존 `proved`/`refuted`를 끌어내리거나
   인증서를 지우는 변경은 사람 승인 필요. 오류 발견 시 상태를 고치되 경위를
   문제 README에 기록한다.
6. **문장 충실성.** 형식화는 `upstream/` 스냅샷 또는 출처 원문과 대조한다.
   README에 원문 인용과 출처 URL을 남기고, 우리 Lean 문장이 원문과 어긋날 수
   있는 지점(인덱스 기준, 뺄셈 semantics, 경계값)을 명시한다.
7. **외부 제출은 사람 승인 후.** OEIS 코멘트, formal-conjectures PR,
   erdosproblems 제보 등 저장소 밖으로 나가는 모든 것.
8. **문서 언어는 영어가 기본값이다.** 문서, 커밋 메시지, 코드 주석, PR 본문은
   영어로 쓴다. 사람이 읽을 한국어 번역본은 같은 위치에 `<이름>.ko.md`로
   두고, 두 파일 맨 위에서 상호 링크한다
   (영어 파일: `**English** | [한국어](<이름>.ko.md)`,
   한국어 파일: `[English](<이름>.md) | **한국어**`).
   문서를 고치면 같은 커밋에서 번역본도 함께 갱신한다.

## 이터레이션 파이프라인

한 번의 자율 이터레이션 = 아래 중 **하나의 유한한 작업 단위**:

1. **harvest** — 새 후보 수집(formal-conjectures 갱신분, erdosproblems.com,
   OEIS "conjectured" 항목, 최근 arXiv 마이너 추측). 선행연구 확인 필수:
   이미 해결된 문제는 그렇게 기록하고 버린다.
2. **triage** — 후보 점수화: 유한 탐색으로 반증 가능한가 / mathlib만으로
   형식화 가능한가 / 예상 컴퓨팅 예산 / 유명 문제 여부(유명 난제는 "해결
   대상"이 아니라 bound-추적 인프라로만).
3. **attack** — 반례 탐색 프로그램 작성·예산 내 실행, 또는 증명 작성 →
   Lean 형식화. 탐색은 실행 전 예상 시간을 추정하고 로컬 2시간을 넘기지
   않는다(더 길면 체크포인트 + 분할).
4. **verify** — 아래 게이트 전부 로컬 통과 후 커밋.
5. **report** — `status.yaml` 갱신 → `python3 scripts/gen_readme.py` →
   문제 README에 재현 명령·런타임 기록 → 브랜치 push + PR.

## 검증 게이트 (로컬에서 CI와 동일하게)

```
python3 scripts/check_imports.py    # 모든 Lean 모듈이 루트에서 도달 가능
python3 scripts/check_sorry.py      # sorry/admit/axiom/native_decide 금지
lake build                          # 전체 컴파일
python3 scripts/check_axioms.py     # #print axioms: 표준 3공리만 허용
python3 scripts/verify_all.py --ci  # ci_feasible 인증서 재실행
python3 scripts/gen_readme.py --check
```

## Lean 규약

- 루트 프로젝트 하나 (mathlib v4.30.0 핀). 문제당
  `AgenticConjectures/<ProblemId>.lean` 또는 하위 디렉터리.
- 새 모듈은 반드시 `AgenticConjectures.lean`에 import 추가 (CI가 강제).
- 열린 문제의 문장은 `def statement : Prop := ...`로 쓴다 — `sorry` 불필요.
  증명/반증은 `theorem ... : statement` / `theorem ... : ¬ statement`.
- 완성한 정리는 해당 문제 `status.yaml`의 `lean.modules`/`lean.theorems`에
  등록한다 (공리 감사 대상).
- upstream 스냅샷과의 대응(동일 명제인지, 어떤 시맨틱 차이가 있는지)을
  모듈 docstring에 기록한다.

## status.yaml 스키마

```yaml
id: <dirname>
title: "..."
domain: oeis | erdos | graph-combinatorics | other
source_url: "..."
claimed_status: proved | refuted | partial | open
claim: "한 문장 요약 (영어)"
artifacts: [{path, kind}]
verify:                     # 문제 디렉터리 기준, CI는 --ci로 ci_feasible만
  - cmd: "..."
    expected_runtime: "..."
    ci_feasible: true|false
    requires: [drat-trim]   # 선택: PATH에 있어야 하는 외부 도구
lean:                       # 형식화 후에만
  modules: [AgenticConjectures.Foo]
  theorems: [AgenticConjectures.Foo.bar]
attribution:                # 작업 주체 (철칙 1)
  - model: "GPT-5.6 Sol"
    harness: "unspecified"
    scope: "original research artifacts"
  - model: "Claude Fable 5"
    harness: "Claude Code"
    scope: "Lean 4 formalization"
notes: "회의적 리뷰어가 알아야 할 것"
```

## 컴퓨팅·디스크 규약

- 컴파일 산출물은 `build/` 하위(이미 gitignore) 또는 `/tmp`. 바이너리 커밋 금지.
- 대용량 산출물(>5MB)은 커밋 전 필요성 검토 — 재생성 가능하면 명령만 기록.
- 이 머신은 디스크 여유가 작다. 큰 임시 파일은 `/tmp`에 쓰고 정리한다.
