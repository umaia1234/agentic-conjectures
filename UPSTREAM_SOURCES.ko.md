[English](UPSTREAM_SOURCES.md) | **한국어**

# Upstream source snapshots

이 작업공간에서 조사에 사용한 외부 저장소 전체 복제본은 문제별 정리 후
삭제했습니다. 현재 문제와 직접 대응하는 Lean 원문은 각 문제 디렉터리의
`upstream/`에 보존하고, 대응하는 성공 결과가 없던 AlphaProof Nexus 기록은
해당 문제의 `README.md`에 사실과 범위만 남겼습니다.

## 고정한 저장소 상태

| 저장소 | 커밋 | 당시 용도 |
|---|---|---|
| [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) | [`9118d083ffca1536f521f9a7d103201f537ea670`](https://github.com/google-deepmind/formal-conjectures/tree/9118d083ffca1536f521f9a7d103201f537ea670) | 2026-08-11 `main`; 수동 OEIS·Erdős·WOWII·기타 형식화의 canonical 원문 |
| [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) | [`67338a157bbb8d87e9a349d662f82a868bda6327`](https://github.com/google-deepmind/formal-conjectures/tree/67338a157bbb8d87e9a349d662f82a868bda6327) | `auto_oeis` 작업 스냅샷; 자동 형식화 OEIS 원문 |
| [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) | [`7a41db3d761324599812d6ca6cb6a9f311046dc7`](https://github.com/google-deepmind/formal-conjectures/tree/7a41db3d761324599812d6ca6cb6a9f311046dc7) | FormalBench 후보 집합을 확인한 스냅샷 |
| [Formal Conjectures PR #4450](https://github.com/google-deepmind/formal-conjectures/pull/4450) | [`93dc5e41789aadbd85380183779a94e7a59cb80e`](https://github.com/google-deepmind/formal-conjectures/tree/93dc5e41789aadbd85380183779a94e7a59cb80e) | 정확한 명제 비교에 사용한 진행 중인 A112970 형식화 |
| [AlphaProof Nexus Results](https://github.com/google-deepmind/alphaproof-nexus-results) | [`0647711a71183c1ea492ad60860776617ce1ea88`](https://github.com/google-deepmind/alphaproof-nexus-results/tree/0647711a71183c1ea492ad60860776617ce1ea88) | 공개 성공 결과와 시도 목록의 교집합 감사 |

모든 원문 작업트리는 삭제 직전 `git status --short`가 비어 있었습니다.
`formal-auto-oeis`, `formal-bench`, 진행 중 PR checkout은 Formal
Conjectures clone의 detached linked worktree였고, 나머지 둘은 독립
clone이었습니다.

## 보존 범위

- 대응 Lean 파일은 원래 basename, 저작권 헤더, 정확한 바이트를 유지합니다.
- 각 `upstream/README.md`에는 원래 경로, 고정 커밋 URL, SHA-256, 중심 선언,
  현재 문제 결과와의 관계를 기록합니다.
- 이 파일들은 원 추측의 **형식화 스냅샷**입니다. `sorry`가 있는 선언을
  형식 증명으로 해석하면 안 됩니다.
- Formal Conjectures 전용 import와 보조 정의 전체를 다시 vendoring하지
  않았으므로 로컬 Lean 파일 하나만으로는 보통 컴파일되지 않습니다. 빌드가
  필요하면 아래처럼 해당 커밋의 원 저장소를 복원해야 합니다.
- 현재 35개 문제와 무관한 수천 개 형식화, `.git` 객체, `.lake` 캐시, 사이트
  소스와 CI 설정은 문제 디렉터리로 복제하지 않았습니다.

## 원 저장소 복원

```bash
git clone https://github.com/google-deepmind/formal-conjectures.git /tmp/formal-conjectures
git -C /tmp/formal-conjectures fetch origin 9118d083ffca1536f521f9a7d103201f537ea670
git -C /tmp/formal-conjectures checkout 9118d083ffca1536f521f9a7d103201f537ea670

git -C /tmp/formal-conjectures fetch origin 93dc5e41789aadbd85380183779a94e7a59cb80e
git -C /tmp/formal-conjectures checkout 93dc5e41789aadbd85380183779a94e7a59cb80e

git clone https://github.com/google-deepmind/alphaproof-nexus-results.git /tmp/alphaproof-nexus-results
git -C /tmp/alphaproof-nexus-results checkout 0647711a71183c1ea492ad60860776617ce1ea88
```

다른 두 Formal Conjectures 스냅샷도 같은 clone에서 해당 커밋을 fetch하고
checkout하면 복원할 수 있습니다. 위의 두 번째 checkout은 진행 중인 PR
#4450의 보존된 head를 선택합니다.

## 라이선스와 제3자 출처

복사한 Formal Conjectures Lean 소스는 원문의 Apache-2.0 저작권 헤더를
유지합니다. [Apache-2.0 전문](THIRD_PARTY_LICENSES/Apache-2.0.txt)도 함께
보존했고 [upstream AUTHORS](THIRD_PARTY_LICENSES/Formal-Conjectures-AUTHORS.txt)도
같은 snapshot에서 옮겼습니다. 원 저장소는 기타 자료를 CC BY 4.0으로 배포하며, OEIS,
Wikipedia, MathOverflow에서 유래한 자료에는 CC BY-SA 4.0 등 원 출처의
조건이 별도로 적용될 수 있다고 고지합니다. 각 문제의 canonical 원문 링크와
고정 upstream 링크를 함께 유지하는 이유입니다.
