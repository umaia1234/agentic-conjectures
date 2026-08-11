# Agentic Conjectures

연구 메모, 인증 코드, 계산 산출물을 **문제 단위**로 정리한 작업공간입니다.

- `problems/`: 한 디렉터리에 한 문제의 증명·코드·증인·결과를 배치합니다.
- 문제와 직접 대응하는 외부 Lean 원문은 해당 문제의 `upstream/`에 둡니다.
- `archive/`: 문제를 확정하지 못한 유산 자료만 격리합니다.

재현 명령은 각 문제의 `README.md`를 따릅니다. `problems/...`로 시작하는
경로는 이 작업공간 루트 기준이고, basename만 쓴 명령은 해당 문제
디렉터리 기준입니다.

## 문제 목록

| 분류 | 문제 디렉터리 |
|---|---|
| OEIS | [A000224](problems/oeis-a000224/README.md), [A056777](problems/oeis-a056777/README.md), [A060841](problems/oeis-a060841/README.md), [A063880](problems/oeis-a063880/README.md), [A067720](problems/oeis-a067720/README.md), [A076141](problems/oeis-a076141/README.md) |
| OEIS | [A136433](problems/oeis-a136433/README.md), [A190363](problems/oeis-a190363/README.md), [A245211](problems/oeis-a245211/README.md), [A297707](problems/oeis-a297707/README.md), [A340881](problems/oeis-a340881/README.md) |
| OEIS | [A354747](problems/oeis-a354747/README.md), [A395412](problems/oeis-a395412/README.md), [A397245](problems/oeis-a397245/README.md), [A397621](problems/oeis-a397621/README.md) |
| Erdős | [#307](problems/erdos-307/README.md), [#385 / #430(i)](problems/erdos-385/README.md), [#424](problems/erdos-424/README.md) |
| 그래프·조합론 | [Ramsey R(3,10)](problems/ramsey-r3-10/README.md), [Conway 99-graph](problems/conway-99-graph/README.md), [WOWII Graph Conjecture 61](problems/wowii-graph-conjecture-61/README.md), [Floridian solitaire](problems/floridian-solitaire/README.md), [Pulse Graphs L(6)](problems/pulse-graphs-l6/README.md) |
| 그래프·조합론 | [Frankl union-closed](problems/frankl-union-closed/README.md), [Chvátal downset](problems/chvatal-downset/README.md), [12차 유한 사영평면](problems/projective-plane-order-12/README.md), [668차 Hadamard](problems/hadamard-668/README.md) |
| 그래프·조합론 | [recoloring radius Q15](problems/recoloring-radius-q15/README.md), [powers-of-two tiles](problems/powers-of-two-tiles/README.md), [Schur S(6)](problems/schur-6/README.md) |
| 기타 | [mortal NFA words](problems/nfa-mortal-words/README.md), [degree vs sensitivity](problems/degree-vs-sensitivity/README.md), [stretched LR](problems/stretched-lr/README.md), [small Diophantine equations](problems/small-diophantine/README.md), [transcendental composite powers](problems/transcendental-composite-powers/README.md) |

## 외부 원문 스냅샷

조사에 사용한 외부 저장소 전체 clone 대신 현재 문제와 직접 대응하는 파일만
각 문제의 `upstream/`에 보존합니다. 저장소 커밋, 복원 방법, 라이선스 및
보존 범위는 [UPSTREAM_SOURCES.md](UPSTREAM_SOURCES.md)에 있습니다.

과거 실행을 기록한 일부 JSON의 `*_output` 값에는 정리 전
`agent_*` 경로가 남아 있습니다. 이는 재현 경로가 아니라 원본 실행
메타데이터이므로 변경하지 않았습니다.
