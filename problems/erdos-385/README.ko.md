[English](README.md) | **한국어**

# Erdős problem #385 / #430(i)

공식 문제 번호는 #385입니다. 소스 파일의 `ep430_*` 이름은 #430의 첫
질문과의 동치 관계를 따라 작성된 기존 이름이므로, 재현 이력을 위해
유지했습니다. 두 프로그램은 유한 범위 실험이며 전체 문제의 증명은
아닙니다.

## FormalConjectures upstream

[로컬 upstream snapshot](upstream/README.md)은 parts (i), (ii)와 하한
변형의 정확한 Lean 명제를 보존한다. 연구 명제들은 `sorry`를 포함하며,
아래 유한 범위 계산은 그 어느 것도 증명하지 않는다.

## AlphaProof Nexus benchmark provenance

Google DeepMind의 AlphaProof Nexus `science-submission` 스냅샷 commit
[`0647711a71183c1ea492ad60860776617ce1ea88`](https://github.com/google-deepmind/alphaproof-nexus-results/tree/0647711a71183c1ea492ad60860776617ce1ea88)의
고정된 [시도 목록](https://github.com/google-deepmind/alphaproof-nexus-results/blob/0647711a71183c1ea492ad60860776617ce1ea88/erdos_problems_attempted.txt)에는
`erdos_385.parts.i`, `erdos_385.parts.ii`, `erdos_385.variants.lb`가 모두
기록되어 있다. 그러나 해당 스냅샷의 `APNOutputs/ErdosProblems`와
`NaturalLanguageProofs/ErdosProblems`에는 #385의 성공 결과가 없다.
따라서 이는 시도 이력이지 해결 결과가 아니다. 아래 C++ 프로그램은
parts (i)와 (ii)의 수량 `F(n)-n`을 유한 범위에서만 조사하며, 이 세
추측 중 어느 것도 증명하지 않는다.

```bash
g++ -O3 -std=c++17 problems/erdos-385/ep430_experiment.cpp -o /tmp/ep385
g++ -O3 -std=c++17 problems/erdos-385/ep430_segmented.cpp -o /tmp/ep385_segmented
```
