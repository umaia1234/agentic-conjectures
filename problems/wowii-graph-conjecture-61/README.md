# WOWII Graph Conjecture 61

## 원 추측과 부분 결과

유한 단순 연결 그래프 \(G\)에 대해 \(f(G)\)를 최대 유도 숲의 정점 수,
\(r(G)\)를 Havel--Hakimi residue, \(D(G)\)를 지름이라 하자. 원 추측은

\[
f(G)\ge r(G)+\left\lceil\frac{D(G)}3\right\rceil
\]

이다. 이 폴더에서는 다음 네 결과를 증명한다.

1. 모든 유한 단순 연결 그래프에서
   \[
   f(G)\ge\alpha(G)+\left\lceil\frac{D(G)}4\right\rceil.
   \]
2. 정점이 두 개 이상이면 \(f(G)\ge\alpha(G)+1\)이고,
   \(f(G)=\alpha(G)+1\)이면 \(D(G)\le4\)이다.
3. 원 추측은
   \[
   D(G)\in\{0,1,2,3,5,6,9\}
   \]
   인 모든 연결 그래프에서 성립한다.
4. 모든 유한 나무는 지름과 관계없이 원 추측을 만족한다.

상세 증명은 [PROOF.md](PROOF.md)에 있다. 이 결과들은 일반 그래프의
나머지 지름을 닫지 않으므로 원 추측 전체의 해결이 아니다.

## FormalConjectures 원본

[로컬 upstream snapshot](upstream/README.md)은 원 부등식의 정확한 Lean
선언을 고정 commit에서 보존한다. 선언은 `sorry`가 있는 문제 명제이며,
이 폴더의 부분 결과들은 그 일반 명제를 닫지 않는다.

## 원문 상태와 검증 범위

- [WOWII Conjecture 61 원문
  링크](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)는
  FormalConjectures가 인용한 출처다.
- 2026-08-11에 확인한 FormalConjectures main commit
  `9118d083ffca1536f521f9a7d103201f537ea670`의
  [`GraphConjecture61.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/WrittenOnTheWallII/GraphConjecture61.lean)은
  원 부등식을 `category research open`으로 표시했다.
- 이 폴더에는 계산 인증서나 완성된 Lean 증명이 없다. 결론은
  [PROOF.md](PROOF.md)의 조합론적 논증과 기본 부등식
  \(r(G)\le\alpha(G)\)에 의존한다.
