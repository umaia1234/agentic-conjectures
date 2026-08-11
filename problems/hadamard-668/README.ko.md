[English](README.md) | **한국어**

# Hadamard matrix of order 668

확인 기준일: 2026-08-11.

## 문제

원소가 `+1` 또는 `-1`인 `668 x 668` 행렬 `H` 중

```text
H H^T = 668 I
```

를 만족하는 행렬이 존재하는지를 묻는다.

## 현재 상태와 알려진 부분결과

Hadamard 추측은 4의 모든 배수 차수에서 이런 행렬의 존재를 예측한다.
2023년 동료평가 논문과 2026년 상태 보고서는 모두 668을 가장 작은 미해결
차수로 기록한다.

2026년 상태 보고서는 길이 333 Legendre pair를 찾는 충분조건 경로에서
다음을 보고한다.

- 9-compression의 PSD-compatible configuration 12,017,243개를 완전
  열거했다.
- 37-compression 휴리스틱에서 얻은 최선의 `L1` PSD 오차는 236이었다.

여기에는 668차 행렬의 존재 또는 비존재를 판정하는 새 결과가 없다.

## 논리적 범위에 대한 주의

길이 333인 Legendre pair가 존재하면 668차 Hadamard matrix를 구성할 수
있다. 그러나 임의의 668차 Hadamard matrix가 반드시 이 형태인 것은
아니다. 따라서 상태 보고서 초록의 “equivalently”를 전체 존재 문제에
대한 논리적 동치로 사용해서는 안 된다.

Legendre-pair, Goethals--Seidel, Williamson 등의 각 구조적 부분공간은
PSD 필터, meet-in-the-middle, SAT 또는 SMT로 탐색할 수 있다. 한 구성
부류에서의 UNSAT는 전체 Hadamard 문제의 비존재 증명이 아니다.

## FormalConjectures 원본

[로컬 upstream snapshot](upstream/README.md)은 정확히 `k=167`, 즉 order
668의 존재를 묻는 Lean 선언을 보존한다. 이 선언은 `sorry`가 있는 열린
문제 명제이며, 위의 구조적 탐색 현황은 그 해답이 아니다.

## 근거

- [Three-dimensional Hadamard matrices of Paley type](https://www.sciencedirect.com/science/article/pii/S107157972300148X),
  *Finite Fields and Their Applications* 92 (2023), 102306.
- Chojecki,
  [Computational Search for a Hadamard Matrix of Order 668 via Legendre Pairs of Length 333](https://www.ulam.ai/research/frontier-had.pdf),
  March 2026 (비동료평가 상태 보고서).
