[English](README.md) | **한국어**

# Finite projective plane of order 12

확인 기준일: 2026-08-11.

## 문제

order 12인 유한 projective plane이 존재하는지를 묻는다. 이는 대칭
`2-(157,13,1)` design의 존재와 동치이다. 행과 열의 합이 13인
`157 x 157` 영일 incidence matrix `A`를 사용하면 조건을

```text
A A^T = 12 I + J
```

로 쓸 수 있다.

## 현재 상태와 알려진 부분결과

2026년 1차 자료는 12를 존재 여부가 알려지지 않은 가장 작은 order로
기록한다. 2023년 논문은 order 4인 collineation group을 배제했고, 기존
결과와 합치면 가능한 전체 collineation group의 order는 1, 2, 3뿐이다.

이 디렉터리는 문제와 계산 후보로서의 성격만 기록하며 새로운 존재·비존재
결과를 주장하지 않는다.

## 계산 관점

Incidence 조건은 exact cover나 SAT로 표현하기 좋지만 변수 수가 크다.
알려진 대칭 배제 결과 때문에 큰 순환대칭을 가정하는 비교적 쉬운 탐색은
이미 막혀 있다. 따라서 trivial 또는 매우 작은 자기동형군을 다루는
canonical search가 핵심 병목이다.

## FormalConjectures 원본

[로컬 upstream snapshot](upstream/README.md)은 Erdős problem 723의
`eq_12` Lean 선언과 고정 commit 정보를 보존한다. 선언은 `sorry`가 있는
존재 문제 명제이고, 이 디렉터리는 새 존재·비존재 결과를 주지 않는다.

## 근거

- Alexeev--Mixon,
  [Forbidden Sidon subsets of perfect difference sets](https://arxiv.org/html/2510.19804v2)
  (2026 판).
- Akiyama--Suetake--Tanaka,
  [Projective planes of order 12 do not have a collineation group of order 4](https://doi.org/10.1002/jcd.21869),
  *Journal of Combinatorial Designs* 31 (2023), 87--123.
