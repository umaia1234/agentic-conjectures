[English](README.md) | **한국어**

# Frankl's union-closed sets conjecture

확인 기준일: 2026-08-11.

## 문제

`{empty set}` 하나만으로 이루어진 경우를 제외한 모든 유한 union-closed
family `F`에 대해, `|F|/2`개 이상의 member set에 포함되는 원소가 항상
존재하는지를 묻는다.

## 현재 상태와 알려진 부분결과

2026년 저널 게재 논문도 이를 추측으로 다루며 최소 반례가 만족해야 할 새
필요조건을 제시한다. 알려진 계산 보조 결과와 일반 하한은 다음과 같다.

- ground set 크기 12 이하에서는 추측이 성립한다.
- 일반적인 family에는 적어도 한 원소가 약 `0.38234 |F|`개의 집합에
  포함된다는 무차원 하한이 증명되어 있다.

따라서 ground set 크기 13은 완전 확인된 범위 바로 다음의 유한 경우이다.
이 말은 13이 최소 반례의 크기라고 알려졌다는 뜻은 아니다.

## 계산 관점

ground set 크기 13에는 가능한 member set가 8,192개 있다. Union closure,
원소별 빈도 상한, 동형 제거를 SAT, ILP 또는 BDD에 함께 넣을 수 있다.
계산 결과를 일반 정리로 해석하려면 전체 경우의 포괄성과 인증 가능한
UNSAT 증명이 필요하다.

## FormalConjectures 원본

[로컬 upstream snapshot](upstream/README.md)은 일반 Frankl 추측과 알려진
12원소 변형의 Lean 명제를 함께 보존한다. 두 선언의 `sorry`는 명제
표시일 뿐 이 파일 안의 형식 증명이 아니며, 이 디렉터리도 13원소 경우를
해결하지 않는다.

## 근거

- [Bouchard, *Le Matematiche* 81(1), 2026](https://arxiv.org/abs/2503.00277)
- [Vuckovic--Zivkovic의 12원소 계산 증명](https://ipsitransactions.org/journals/papers/tir/2017jan/p9.pdf)
- [Yu의 `0.38234` 하한](https://www.mdpi.com/1099-4300/25/5/767)
