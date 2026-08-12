[English](README.md) | **한국어**

# 그래프 색칠 재구성 반지름: 질문 15의 반례

Cambie–Cames van Batenburg–Cranston 질문 15는 거짓이다. 꼭짓점 7개의
세분된 클로가 \(k=4\)에서 \(k+1=5\)로 넘어갈 때의 반례를 준다.

## 결과

\(K_{1,3}\)의 모든 변을 한 번씩 세분하여 얻은 나무를 \(T\)라 하자.
꼭짓점을 \(0,\ldots,6\)으로 두고 다음 변을 사용한다.

```text
E(T) = {03, 06, 14, 16, 25, 26}.
```

따라서 꼭짓점 6은 중심이고, 0, 1, 2는 차수 2인 세분 꼭짓점이며,
3, 4, 5는 잎이다. 이 그래프의 graph6 인코딩은 `FCOf?`이다. 정확한
계산 결과는 다음과 같다.

| 재색칠 그래프 | 올바른 색칠 수 | 재색칠 변 수 | 연결 | 반지름 | 지름 |
|---|---:|---:|:---:|---:|---:|
| \(\mathcal C_4(T)\) | 2,916 | 15,876 | 예 | 9 | 10 |
| \(\mathcal C_5(T)\) | 20,480 | 178,560 | 예 | 10 | 10 |

특히 다음이 성립한다.

\[
  \operatorname{rad}\mathcal C_4(T)=9
  <10=\operatorname{rad}\mathcal C_5(T).
\]

\(4\ge3\)이고 두 재색칠 그래프가 모두 연결성 가정을 만족한다. 따라서 이
그래프 하나로 보편 명제가 반박된다.

## 출처와 명제

그래프 \(G\)의 \(k\)-재색칠 그래프 \(\mathcal C_k(G)\)는 \(G\)의 올바른
\(k\)-색칠을 꼭짓점으로 삼는다. 두 색칠은 정확히 한 꼭짓점의 색만 다를 때
인접한다. 출판된 질문은 \(k\ge3\)이고 연속한 두 재색칠 그래프가 모두 연결일
때 다음 부등식이 항상 성립하는지를 묻는다.

> “\(\operatorname{rad}\mathcal C_k(G)\ge
> \operatorname{rad}\mathcal C_{k+1}(G)\)가 반드시 성립하는가?”

일차 출처: Stijn Cambie, Wouter Cames van Batenburg, Daniel W. Cranston,
“Sharp Bounds on Lengths of Linear Recolouring Sequences,”
*Electronic Journal of Combinatorics* 33(1) (2026), #P1.18,
[doi:10.37236/13788](https://doi.org/10.37236/13788), 질문 15.

## 기계 검증 인증서

[`counterexample.json`](counterexample.json)은 그래프와 주장하는 모든 정수를
고정한다. 서로 독립적인 두 구현이 저장된 탐색 로그를 신뢰하지 않고 완전한
재색칠 그래프를 매번 다시 구성한다.

1. [`recolor_radius_exact.cpp`](recolor_radius_exact.cpp)는 색칠을 \(k\)진법
   정수로 인코딩하고, 가능한 모든 한 꼭짓점 재색칠 이동을 구성하여 연결성을
   확인한 뒤 정수 BFS로 정확한 반지름을 계산한다.
2. [`verify_counterexample.py`](verify_counterexample.py)는 별도의 graph6
   해독기, 튜플 색칠, 표준 라이브러리의 deque BFS를 사용한다. 자체 계산을
   모두 마친 뒤에만 C++ 프로그램을 실행하여 두 결과를 비교한다.

색 이름의 전역 치환은 각 재색칠 그래프의 자기동형을 이룬다. 따라서 두 구현은
색 이름 치환 궤도마다 제한 성장 대표 하나를 BFS 시작점으로 사용한다. Python
인증서는 이 궤도 분해가 레이블된 모든 상태를 정확히 덮는지 검사하고,
\(k=4\)의 대표 122개와 \(k=5\)의 대표 187개 모두에서 가지치기 없는 완전한
BFS를 실행한다.

내부 검사로 상태 수는 나무의 공식 \(k(k-1)^6\)과도 일치한다. \(k=4\)에서는
레이블된 상태 192개의 이심률이 9이고 나머지 2,724개의 이심률이 10이다.
\(k=5\)에서는 20,480개 상태의 이심률이 모두 10이다. 이 분포가 두 반지름을
각각 확정한다.

자세한 전개와 인증서 불변식은 [`DETAILS.ko.md`](DETAILS.ko.md)에 기록되어
있다.

## 재현

저장소 루트에서 다음을 실행한다.

```bash
g++ -O3 -std=c++17 \
  problems/recoloring-radius-q15/recolor_radius_exact.cpp \
  -o /tmp/recolor_radius_exact
python3 problems/recoloring-radius-q15/verify_counterexample.py \
  --cpp /tmp/recolor_radius_exact
```

예상 출력은 다음과 같다.

```text
PASS graph6 FCOf? decodes as the 7-vertex subdivided claw
PASS independent Python exhaustive BFS: C_4 connected, 2916 states, 15876 edges, radius 9, diameter 10
PASS independent Python exhaustive BFS: C_5 connected, 20480 states, 178560 edges, radius 10, diameter 10
PASS independent C++ exact-radius results agree
PASS counterexample: 9 < 10 (...s)
```

기록된 로컬 실행은 1.87초가 걸렸고 최대 상주 메모리는 약 23 MB였다.
검증기에는 C++17 컴파일러와 Python 표준 라이브러리만 필요하다.

## 보존한 이전 탐색 결과

고정된 [`atlas_1_7.g6`](atlas_1_7.g6) 데이터셋과 두 검증기는 별도의 유한
범위 결과로 남아 있다. 꼭짓점이 1개에서 7개인 단순 그래프의 비동형류
1,252개를 모두 \(k=3\)에서 \(k=4\)로 넘어가는 비교에 대해 검사한다. 정확히
145개에서 두 재색칠 그래프가 모두 연결이고 반례는 없다. 데이터셋의 SHA-256은
`ad68465d32eb7679a1ed8b0aa7a7f1da366da9b1ef8566b04664c504e8876255`이다.
이번 반례는 \(k=4\)를 사용하므로 이 결과와 모순되지 않는다.

같은 컴파일된 바이너리로 이 검증을 다시 실행하려면 다음 명령을 사용한다.

```bash
python3 problems/recoloring-radius-q15/verify_atlas.py \
  --cpp /tmp/recolor_radius_exact
```

## 원문 충실성과 범위

인증서는 유한 무향 단순 그래프, 팔레트 \(\{0,\ldots,k-1\}\)를 쓰는 레이블된
올바른 색칠, 한 꼭짓점 재색칠 이동, 보통의 그래프 거리, 최소 이심률로 정의한
반지름을 사용한다. 이는 출판된 정의와 일치한다. 색 이름을 0부터 쓰는지
1부터 쓰는지는 수학적 차이가 없다. 최종 출판본에서는 이 명제가 질문 15이며,
이전 원고의 번호는 달랐다.

이 저장소는 기계로 검증한 반례를 기록한다. 외부 검토 전에는 출판 우선권이나
새로움을 주장하지 않는다.
