[English](README.md) | **한국어**

# 그래프 색칠 재구성 반지름, 질문 15

이 디렉터리는 Cambie–Cames van Batenburg–Cranston 질문 15에 대한 정확한
유한 범위 검증을 기록한다. \(k=3\)일 때 꼭짓점이 1개에서 7개인 모든 단순
그래프에서 반례가 없다. 이는 유한 범위의 부분 결과이며 일반적인
질문은 여전히 미해결이다.

## 출처와 명제

그래프 \(G\)의 \(k\)-재색칠 그래프 \(\mathcal C_k(G)\)는 \(G\)의 올바른
\(k\)-색칠을 꼭짓점으로 삼는다. 두 색칠은 정확히 한 꼭짓점의 색만 다를 때
인접한다. 출판된 질문은 \(k\ge3\)이고 연속한 두 재색칠 그래프가 모두
연결되어 있을 때 다음 부등식이 항상 성립하는지를 묻는다.

> “\(\operatorname{rad}\mathcal C_k(G)\ge
> \operatorname{rad}\mathcal C_{k+1}(G)\)가 반드시 성립하는가?”

일차 출처: Stijn Cambie, Wouter Cames van Batenburg, Daniel W. Cranston,
“Sharp Bounds on Lengths of Linear Recolouring Sequences,”
*Electronic Journal of Combinatorics* 33(1) (2026), #P1.18,
[doi:10.37236/13788](https://doi.org/10.37236/13788), 질문 15.

## 정확한 유한 범위 결과

고정된 graph6 데이터셋은 꼭짓점이 1개에서 7개인 모든 단순 그래프의 비동형류
대표를 하나씩 포함한다. 이 가운데 정확히 145개에서
\(\mathcal C_3(G)\)와 \(\mathcal C_4(G)\)가 모두 연결되어 있다. 정확한 반지름
계산 결과
\(\operatorname{rad}\mathcal C_3(G)<\operatorname{rad}\mathcal C_4(G)\)인
그래프는 없었다.

| 꼭짓점 수 \(n\) | Atlas 그래프 수 | 두 재색칠 그래프가 모두 연결 | 반례 수 |
|---:|---:|---:|---:|
| 1 | 1 | 1 | 0 |
| 2 | 2 | 2 | 0 |
| 3 | 4 | 3 | 0 |
| 4 | 11 | 7 | 0 |
| 5 | 34 | 13 | 0 |
| 6 | 156 | 34 | 0 |
| 7 | 1,044 | 85 | 0 |
| **합계** | **1,252** | **145** | **0** |

이 결과는 꼭짓점이 8개 이상인 그래프나 \(k>3\)인 \(k\to k+1\) 비교에
대해 질문 15를 해결하지 않는다. 새로움도 주장하지 않는다.

## 검증 구조

`atlas_1_7.g6`은 NetworkX 3.6.1의 `graph_atlas_g()`에서 꼭짓점이 0개인
그래프만 제외하여 생성했다. 서로 다른 레코드 1,252개의 SHA-256은
`ad68465d32eb7679a1ed8b0aa7a7f1da366da9b1ef8566b04664c504e8876255`이다.
두 반지름 계산을 시작하기 전에 위 차수별 개수를 검사한다.

두 구현이 결과를 검증한다.

1. `recolor_radius_exact.cpp`는 graph6을 해독하고 레이블된 모든 올바른
   색칠을 열거하여 각 재색칠 그래프를 구성한 뒤 정수 BFS로 정확한 반지름을
   구한다. 색 이름을 전역적으로 치환해도 이심률이 보존되므로 색 치환 궤도마다
   제한 성장 형태의 시작점 하나만 조사하면 충분하다.
2. `verify_atlas.py`는 별도의 graph6 해독기와 튜플 상태 BFS를 사용한다.
   비연결 그래프 \(G\)에 대해서는 정확한 항등식
   \(\mathcal C_k(G_1\mathbin{\dot\cup}G_2)=
   \mathcal C_k(G_1)\mathbin{\square}\mathcal C_k(G_2)\)를 사용하므로,
   연결성은 성분별로 결정되고 반지름은 더해진다. 꼭짓점이 6개 이하인 모든
   그래프의 \(\mathcal C_3(G)\)에 대해, 그리고 \(\mathcal C_3(G)\)가 연결된
   그래프의 \(\mathcal C_4(G)\)에 대해 이 환원을 사용하지 않은 직접 곱
   BFS와도 교차 검증한다.

두 구현에서 사용하는 환원의 정당화는 [DETAILS.ko.md](DETAILS.ko.md)에
정리되어 있다.

신뢰 경계는 표준 Graph Atlas 열거와 일반 컴파일러 및 Python 실행 환경이다.
`generate_atlas_data.py`는 NetworkX 버전, 차수별 개수, 레코드 유일성,
예상 데이터셋 해시를 고정한다. CI 검증기 자체는 NetworkX에 의존하지 않는다.

## 재현

저장소 루트에서 다음을 실행한다.

```bash
g++ -O3 -std=c++17 \
  problems/recoloring-radius-q15/recolor_radius_exact.cpp \
  -o /tmp/recolor_radius_exact
python3 problems/recoloring-radius-q15/verify_atlas.py \
  --cpp /tmp/recolor_radius_exact
```

예상 출력의 마지막 부분은 다음과 같다.

```text
PASS dataset: 1252 unique records, SHA-256 ad68465d32eb7679a1ed8b0aa7a7f1da366da9b1ef8566b04664c504e8876255
PASS C++ exhaustive audit: 1252 graphs, 145 eligible pairs, 0 counterexamples
PASS independent Python audit: 1252 graphs through order 7, 145 eligible pairs, 0 counterexamples (...s)
```

기록된 로컬 실행에서 C++ 검증은 1.12초, 독립 Python 검증은 53.53초가
걸렸다. 전체 검증 시간은 56.76초였고 최대 상주 메모리는 약 22 MB였다.

고정 입력을 독립적으로 다시 생성하려면 다음을 실행한다.

```bash
python3 -m venv /tmp/recolor-atlas-venv
/tmp/recolor-atlas-venv/bin/pip install 'networkx==3.6.1'
/tmp/recolor-atlas-venv/bin/python \
  problems/recoloring-radius-q15/generate_atlas_data.py \
  /tmp/atlas_1_7.g6
cmp /tmp/atlas_1_7.g6 problems/recoloring-radius-q15/atlas_1_7.g6
```

## 원문 충실성과 규약

계산은 유한 무향 단순 그래프, 팔레트 \(\{0,\ldots,k-1\}\)를 쓰는 레이블된
올바른 색칠, 한 꼭짓점씩 바꾸는 재색칠 이동, 보통의 그래프 거리, 최소
이심률로 정의한 반지름을 사용한다. 이는 출판된 정의와 일치하며 색 이름을
0부터 쓰는 것과 1부터 쓰는 것에는 의미상 차이가 없다. 재색칠 그래프의
연결성과 반지름은 그래프 동형 아래 불변이므로 각 비동형 그래프의 대표 하나만
검사해도 된다. 꼭짓점이 0개인 그래프는 주장한 탐색 범위에 포함하지 않는다.

`recolor_radius_search.py`는 탐색용 NetworkX 구현으로 남겨 둔다. 위 인증서
명령은 고정 데이터, C++ 탐색기, 표준 라이브러리만 사용하는 독립 Python
검증기만 이용한다.
