[English](README.md) | **한국어**

# WOWII 그래프 추측 189

## 명제

E. DeLaViña가 정리한 Graffiti.pc 프로그램의 추측 목록 *Written on the Wall II*의 추측 189이다.
Formal Conjectures 스냅샷에 실린 원문을 그대로 옮긴다.

> If G is a simple connected graph with n > 1 such that maximum { dist_even(v) : dist_even(v) is
> the number of vertices at even distance from v } ≤ 1 + σ(G), then G has a Hamiltonian path.

출처: [Written on the Wall II](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/).
Formal Conjectures는 `http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj189`를
인용하고 상태를 O(미해결)로 기록한다. 거리 0도 짝수이므로 dist_even(v)는 v 자신도 센다.
σ(G)는 차수를 오름차순으로 나열한 수열의 두 번째 항이다.

아래에서 (H)는 다음 가설을 뜻한다: G는 연결 그래프이고, n > 1이며,
max_v dist_even(v) ≤ 1 + σ(G)이다. *추적 가능*(traceable)하다는 것은 해밀턴 경로가 있다는
뜻이다. N₂(v)는 v로부터의 거리가 정확히 2인 정점들의 집합이다.

## 결과

**상태: 부분 결과.** 추측은 해결되지 않았다. Lean 4로 다음을 증명했다. `sorry`, 추가 공리,
`native_decide`는 쓰지 않았다.

1. diam(G) ≤ 2이면 추측이 성립한다. Easwar–Johari 정리 B의 조건 (1)을 재현한 것이다.
2. (H) 아래에서 모든 정점 v에 대해 |N₂(v)| ≤ σ이다.
3. (H) 아래에서 모든 정점 x에 대해 n ≤ dist_even(x) + deg(x) + (dist_even(x) − 1)·σ이다.
   따라서 모든 정점의 차수는 n − σ² − σ − 1 이상이고, n ≤ (σ + 1)²이다.
4. (H) 아래에서 모든 정점 x에 대해 4n ≤ 4(σ + 1) + 4·deg(x) + (σ + 1)²이다. 따라서
   n ≤ 2σ + 1 + ⌊(σ + 1)²/4⌋이고, 이 값은 σ = 3이면 11, σ = 4이면 15이다. σ ≤ 4이면 모든
   정점의 차수는 n − 11 이상이다.

세 가지 전수 컴퓨터 탐색에서 반례가 나오지 않았다.

5. 정점이 11개 이하인 모든 연결 그래프. n = 11에서 1,006,700,565개이고, 그중 27,429,222개가
   (H)를 만족한다.
6. σ(G) ≤ 3인 모든 그래프. 3번 결과에 따르면 (H)를 만족하고 σ(G) ≤ 3인 그래프는 정점이
   16개 이하이므로, n ≤ 16에서 가지치기 탐색을 하면 빠짐없이 다룰 수 있다. 동형을 무시하면
   이런 그래프는 정확히 654개다. 모두 정점이 10개 이하이고, 모두 추적 가능하다.
7. σ(G) = 4인 모든 그래프. 4번 결과에 따르면 (H)를 만족하고 σ(G) = 4인 그래프는 정점이
   15개 이하이므로, n ≤ 15에서 가지치기 탐색을 하면 빠짐없이 다룰 수 있다. 동형을 무시하면
   이런 그래프는 정확히 61,054개다. 모두 정점이 13개 이하이고, 모두 추적 가능하다.

따라서 **정점이 11개 이하인 모든 그래프와 σ(G) ≤ 4인 모든 그래프에서 추측 189가 성립한다**.
5–7번은 컴퓨터 보조 결과로, nauty의 `geng`과 탐색 프로그램이 올바르다는 가정에 기댄다.
모든 그래프는 서로 독립적으로 작성한 C 프로그램 두 개가 검사한다. 6번의 그래프 654개와 7번의
그래프 61,054개에 대해서는 표준 라이브러리만 쓰는 Python 스크립트가 해밀턴 경로를 하나씩 다시
확인한다.

### Lean 정리

모듈: `AgenticConjectures.WowiiGraphConjecture189`
([소스](../../AgenticConjectures/WowiiGraphConjecture189.lean)).

| 정리 | 내용 |
| --- | --- |
| `statement` | 상류의 `conjecture189`를 `Prop`으로 옮긴 것; 증명되지 않음 |
| `exists_isHamiltonian_of_ore` | 서로 다르고 인접하지 않은 모든 u, v에 대해 deg u + deg v ≥ n − 1이면 G는 추적 가능하다 (Ore) |
| `secondSmallestDegree_le_max` | u ≠ v이면 σ ≤ max(deg u, deg v) |
| `distEven_eq_card_sub_degree` | diam ≤ 2이면 dist_even(v) = n − deg v |
| `conjecture189_of_diam_le_two` | (H)와 diam ≤ 2이면 추적 가능 |
| `card_dist_eq_two_le` | (H)이면 \|N₂(v)\| ≤ σ |
| `card_le_distEven_add_degree` | (H)이면 n ≤ dist_even(x) + deg x + (dist_even(x) − 1)σ |
| `card_le_degree_add` | (H)이면 n ≤ deg x + σ² + σ + 1 |
| `card_le_sq` | (H)이면 n ≤ (σ + 1)² |
| `search_reduction` | (H)와 σ ≤ 3이면 n ≤ 16, 최소 차수 ≥ n − 13, \|N₂(v)\| ≤ 3, 차수가 3 이하인 정점이 둘 이상 |
| `exists_card_add_mul_self_le` | (H)이면 모든 x에 대해 n + s² ≤ dist_even(x) + deg x + s(σ + 1)인 s가 있다 |
| `four_mul_card_le` | (H)이면 4n ≤ 4(σ + 1) + 4 deg x + (σ + 1)² |
| `four_mul_card_le_sq` | (H)이면 4n ≤ 4(2σ + 1) + (σ + 1)² |
| `search_reduction_four` | (H)와 σ ≤ 4이면 n ≤ 15, 최소 차수 ≥ n − 11, \|N₂(v)\| ≤ 4, 차수가 4 이하인 정점이 둘 이상 |
| `exists_degree_eq_secondSmallestDegree`, `two_le_card_degree_le` | 차수가 σ인 정점이 있고, 차수가 σ 이하인 정점이 둘 이상 있다 |

## 방법

### 지름이 2 이하인 경우

diam(G) ≤ 2이면 v로부터 짝수 거리에 있는 정점은 v 자신과 v의 비이웃뿐이다. 따라서
dist_even(v) = n − deg(v)이고, (H)는 모든 v에 대해 deg(v) ≥ n − 1 − σ라는 뜻이 된다.
σ가 두 번째로 작은 차수이므로 서로 다른 두 정점은 σ ≤ max(deg u, deg v)를 만족한다. 그러므로
deg u + deg v ≥ n − 1이고, 이것이 해밀턴 경로에 대한 Ore 조건이다. Ore 조건의 Lean 증명은
외부 결과에 기대지 않는다. 가장 긴 경로를 잡고, 통상적인 회전으로 사이클을 만든 뒤 그 사이클을
늘린다.

### 위수 상한

정점 x를 고정하고, x로부터 짝수 거리에 있는 정점들의 집합을 D라 하자. 그러면
|D| = dist_even(x)이다.

- x로부터 홀수 거리 3 이상에 있는 정점 w에는 x에 한 걸음 더 가까운 이웃 y가 있다. 이 y는
  D \ {x}에 속한다.
- w는 y의 이웃 가운데 x에 한 걸음 더 가까운 고정된 정점 q(y)로부터 거리가 정확히 2이다.
  경로 q(y)–y–w가 거리 2 이하를 주고, x로부터의 거리를 비교하면 2 이상이다.
- (H) 아래에서 모든 p에 대해 |N₂(p)| ≤ dist_even(p) − 1 ≤ σ이다.

따라서 홀수 거리 3 이상인 정점은 많아야 (|D| − 1)·σ개이고,
n ≤ |D| + deg(x) + (|D| − 1)·σ이다. |D| ≤ σ + 1이므로 차수가 σ인 x를 고르면
n ≤ (σ + 1)²을 얻는다. 임의의 x에 대해서는 deg(x) ≥ n − σ² − σ − 1을 얻는다.

### 더 날카로운 위수 상한

x로부터 홀수 거리 3 이상에 있는 정점들의 집합을 O(x)라 하면
n = dist_even(x) + deg(x) + |O(x)|이다. 각 z ∈ O(x)에는 x에 한 걸음 더 가까운 이웃 q(z)가
있다. x의 이웃으로 이루어진 집합 가운데, 모든 z ∈ O(x)에 대해 x에서 q(z)로 가는 최단 경로
위의 정점을 하나씩 포함하는 가장 작은 집합을 Y라 하고 s = |Y|라 하자. 그러면 다음이 성립한다.

- 모든 z ∈ O(x)는 어떤 y ∈ Y로부터 짝수 거리에 있다.
- Y가 최소이므로, 모든 y ∈ Y는 자기 자신 말고도 O(x) 밖의 정점 s − 1개를 짝수 거리에 둔다.

따라서 (H) 아래에서 각 y ∈ Y로부터 짝수 거리에 있는 O(x)의 정점은 많아야 σ + 1 − s개이고,
|O(x)| ≤ s·(σ + 1 − s) ≤ (σ + 1)²/4이다. 그러므로 4n ≤ 4(σ + 1) + 4·deg(x) + (σ + 1)²이고,
차수가 σ인 정점을 고르면 n ≤ 2σ + 1 + ⌊(σ + 1)²/4⌋을 얻는다. 전체 증명은
[`DETAILS.ko.md`](DETAILS.ko.md)에 있다.

### n ≤ 11 전수 탐색

nauty 2.9.3의 `geng -c n`은 모든 연결 그래프를 동형을 무시하고 한 번씩 생성한다. 그 출력을
두 검사기에 통과시킨다.

- [`hyp189.c`](hyp189.c)는 비트셋 BFS로 dist_even을 계산한 뒤 σ와 (H)를 계산한다. (H)를
  만족하는 그래프마다 노드 예산을 둔 깊이 우선 탐색으로 추적 가능성을 판정하고, 예산을 넘기면
  정확한 부분집합 동적 계획법으로 넘어간다.
- [`ind189.c`](ind189.c)는 이와 독립적으로 작성했다. 인접 리스트 BFS와 백트래킹을 쓰며,
  순수 부분집합 DP 옵션 `-dp`가 있다.

n ≤ 11에서 두 프로그램은 (H) 그래프의 개수와 σ별 분포가 일치한다. 어느 프로그램도
해밀턴 경로가 없는 (H) 그래프를 찾지 못했다.

| n | 연결 그래프 | (H) 그래프 | σ별 (H) 그래프 (σ: 개수) | Easwar–Johari 이후 남는 경우 |
| --- | ---: | ---: | --- | ---: |
| 2 | 1 | 1 | 1:1 | 0 |
| 3 | 2 | 2 | 1:1 2:1 | 0 |
| 4 | 6 | 5 | 1:1 2:3 3:1 | 0 |
| 5 | 21 | 15 | 2:9 3:5 4:1 | 0 |
| 6 | 112 | 51 | 2:15 3:27 4:8 5:1 | 0 |
| 7 | 853 | 247 | 2:5 3:163 4:67 5:11 6:1 | 0 |
| 8 | 11,117 | 1,476 | 3:293 4:1018 5:149 6:15 7:1 | 0 |
| 9 | 261,080 | 22,575 | 3:100 4:17012 5:5132 6:311 7:19 8:1 | 0 |
| 10 | 11,716,571 | 418,415 | 3:29 4:33433 5:360065 6:24249 7:614 8:24 9:1 | 24 |
| 11 | 1,006,700,565 | 27,429,222 | 4:7186 5:21987577 6:5321065 7:112195 8:1169 9:29 10:1 | 0 |

마지막 열은 Easwar–Johari의 정리 B가 다루지 못하는 (H) 그래프의 수다. 2-연결이고, 지름이 3
이상이며, n ≥ 2σ + 4인 그래프다. n = 10의 24개는 모두 σ = 3이다.

n = 11에서는 `geng`의 res/mod 옵션으로 출력을 여덟 부분으로 나누었고, 두 검사 프로그램이
모든 부분을 읽었다. 모든 실행의 요약 출력 원문은 [`search_summary.txt`](search_summary.txt)에
있다.

### σ(G) ≤ 3 전수 탐색

[`prune189.c`](prune189.c)는 `geng`의 `PRUNE` 훅으로, SMAX=3으로 실행한다. 중간 단계든 최종
단계든, 다음 두 경우 중 하나에 해당하는 그래프를 버린다.

- 어떤 정점으로부터 거리가 2인 정점이 셋보다 많다.
- 차수가 3 이하인 정점의 수가 2 − (n_final − n_current)보다 적다.

`geng`은 각 그래프에 유도 부분그래프의 사슬을 따라 도달한다. 유도 부분그래프에서 거리가 2라는
것은 인접하지 않고 공통 이웃이 있다는 뜻이므로, 전체 그래프에서도 거리가 2이다. 사슬을 따라
차수는 늘어나기만 한다. 따라서 `search_reduction`에 의해 σ ≤ 3인 (H) 그래프는 모두 가지치기를
통과한다. n = 15와 n = 16에서는 `search_reduction`이 최소 차수가 n − 13 이상임도 보장하므로,
`geng -c -d2`와 `geng -c -d3`로 탐색한다.

경험적 확인으로, n ≤ 11인 모든 n에서 가지치기 탐색은 가지치기 없는 탐색이 찾은 σ ≤ 3인 (H)
그래프를 같은 graph6 문자열로 정확히 다시 얻는다. 개수는 1, 2, 5, 14, 42, 168, 293, 100, 29,
0이다.

| n | `geng` 옵션 | 가지치기 후 그래프 | (H) 그래프 (모두 σ ≤ 3) | CPU 시간 |
| --- | --- | ---: | ---: | ---: |
| 2–9 | `-c` | 1, 2, 6, 20, 93, 396, 939, 785 | 1, 2, 5, 14, 42, 168, 293, 100 | 각 0.1초 미만 |
| 10 | `-c` | 669 | 29 | 0.1초 |
| 11 | `-c` | 796 | 0 | 0.7초 |
| 12 | `-c` | 1,513 | 0 | 4.8초 |
| 13 | `-c` | 3,167 | 0 | 47초 |
| 14 | `-c` | 7,100 | 0 | 8.7분 |
| 15 | `-c -d2` | 2,125 | 0 | 76분 |
| 16 | `-c -d3` | 5 | 0 | 7.7시간 |

찾은 (H) 그래프는 모두 추적 가능하다. 가지치기를 통과한 그래프에 대해 `hyp189`, `ind189`,
[`certify.py`](certify.py)의 판정이 모두 일치한다.
[`sigma3_certificates.txt`](sigma3_certificates.txt)에는 그래프 654개가 graph6 형식으로,
각각의 해밀턴 경로와 함께 실려 있다. `certify.py`는 Python 표준 라이브러리만 쓰는, dist_even과
σ의 세 번째 구현이다. 연결성, (H), σ ≤ 3, 각 경로, 그리고 위수별 개수를 다시 확인한다.

### σ(G) = 4 전수 탐색

같은 논법으로, SMAX=4로 실행한 훅은 σ ≤ 4인 (H) 그래프를 모두 남긴다. 이번에는
`search_reduction_four`에 기댄다. 이 정리는 n ≤ 15이고 최소 차수가 n − 11 이상임도 보장하므로,
n ≤ 14에서는 `geng -c`, n = 15에서는 `geng -c -d4`로 탐색한다.

| n | `geng` 옵션 | 가지치기 후 그래프 | σ ≤ 4인 (H) 그래프 | 그중 σ = 4 | 시간 |
| --- | --- | ---: | ---: | ---: | ---: |
| 2–9 | `-c` | 1, 2, 6, 21, 111, 808, 7,623, 54,274 | 1, 2, 5, 15, 50, 235, 1,311, 17,112 | 0, 0, 0, 1, 8, 67, 1,018, 17,012 | 각 0.1초 미만 |
| 10 | `-c` | 133,566 | 33,462 | 33,433 | 0.7초 |
| 11 | `-c` | 136,772 | 7,186 | 7,186 | 6.1초 |
| 12 | `-c` | 166,081 | 2,044 | 2,044 | 53초 |
| 13 | `-c` | 341,208 | 285 | 285 | 8.6분 |
| 14 | `-c` | 1,001,800 | 0 | 0 | 4코어로 23분 |
| 15 | `-c -d4` | 23 | 0 | 0 | 4코어로 25분 |

n = 13까지는 CPU 시간이다. n = 14와 15는 res/mod 조각 128개를 네 개씩 동시에 실행한 실제 경과
시간이다. n ≤ 11에서 가지치기 탐색은 가지치기 없는 탐색이 찾은 σ = 4인 (H) 그래프를 정확히 다시
얻고, n ≤ 10에서는 가지치기 없는 `geng`이 같은 graph6 문자열을 낸다. 찾은 (H) 그래프는 모두
추적 가능하다. 가지치기를 통과한 그래프에 대해 `hyp189`, `ind189`, `certify.py --sigma4`의
판정이 모두 일치한다. [`sigma4_certificates.txt`](sigma4_certificates.txt)에는 σ = 4인 그래프
61,054개가 graph6 형식으로, 각각의 해밀턴 경로와 함께 실려 있다. 이 탐색이 찾은 σ ≤ 3인 (H)
그래프는 `sigma3_certificates.txt`의 그래프와 같다.

σ = 4인 그래프 가운데 2,243개(n = 12에서 1,973개, n = 13에서 270개)는 2-연결이고, 지름이 3
이상이며, n ≥ 2σ + 4이므로 Easwar–Johari의 정리 B가 다루지 않는다.
[`DETAILS.ko.md`](DETAILS.ko.md)에는 σ = 4인 그래프가 극단적인 경우에 대해 보여 주는 것과,
같은 탐색이 σ = 5에서는 감당할 수 없는 이유를 적었다.

## 재현

```bash
python3 certify.py sigma3_certificates.txt
python3 certify.py --sigma4 sigma4_certificates.txt
```

CI가 실행하는 검사이며, 각각 1초 미만과 약 2초가 걸린다. 전수 탐색을 재현하려면 C 컴파일러와,
압축을 풀고 `./configure`까지 마친 nauty 2.9.3 소스가 필요하다.

```bash
bash reproduce.sh /path/to/nauty2_9_3
```

`reproduce.sh`는 `hyp189`, `ind189`, 그리고 훅을 넣은 `geng`인 `geng189`를 빌드한다. 이어서
n ≤ `FULL_MAX`(기본값 10; `FULL_MAX=11`이면 위 표를 재현)에서 가지치기 없는 탐색을 하고,
n ≤ 16에서 σ ≤ 3 탐색을, n ≤ 15에서 σ ≤ 4 탐색을 한다. 또 n ≤ 10에서 가지치기 없는 `geng`이
가지치기 탐색과 같은 σ ≤ 3인 (H) 그래프와 σ = 4인 (H) 그래프를 내는지 확인하고, 다시 만든
인증서가 커밋된 인증서와 같은 그래프를 담는지도 확인한다. 불일치나 반례가 나오면 멈춘다.
`SIGMA_MAX`와 `SIGMA4_MAX`로 두 가지치기 탐색의 최대 위수를 낮출 수 있고,
`FULL_MAX=2 SIGMA_MAX=2`로 실행하면 사실상 σ ≤ 4 탐색만 한다. Apple silicon 기기에서 걸리는
시간은 다음과 같다.

- 가지치기 없는 탐색은 `geng`의 출력을 하나의 파이프라인으로 두 검사 프로그램에 보낸다.
  n ≤ 10에 약 5초, n = 11에 약 7분 걸린다(실제 경과 시간).
- σ ≤ 3 탐색은 CPU 시간으로 n ≤ 13에 1분 미만, n = 14에 9분, n = 15에 76분, n = 16에
  7.7시간 걸린다.
- σ ≤ 4 탐색은 CPU 시간으로 n ≤ 13에 약 10분 걸린다. `JOBS=4`이면 n = 14와 n = 15에 각각
  약 25분(실제 경과 시간)이 걸린다. 검사까지 포함한 σ ≤ 4 부분 전체는 실제 경과 시간 53분,
  CPU 시간 3.3시간이 걸렸다.

`reproduce.sh`는 큰 위수(σ ≤ 3은 n ≥ 14, σ ≤ 4는 n ≥ 13)를 `geng`의 res/mod 옵션으로
조각으로 나누고, 그중 `JOBS`개(기본값 4)를 병렬로 실행한다.

## 명제의 충실성

- `AgenticConjectures.WowiiGraphConjecture189.statement`는 상류 `conjecture189`의 전칭
  폐포다([스냅샷](upstream/README.md)). `distEven`, `degreeSequence`, `secondSmallestDegree`는
  항 단위로 그대로 옮겼다.
- dist_even(v)는 상류와 Easwar–Johari처럼 v 자신을 센다. v를 빼고 세는 해석은 거짓이다. 발톱
  그래프 K₁,₃에서 각 잎은 짝수 거리에 다른 정점 둘을 두고 중심은 하나도 두지 않으므로 최댓값은
  2 = 1 + σ인데, 발톱 그래프에는 해밀턴 경로가 없다.
- σ(G)는 정렬된 차수 수열의 두 번째 항이며, 중복도를 센다. 따라서 최소 차수를 갖는 정점이 둘
  이상이면 σ는 최소 차수와 같다. 이는 상류의 `secondSmallestDegree` 및 Easwar–Johari의 d₂와
  일치한다.
- C와 Python 프로그램은 graph6 입력에 대해 같은 정의를 정확한 정수 연산으로 구현한다. 5–7번의
  탐색 부분은 Lean으로 형식화하지 않았다. Lean은 환원 부분(1–4번, `search_reduction`,
  `search_reduction_four`)만 보증한다.
- **툴체인.** 이 저장소는 Lean과 mathlib `v4.30.0`으로 빌드하고, Formal Conjectures `c094b97`은
  `v4.33.1`(mathlib `0df444a`)을 고정한다. 명제가 쓰는 mathlib 선언(`Connected`, `dist`,
  `edist`, `degree`, `neighborFinset`, `Walk.support`, `Walk.IsHamiltonian`, `Multiset.sort`)은
  두 버전에서 글자 그대로 같다. `SimpleGraph`에서는 증명 필드 `symm`의 타입만 바뀌었고
  (`Symmetric Adj` 대신 `Std.Symm Adj`), `Adj`는 그대로다. 이 모듈을 `v4.33.1`에서 컴파일해
  보지는 않았다.

## 선행 연구와 범위

- R. Easwar, S. Johari, *Conditions for traceability under a bound on the size of even-distance
  sets*, [arXiv:2609.11719](https://arxiv.org/abs/2609.11719) (2026). 정리 B는 (H)를 만족하는
  G가 다음 각 경우에 추적 가능함을 보인다.
  - diam ≤ 2;
  - n ≤ 2σ + 2;
  - n = 2σ + 3이고 G가 2-연결;
  - G가 2-연결이 아님.

  위의 1번은 같은 Ore 논법으로 첫 번째 경우를 재현한다. 이 논문에는 계산 결과가 없다.
- O. Ore, *Note on Hamilton circuits*, Amer. Math. Monthly 67 (1960), 55. Easwar–Johari가 쓰는
  것은 이 결과의 경로 판본이다.
- 위수 상한 n ≤ (σ + 1)²와 n ≤ 2σ + 1 + ⌊(σ + 1)²/4⌋, σ ≤ 3 환원과 σ ≤ 4 환원, 그리고 탐색
  결과는 확인한 자료에서 찾지 못했다. 이는 새로움을 주장하는 것이 아니다.

이 결과는 사람이 검토하지 않았다. AI 모델이 만들었고, Lean 커널, 서로 독립인 두 검사 프로그램,
인증서 스크립트로만 확인했다. Formal Conjectures, WOWII 관리자, 그 밖의 어디에도 제출하지
않았으며, 외부 제출에는 사람의 승인이 필요하다.

## 파일

- [`DETAILS.ko.md`](DETAILS.ko.md): 더 날카로운 위수 상한의 증명, σ = 4인 그래프가 보여 주는
  것, σ = 5 벤치마크, 효과가 없었던 접근.
- [`certify.py`](certify.py), [`sigma3_certificates.txt`](sigma3_certificates.txt),
  [`sigma4_certificates.txt`](sigma4_certificates.txt): σ ≤ 3과 σ = 4 경우의 해밀턴 경로 인증서.
- [`hyp189.c`](hyp189.c), [`ind189.c`](ind189.c), [`prune189.c`](prune189.c): 탐색 프로그램.
- [`reproduce.sh`](reproduce.sh): 탐색을 빌드하고 실행한다.
- [`search_summary.txt`](search_summary.txt): 실행에서 나온 위수별 요약 줄 원본.
- [`upstream/`](upstream/README.md): Formal Conjectures 스냅샷.
