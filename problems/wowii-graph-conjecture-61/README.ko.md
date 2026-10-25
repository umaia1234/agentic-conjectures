[English](README.md) | **한국어**

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

상세 증명은 [PROOF.ko.md](PROOF.ko.md)에 있다. 이 결과들은 일반 그래프의
나머지 지름을 닫지 않으므로 원 추측 전체의 해결이 아니다. 결과 2의
부등식 \(f(G)\ge\alpha(G)+1\)은 Lean으로도 증명했고, 전수 컴퓨터
검증으로 여러 유한 그래프족에서 원 추측의 반례가 없음을 확인했다. 둘 다
아래에서 설명한다.

## 전수 컴퓨터 검증 (2026-10-24)

### 검증한 명제

아래 네 유한 그래프족에 속하는 모든 그래프 \(G\)에서 추측된 부등식
\(f(G)\ge r(G)+\lceil D(G)/3\rceil\)이 성립한다. 즉 이 그래프족들에는
반례가 없다. 각 값은 upstream Lean 정의를 그대로 따른다. \(r(G)\)는
`SimpleGraph.residue`, 곧 Havel--Hakimi residue다(반지름이 아니다).
차수열을 내림차순으로 정렬한 뒤, 첫 항 \(d\)를 떼어 내고 `List.splitAt`과
자연수 뺄셈(0에서 멈추는 뺄셈)으로 다음 \(d\)개 항을 1씩 줄여 다시
정렬하는 일을 반복한다. 마지막에 남은 0의 개수가 \(r(G)\)다. \(f(G)\)는
`largestInducedForestSize`, \(D(G)\)는 `SimpleGraph.diam`이다.

| 그래프족 | 열거 방법 | 그래프 수 | 최소 여유 |
|---|---|---|---|
| \(n\le11\)인 모든 연결 그래프 | `geng -c n` | 1018690329 | 0 |
| \(n\le26\)인 모든 트리 | `gentreeg n` | 447672596 | 0 |
| 순환 차수(cyclomatic number) \(m-n+1\le c\)인 연결 그래프: \(12\le n\le15\)이면 \(c=4\), \(n=16,17\)이면 \(c=3\), \(18\le n\le20\)이면 \(c=2\) | `geng -c n n-1:n-1+c` | 626942607 | 0 |
| \(12\le n\le18\)이고 \(D\ge n-5\)인 연결 그래프 | `diampath_gen n D \| shortg` | 2046546 | 1 |

\(n\)은 정점 수, \(m\)은 변의 수다. 여유(slack)를
\(s(G)=f(G)-r(G)-\lceil D(G)/3\rceil\)로 쓰자. 앞의 세 그래프족에서는
모든 차수 \(n\)에서 최소 여유가 \(0\)이다. 별 그래프
\(K_{1,n-1}\)(\(f=n\), \(r=n-1\), \(D=2\))이 이 값을 가지며,
\(n\le11\)인 연결 그래프 중에서는 \(K_n\)도 마찬가지다. 따라서
부등식은 모든 차수에서 등호에 닿는다. 이것은 유한 범위의 탐색일 뿐
추측의 증명은 아니다.

### 정점 11개 이하의 모든 연결 그래프

| n | 그래프 수 | 트리 수 | 최소 여유 | 최소 여유인 그래프 수 | 최대 D | 위반 | 교차 검증 |
|---|---|---|---|---|---|---|---|
| 1 | 1 | 1 | 0 | 1 | 0 | 0 | 불일치 0 |
| 2 | 1 | 1 | 0 | 1 | 1 | 0 | 불일치 0 |
| 3 | 2 | 1 | 0 | 2 | 2 | 0 | 불일치 0 |
| 4 | 6 | 2 | 0 | 5 | 3 | 0 | 불일치 0 |
| 5 | 21 | 3 | 0 | 11 | 4 | 0 | 불일치 0 |
| 6 | 112 | 6 | 0 | 32 | 5 | 0 | 불일치 0 |
| 7 | 853 | 11 | 0 | 100 | 6 | 0 | 불일치 0 |
| 8 | 11117 | 23 | 0 | 338 | 7 | 0 | 불일치 0 |
| 9 | 261080 | 47 | 0 | 1231 | 8 | 0 | 불일치 0 |
| 10 | 11716571 | 106 | 0 | 5124 | 9 | 0 | 불일치 0 |
| 11 | 1006700565 | 235 | 0 | 26094 | 10 | 0 | 표본: 불일치 0 |

"위반"은 추측이나 아래에 나열한 PROOF.ko.md의 부등식을 어기는 그래프의
수에 검사기 내부 이상 징후의 수를 더한 값이다. "교차 검증"은 \(f\),
\(\alpha\), \(D\), \(r\)의 빠른 계산과 전수(brute-force) 계산이 어긋난
횟수다. \(n=11\)에서는 전수 계산을 모든 그래프가 아니라 해시 표본
246176개에서만 돌렸다.

\(n\le 11\)인 모든 연결 그래프를 지름별로 모으면 다음과 같다.

| D | 그래프 수 | 최소 여유 | 최소 여유인 그래프 수 | 최소 f-alpha | ceil(D/4) | ceil(D/3) | f-alpha < ceil(D/3)인 그래프 수 | 그중 최소 여유 |
|---|---|---|---|---|---|---|---|---|
| 0 | 1 | 0 | 1 | 0 | 0 | 0 | 0 | - |
| 1 | 10 | 0 | 10 | 1 | 1 | 1 | 0 | - |
| 2 | 373528268 | 0 | 9215 | 1 | 1 | 1 | 0 | - |
| 3 | 611259790 | 0 | 12523 | 1 | 1 | 1 | 0 | - |
| 4 | 32578716 | 0 | 11190 | 1 | 1 | 2 | 185926 | 0 |
| 5 | 1252762 | 1 | 18066 | 2 | 2 | 2 | 0 | - |
| 6 | 65940 | 1 | 389 | 2 | 2 | 2 | 0 | - |
| 7 | 4496 | 1 | 649 | 2 | 2 | 3 | 51 | 1 |
| 8 | 327 | 2 | 161 | 2 | 2 | 3 | 1 | 2 |
| 9 | 18 | 3 | 18 | 4 | 3 | 3 | 0 | - |
| 10 | 1 | 3 | 1 | 5 | 3 | 4 | 0 | - |

"최소 f-alpha"는 \(f-\alpha\)의 최솟값이다. "f-alpha < ceil(D/3)인
그래프 수" 열은 더 강한 부등식 \(f(G)\ge\alpha(G)+\lceil D(G)/3\rceil\)이
깨지는 그래프의 수다. 이런 그래프에서 추측이 성립하는 것은
\(r(G)<\alpha(G)\)이기 때문이다.

### 남은 지름 4, 7, 8, 10 이상

PROOF.ko.md는 지름 \(\{0,1,2,3,5,6,9\}\)와 모든 트리를 해결한다. 남은
지름은 \(4\), \(7\), \(8\), \(D\ge10\)이다. 그래프족별 최소 여유는
다음과 같다.

| 그래프족 | 남은 지름 D | 그래프 수 | 최소 여유 | 최소 여유인 그래프 수 | f-alpha < ceil(D/3)인 그래프 수 | 최소 여유에서 사전순 첫 graph6 |
|---|---|---|---|---|---|---|
| 연결 그래프, \(n\le11\) | 4 | 32578716 | 0 | 11190 | 185926 | `E?zO` |
| 연결 그래프, \(n\le11\) | 7 | 4496 | 1 | 649 | 51 | `H?ABAqW` |
| 연결 그래프, \(n\le11\) | 8 | 327 | 2 | 161 | 1 | `` H?`D@`O `` |
| 연결 그래프, \(n\le11\) | >= 10 | 1 | 3 | 1 | 0 | `J?AAD?oEAO?` |
| 트리, \(n\le26\) | 4 | 8970 | 1 | 363 | 0 | `DkC` |
| 트리, \(n\le26\) | 7 | 10943967 | 2 | 7 | 0 | `GhE?GC` |
| 트리, \(n\le26\) | 8 | 36178575 | 2 | 1 | 0 | `HhE?GC@` |
| 트리, \(n\le26\) | >= 10 | 331250953 | 3 | 12 | 0 | `JhCK?C@?G?_` |
| 희소 그래프, \(12\le n\le20\) | 4 | 3878499 | 0 | 1358 | 1704 | `K???????F?Z}` |
| 희소 그래프, \(12\le n\le20\) | 7 | 155279595 | 1 | 69 | 5931 | `K???C@_SKYTW` |
| 희소 그래프, \(12\le n\le20\) | 8 | 147446044 | 2 | 4490 | 956 | `K????B_FEEBW` |
| 희소 그래프, \(12\le n\le20\) | >= 10 | 82006435 | 2 | 1391 | 2693 | `K???EA_E?kGo` |
| \(D\ge n-5\), \(12\le n\le18\) | 7 | 94741 | 1 | 2936 | 646 | `K????CKHIeRW` |
| \(D\ge n-5\), \(12\le n\le18\) | 8 | 141783 | 2 | 15477 | 188 | `` K?????FP`qV? `` |
| \(D\ge n-5\), \(12\le n\le18\) | >= 10 | 1614921 | 2 | 15160 | 1745 | `` K???OH@_`oE_ `` |

위 자료에서 읽을 수 있는 관찰은 다음과 같다.

- **지름 4.** 여유 \(0\)은 \(n=6\)부터 나타난다(정점 6개 그래프 네 개).
  그중 `E?zO`는 4-cycle의 마주 보는 두 꼭짓점에 펜던트 정점을 하나씩 단
  그래프로, \(f=5\), \(\alpha=4\), \(r=3\), \(D=4\)이다. 여기서
  \(D=4\)이면서 \(f=\alpha+1\)이므로 PROOF.ko.md (6)의 상한 \(D\le4\)는
  실제로 도달된다. 또 \(f<\alpha+\lceil D/3\rceil\)이어서, 이 그래프에서
  추측이 성립하는 것은 \(r<\alpha\)이기 때문일 뿐이다.
- **지름 7.** 최소 여유는 \(1\)이다. 예를 들어 `H?ABAqW`는 \(n=9\),
  \(f=8\), \(\alpha=5\), \(r=4\)다. 더 강한 부등식
  \(f\ge\alpha+\lceil D/3\rceil\)은 \(n=10\)부터 깨진다. 정점 10개
  그래프 세 개가 그렇고, 예를 들어 `I??E@osa_`는 \(f=\alpha+2=8\),
  \(r=\alpha-2=4\)다.
- **지름 8.** 최소 여유는 \(2\)이고 경로 \(P_9\)(`` H?`D@`O ``)가 이
  값을 가진다. 더 강한 부등식은 정점 11개 그래프 하나
  (`` J???F?[o`o? ``, \(f=9\), \(\alpha=7\), \(r=4\)), \(D\ge n-5\)
  그래프족의 그래프 188개, 희소 그래프족의 그래프 956개에서 깨진다.
- **지름 10 이상.** \(n\le11\)인 연결 그래프 중 \(D\ge10\)인 것은
  \(P_{11}\)뿐이고(여유 3), \(n\le26\)이고 \(D\ge10\)인 트리의 여유는
  3 이상이다. 희소 그래프족과 \(D\ge n-5\) 그래프족에서는 \(D=10\)에서
  여유 \(2\)가 나온다. 예를 들어 정점 12개의 단일 사이클 그래프
  `K???EA_E?kGo`는 \(f=11\), \(\alpha=7\), \(r=5\)다.
- **증명에 주는 함의.** \(D\in\{4,7,8,10,11,12,13,14\}\)인 모든 지름,
  곧 14 이하의 모든 남은 지름에서 위 그래프족에는
  \(f<\alpha+\lceil D/3\rceil\)인 그래프가 있다. 따라서 이 지름들에서는
  \(f-\alpha\)의 하한을 구한 뒤 \(r\le\alpha\)를 쓰는 방식의 논증으로
  추측을 증명할 수 없다. 증명에는 \(r\)에 대한 더 많은 정보가 필요하다.

### PROOF.ko.md의 점검

위 모든 그래프족의 모든 그래프는 \(r\le\alpha\)(부등식 (1)),
\(f\ge\alpha+\lceil D/4\rceil\)(정리 1), \(n\ge2\)일 때
\(f\ge\alpha+1\)(부등식 (5)), \(f=\alpha+1\Rightarrow D\le4\)(함의 (6))도
만족한다. 모든 트리는 \(f=n\)이고 추측을 만족한다(정리 4). 이
그래프족들에서 정리 1은 \(D\le14\)인 모든 지름마다 등호를 이루는 그래프가
있고, (6)은 \(D=4\)에서 도달된다.

### 구현과 교차 검증

1. [`wowii61.cpp`](wowii61.cpp)는 빠른 경로다. \(f\)는 정점 부분집합에
   대한 분기 한정법으로 구한다. 현재 숲을 연결 성분 비트마스크 목록으로
   들고 다니며, 사이클을 닫을 정점은 버리고, 들어올 수 있는 이웃이
   하나 이하인 정점은 분기 없이 넣는다. \(\alpha\)는 차수 \(\le1\)
   규칙을 쓴 분기로, \(D\)는 모든 정점에서의 비트마스크 BFS로 구한다.
   \(r\)은 `havelHakimiStep`/`residueAux`를 그대로 옮긴 코드다.
   프로그램은 `geng`/`gentreeg`의 출력을 읽거나, nauty 없이
   \(n\le8\)의 모든 표지 그래프를 직접 열거한다.
2. `wowii61 --crosscheck`는 같은 프로그램 안의 별도 전수 코드를
   돌린다. \(f\)와 \(\alpha\)는 모든 \(2^n\)개 정점 부분집합을 보고(비순환
   판정은 \(|E|=|V|-\)성분 수), \(D\)는 Floyd--Warshall, \(r\)은 개수
   배열 위의 Havel--Hakimi로 다시 계산한다. \(n\le10\)인 모든 연결
   그래프와 \(n=11\) 해시 표본에서 돌렸고 불일치는 0건이다.
3. [`wowii61_ref.py`](wowii61_ref.py)는 독립된 Python 구현이다. 자체
   graph6 파서, union-find를 쓰는 부분집합 탐색(\(f\)), 부분집합
   탐색(\(\alpha\)), BFS(\(D\)), Lean 정의를 한 줄씩 따라가는 리스트 기반
   residue를 쓴다. `--nx`를 주면 networkx로 파싱, 연결성, 지름,
   \(\alpha\)(여그래프의 최대 클릭), 숲 증인의 비순환성을 다시 계산한다.
   \(n\le9\)인 모든 연결 그래프에서 요약이 C++ 요약과 똑같다.
   \(n=10\)(1/64, 182471개)과 \(n=11\)(1/4096, 246176개)의 해시
   표본에서는 그래프마다 모든 값이 C++ 값과 일치하고, networkx도 모든
   곳에서 일치한다([`results/reference_check.log`](results/reference_check.log)).
4. 열거의 완전성은 nauty(`geng`, `gentreeg`, `shortg`)에 기댄다. 그래프
   수는 OEIS [A001349](https://oeis.org/A001349)(연결 그래프,
   \(n\le11\)), [A000055](https://oeis.org/A000055)(트리, \(n\le26\))와
   일치하고, CI에서 도는 표지 그래프 열거는
   [A001187](https://oeis.org/A001187)과 일치한다.
   [`diampath_gen.cpp`](diampath_gen.cpp)는 지름 \(D\ge n-5\)인 모든
   연결 그래프를 지름 경로를 따라(경로 밖 정점은 최대 네 개) 나열한다.
   이 생성기는 모든 \(n\le11\)과 \(D\ge\max(1,n-5)\)에서 `geng`의 개수를
   그대로 재현한다([`results/diampath_validation.log`](results/diampath_validation.log)).

### 재현

이 폴더에서, nauty 2.9.3과 C++17 컴파일러가 `PATH`에 있을 때 다음을
실행한다.

```bash
python3 verify_small.py                    # CI 검사: 실제 5초
bash run_exhaustive.sh OUT conn 3          # n <= 10: 실제 44초, CPU 69초
bash run_exhaustive.sh OUT conn11 3        # n = 11: 실제 875초, CPU 1616초
bash run_exhaustive.sh OUT trees 2         # 트리: 실제 1539초, CPU 1789초
bash run_exhaustive.sh OUT sparse 3        # 희소 그래프: 실제 2196초, CPU 4360초
bash run_exhaustive.sh OUT diampath 3      # D >= n-5: 실제 31초, CPU 52초
PYTHON=python3-with-networkx bash run_exhaustive.sh OUT ref 1
                                           # 참조 구현: 실제 1264초, CPU 648초
```

`diampath`와 `ref`는 `conn`과 `conn11`의 출력이 있어야 한다. 시간은
다른 작업과 함께 쓰는 Apple M5 Max(load average 60--95)에서 Apple
clang 21로 잰 값이다. `OUT`에 쓰이는 병합 요약(`connected_n1-10.txt`,
`connected_n11.txt`, `trees_n1-26.txt`, `sparse.txt`,
`diampath_n12-18.txt`)은 [`results/`](results/)의 파일과 같아야 한다.
nauty 버전이 다르면 그래프의 표지가 달라질 수 있는데, 이때 바뀌는 것은
`EX_` 예시 줄뿐이다. 요약마다 \(n\)별 개수, \((n,D,f-\alpha,\alpha-r)\)의 히스토그램, 위반과
불일치 카운터, 그리고 \((n,D)\)마다 최소 여유와 최소 \(f-\alpha\)를
이루는 사전순으로 가장 작은 graph6 문자열 다섯 개가 들어 있다.
[`wowii61_summary.py`](wowii61_summary.py)가 요약을 병합하고 위 표를
출력한다. \(n=10,11\)의 해시 표본은 커밋하지 않았다. `conn`과
`conn11`이 다시 만들며, SHA-256 값은 `results/reference_check.log`에
있다.

`verify_small.py`(CI)는 `wowii61.cpp`를 컴파일하고, \(n\le7\)인 모든
표지 그래프에서 전수 교차 검증을 켠 채 실행한다(연결 그래프 수는
A001187과 같아야 한다). 이어서 \(n\le6\)인 모든 표지 그래프에서 Python
참조 구현과 결과를 비교하고, 커밋된 요약을 점검한다. 점검 항목은 OEIS
개수, 히스토그램 합계, 0인 카운터, 히스토그램 위에서 다시 확인한
부등식들, 그리고 \(n\le7\)에서 표지 그래프 열거와 같은
\((D,f-\alpha,\alpha-r)\) 값 집합이다.

### 주장하지 않는 것

- 추측의 증명이 아니며, 나열한 그래프족 밖의 그래프에 대해서는 아무것도
  주장하지 않는다. "반례 없음"은 이 유한 그래프족에 대한 진술일 뿐이다.
- 새로움을 주장하지 않는다. Graffiti 추측을 작은 차수에서 점검하는 일은
  흔하며, 이 계산은 발표되지 않은 기존 점검을 되풀이한 것일 수 있다.
- 열거의 완전성은 nauty와 OEIS 개수에 기댄다. 희소 그래프족은 그 안의
  트리 수만 OEIS와 비교했고, 전체 개수는 독립된 출처와 비교하지 않았다.
  CI는 \(n\le7\)의 표지 그래프 부분만 다시 돌리고 커밋된 요약을 다시
  읽는다. 더 큰 계산은 로컬에서 했다.
- PROOF.ko.md의 비형식적 증명은 아래에서 형식화한 부등식 (5)를 빼면
  여전히 비형식적이다. \(r\le\alpha\)는 문헌에서 인용한 것이며 여기서는
  수치로만 확인했다.

## 부등식 (5)의 Lean 형식화

[`AgenticConjectures/WowiiGraphConjecture61.lean`](../../AgenticConjectures/WowiiGraphConjecture61.lean)은
PROOF.ko.md의 부등식 (5)(정리 2의 앞부분)를 `sorry`, 추가 공리,
`native_decide` 없이 증명한다.

| 선언 | 내용 |
|---|---|
| `largestInducedForestSize G` | `sSup {n \| ∃ s : Finset α, (G.induce s).IsAcyclic ∧ s.card = n}`, upstream 보조 정의와 같은 본문 |
| `card_le_largestInducedForestSize` | `(G.induce s).IsAcyclic`인 finset `s`는 `s.card ≤ largestInducedForestSize G`를 만족 |
| `isAcyclic_induce_insert` | `I`가 독립집합이면 `G.induce (insert x I)`는 비순환 |
| `indepNum_add_one_le_largestInducedForestSize` | `[Nontrivial α]`, `G.Connected` ⟹ `G.indepNum + 1 ≤ largestInducedForestSize G` |

명제의 충실성. upstream 보조 정의 `SimpleGraph.largestInducedForestSize`
(FormalConjecturesForMathlib, `Combinatorics/SimpleGraph/Induced.lean`)는
이 저장소의 의존성이 아니므로, 모듈이 그 본문
`sSup { n | ∃ s : Finset α, (G.induce s).IsAcyclic ∧ s.card = n }`
(`s`는 집합으로 강제 변환)을 그대로 복사한다. \(\alpha(G)\)는 mathlib의
`SimpleGraph.indepNum`이다. 타입 클래스 문맥
`[Fintype α] [DecidableEq α] [Nontrivial α]`과 가정 `G.Connected`는
upstream `conjecture61`의 것과 같다. `Nontrivial`은 꼭 필요하다. 정점이
하나인 그래프에서는 \(f=\alpha=1\)이기 때문이다. 이 정리에는 residue도
지름도 나오지 않는다. 따라서 upstream 명제를 향한 부분 결과일 뿐 그
증명은 아니며, upstream 선언은 여전히 `sorry`로 표시된 미해결 문제다.

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
- 위 네 결과는 [PROOF.ko.md](PROOF.ko.md)의 조합론적 논증과 기본
  부등식 \(r(G)\le\alpha(G)\)에 의존한다. Lean으로 증명한 것은 부등식
  (5)뿐이다. 전수 컴퓨터 검증은 유한 그래프족만 다루므로 일반 명제의
  인증서가 아니다.
