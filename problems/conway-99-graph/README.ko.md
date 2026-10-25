[English](README.md) | **한국어**

# Conway 99-graph

확인 기준일: 2026-08-11.

## 문제

강정규 그래프

```text
srg(99,14,1,2)
```

가 존재하는지를 묻는다. 즉 99개 정점을 가지며 모든 정점의 차수가 14이고,
인접한 두 정점은 공통 이웃을 1개, 비인접한 두 정점은 공통 이웃을 2개
가지는 그래프의 존재 문제이다. 동치로, 각 변은 정확히 한 삼각형에 놓이고
각 비변은 정확히 한 4-cycle에 놓인다.

## 현재 상태와 알려진 부분결과

2025년 동료평가 논문도 이 존재 문제를 미해결 문제로 명시한다. 그 논문은
가상 그래프의 자기동형군을 `G`라 할 때 다음을 컴퓨터 없이 증명했다.

- `2 | |G|`이면 `|G| | 6`이다.
- `7 | |G|`이면 `G`는 순환군 `Z_7`이다.

여기에는 존재 또는 비존재를 판정하는 새 계산 결과가 없다. 이 문서는 향후
계산 탐색 후보의 명제와 이미 알려진 제한을 기록한다.

## 계산 관점

한 정점을 고정하면 나머지 정점은 거리 층에 따라 `1 + 14 + 84`로
분해된다. 정규성, 공통이웃 등식, canonical augmentation을 SAT,
정수계획 또는 완전탐색에 직접 넣을 수 있다. 다만 실제 그래프의 대칭이
거의 없을 수도 있으므로 큰 자기동형군을 가정한 부분공간의 배제만으로 전체
문제를 해결할 수는 없다.

## 대칭 부분 경우: SAT/DRAT 배제 (2026-10-24)

**결과 (컴퓨터 검증, 부분 결과).** `Γ`가 srg(99,14,1,2)이고 `t`가 위수 2인
자기동형이면, `t`가 고정하는 정점은 정확히 1, 3, 5, 7, 9개 중 하나이다.
구체적으로, 아래 표에서 고정점이 `F >= 11`인 열 가지 국소 involution 유형
각각에 대해 "rooted frame 위의 어떤 srg(99,14,1,2)가 이 involution 아래
불변이다"라는 CNF가 충족 불가능하며, CaDiCaL이 만든 DRAT 증명을
`drat-trim`으로 검증했다. CI는 이 열 개의 증명을 다시 검사한다. 열 유형 중
여덟 개(`F >= 19`)는 아래에서 유도하는 초등적인 interlacing 상계 `F <= 18`로도
배제되므로, 이들에 대한 SAT 실행은 일관성 점검일 뿐이다. 이 상계로 처리되지
않는 부분은 `F = 11`, `F = 13`인 두 유형이다.

또한 `F = 9`인 유형 `(d, e) = (0, 2)`도 충족 불가능하다. 이 유형의
involution은 매칭 `Γ1(x)`의 변 두 개를 점별로 고정하고 나머지 다섯 개를
뒤집는다. CaDiCaL은 1061초가 걸렸고, 549 MB 증명은 drat-trim으로 로컬에서
검증했다. core 증명(105 MB)이 너무 커서 커밋하지 않았으므로 CI는 이 유형을
다시 검사하지 않는다. `certify_case.py`로 다시 만들 수 있다("재현" 참고).
`F = 9`인 다른 유형은 `(3, 1)`뿐이므로, 정점 9개를 고정하는 involution은
모든 고정 정점 `x`에서 유형 `(3, 1)`이다. 즉 매칭 `Γ1(x)`의 변 세 쌍을
맞바꾸고 일곱 번째 변을 점별로 고정한다.

"문헌" 절의 출처에서는 이 사실들을 찾지 못했지만 Behbahani–Lam (2011),
Makhnev–Minakova (2004), Wilbrink (1984)의 전문은 확인하지 못했으므로
새로움을 주장하지 않는다. 같은 파이프라인으로 이미 알려진 배제도 일관성
점검으로 재현했다(아래에서 "재현"으로 표시). 이 절의 내용은 존재 여부를
판정하지 않는다. 나머지 여덟 가지 involution 유형(`F <= 9`)과 고정점 없는 위수
3 자기동형은 여전히 미해결이며, 아래 실행에서는 UNKNOWN으로 끝났다.

### 고려해야 하는 대칭 유형

인접행렬을 `A`라 하면 `A^2 + A - 12I = 2J`이므로 고윳값은 14(한 번), 3,
-4이다. 중복도 `f, g`는 `f + g = 98`, `14 + 3f - 4g = tr A = 0`을 만족하므로
각각 54와 44이다.

*대각합 조건.* 자기동형 `g`의 치환행렬을 `P`, 고정 정점 수를 `F = tr P`,
`α1 = tr(PA) = #{x : x^g ~ x}`라 하자. `P`는 `A`와 교환하므로 고유공간을
보존한다. 고윳값 3과 -4의 고유공간에서 `P`의 대각합을 `χ1, χ2`라 하면
`F = 1 + χ1 + χ2`, `α1 = 14 + 3χ1 - 4χ2`이므로

```text
χ1 = (4F + α1 - 18)/7,    χ2 = (3F - α1 + 11)/7
```

은 정수이다. `g`의 위수가 소수 `p`이면, 차원 `d`인 고유공간에서 고윳값 1의
중복도를 `a`라 할 때 모든 원시 `p`제곱근이 같은 중복도 `b`를 가진다.
따라서 `χ = a - b`, `χ ≡ d (mod p)`, `-d/(p-1) <= χ <= d`이며, 특히
`χ1 ≡ 54`, `χ2 ≡ 44 (mod p)`이다. `p = 2`이면 이 조건은
`α1 ≡ 18 - 4F (mod 14)`만을 뜻하므로(99가 홀수라서 `F`는 홀수이다) `F`의
상계를 주지 않는다.

*고정점 상계.* `g ≠ 1`의 고정점 집합을 `Φ`(`|Φ| = F >= 1`), 나머지
`99 - F`개 정점을 `N`이라 하자. `x ∈ N`의 고정된 이웃은 `x`와
`x^g ≠ x`의 공통 이웃이므로, `x`의 고정된 이웃은 많아야
`max(λ, μ) = 2`개이다. `N`의 정점이 가지는 고정된 이웃 수의 평균을
`c <= 2`, `Φ` 내부의 평균 차수를 `a`라 하자. 분할 `{Φ, N}`의 몫행렬은
고윳값 14와 `a - c`를 가진다. interlacing에 의해 `a - c`는 `A`의 두 번째
고윳값 3 이하이다. `Φ`와 `N` 사이의 변을 세면 `F(14 - a) = (99 - F)c`이다.
따라서 `F(11 - c) <= (99 - F)c`, 즉 `11F <= 99c <= 198`이고 `F <= 18`이다.

*root를 고정하는 자기동형.* 정점 `x`를 고정하자. `λ = 1`이므로 `Γ1(x)`는
변 7개로 이루어진 완전 매칭이다. `Γ2(x)`의 각 정점은 `Γ1(x)` 안에 정확히 두
이웃을 가지며, 그 둘은 서로 인접하지 않는다(`λ = 1`). 서로 다른 정점은
서로 다른 쌍을 준다(`μ = 2`). 양쪽 모두 84개이므로 이 대응은 전단사이다.
그래서 인코더는 이 *rooted frame*(root 0, 매칭 `{2i-1, 2i}`를 가진
`Γ1 = {1..14}`, 비인접 쌍의 사전식 순서로 이름 붙인 `Γ2`)을 고정한다. `x`를
고정하는 자기동형은 `Γ1(x)` 위의 작용 `σ`로 결정된다. `σ`는 매칭을
보존하는 hyperoctahedral group `Z2 ≀ S7`(위수 `2^11·3^2·5·7`)의 원소이며,
켤레인 `σ`들은 이름만 바뀐 동치 충족 가능 CNF를 준다. 따라서 소수 위수
`p`별 경우는 다음과 같다.

- `p >= 11`: `p`는 `|Z2 ≀ S7|`을 나누지 않으므로, 정점을 고정하는 위수 `p`
  자기동형은 `Γ1`과 `Γ2`에 자명하게 작용해야 하는데 이는 불가능하다.
  따라서 고정점이 없고 `p | 99`, 즉 `p = 11`이며 순환 유형은 `11^9`이다
  (경우 `p11-free`).
- `p = 7`: `F ≡ 1 (mod 7)`이므로 고정점이 있고, `σ`는 매칭 변 위의 양의
  7-순환이다(`F = 1`, 경우 `p7-root`).
- `p = 5`: `F ≡ 4 (mod 5)`이므로 고정점이 있고, `σ`는 양의 5-순환이며 나머지
  두 변을 점별로 고정한다(`F = 9`, 경우 `p5-root`).
- `p = 3`: `σ`는 양의 3-순환 한 개 또는 두 개이고 나머지 변은 점별로
  고정된다(`F = 33` 또는 `F = 3`, 경우 `p3-root-a`, `p3-root-b`). 또는 `g`가
  순환 유형 `3^33`으로 고정점이 없다(경우 `p3-free`).
- `p = 2`: 99가 홀수이므로 모든 involution은 정점을 고정한다. 켤레를 제외하면
  `σ`는 매칭 변 `d`쌍을 서로 맞바꾸고, `e`개 변을 점별로 고정하고, 나머지
  `7 - 2d - e`개 변을 뒤집는다. 고정 정점 수는 `F = 1 + 2e^2 + 2d`이다.
  항등이 아닌 유형 `(d, e)`는 19가지이다(경우 `p2-d<d>-e<e>`). 위 상계에
  의해 실제로 가능한 것은 `F <= 18`인 11가지뿐이다.

### 인코딩 명세

`symmetric/srg_sym_encode.py`(표준 라이브러리만 사용)는 생성원으로 주어진 군
`G`에 대해 "`{0..v-1}` 위에 `G`-불변인 srg(v,k,λ,μ)가 존재한다"는 CNF를
쓴다(rooted 경우에는 rooted frame을 더한다).

1. 변수 `1..m`은 정점 비순서쌍의 `G`-궤도이며, 가장 작은 쌍 번호 `x·v + y`
   (`x < y`)의 증가 순서로 번호를 붙인다. 변수 `m+1..`은 필요한 정렬된 쌍
   `(A, B)`(`A < B`)에 대한 AND 게이트 `t = e_A ∧ e_B`이며 증가 순서로
   번호를 붙인다.
2. 제약 블록: 각 정점 궤도 대표 `x`(오름차순)에 대해
   `Σ_{y≠x} e(x,y) = k`. 이어서 각 쌍 궤도 대표 `(x, y)`(오름차순)에 대해,
   `z ∉ {x, y}`의 오름차순으로 리터럴 `e(x,z) ∧ e(y,z)`(두 쌍이 같은 궤도이면
   변수 자체, 아니면 AND 게이트)를 놓고, 그 뒤에 `e(x,y)`를 `μ - λ`번(또는
   `¬e(x,y)`를 `λ - μ`번) 덧붙여 합이 정확히 `max(λ, μ)`가 되게 한다. 이
   등식 하나가 변에 대해서는 `λ = 1`을, 비변에 대해서는 `μ = 2`를 나타낸다.
3. 리터럴 `N`개와 한계 `K`를 가진 각 블록은 완전 sequential counter를 쓴다.
   변수 `s(i,j)`는 "처음 `i`개 리터럴 중 적어도 `j`개가 참"을 뜻한다
   (`j <= min(i, K+1)`, `i` 다음 `j` 순서로 번호). 각 칸의 절은
   `s(i-1,j) → s(i,j)`, `s(i-1,j-1) ∧ l_i → s(i,j)`,
   `s(i,j) → s(i-1,j) ∨ l_i`, `s(i,j) → s(i-1,j-1)`이다. 여기서 `s(i-1,0)`은
   참으로, 없는 `s(i-1,j)`는 거짓으로 읽고, 이런 상수만 포함하는 절은
   단순화한다. 블록 끝에 단위절 `s(N,K)`와 `¬s(N,K+1)`(`K+1 <= N`일 때만)을
   붙인다.
4. 절 순서: frame 단위절(변수 순), AND 삼중절 `[¬t,a] [¬t,b] [t,¬a,¬b]`, 그
   다음 블록별 counter 절(칸은 `i` 다음 `j` 순서, 네 종류의 절은 위에 적은
   순서). DIMACS 출력: 머리줄 `p cnf V C`, 한 줄에 절 하나, 끝은 ` 0`.

모든 보조 변수는 함수적으로 정의되므로, frame 위의 `G`-불변
srg(99,14,1,2)는 모델을 준다. 따라서 UNSAT 답은 그 유형을 배제한다.
`symmetric/srg_sym_audit.py`는 인코더를 import하지 않는다. 군을 닫힘으로
다시 만들고, 생성원 불변량(위수, 고정점, 순환 유형, 매칭 위의 부호 있는 작용,
frame 불변성)을 다시 계산하고, DIMACS 바이트를 다시 유도하여 SHA-256을
`cases.json`과 비교한다.

### 결과

모든 실행은 2026-10-24에 `certify_case.py`로 했으며 CaDiCaL 3.0.1(기본 옵션,
이진 DRAT)과 drat-trim을 사용했다. `F`는 고정 정점 수이다. 시간은 다른
작업과 공유한 Apple M5 Max에서 잰 벽시계 시간이다. `> L s`는 CaDiCaL이 답
없이 시간 제한 `L`에서 멈췄다는 뜻이다(UNKNOWN). `(0, 2)`를 제외한 UNSAT
행의 core 증명과 절 core는 `symmetric/certs/`에 있다. `symmetric/results/<case>.json`과
`symmetric/logs/<case>.log`에는 풀이기와 drat-trim 출력이 있다(로컬 build
디렉터리는 `BUILD/`로 적었다).

root를 고정하는 involution(`σ`는 매칭 변 `d`쌍을 맞바꾸고 `e`개 변을 점별로
고정한다):

| `(d, e)` | `F` | 쌍 궤도 | 절 | 결과 | CaDiCaL | drat-trim (전체 / core 증명) | core 증명, xz |
|---|---|---|---|---|---|---|---|
| `(0, 6)` | 73 | 3746 | 5,417,579 | UNSAT, DRAT 검증 | 1.3 s | 4.6 s / 3.3 s | 2.6 kB |
| `(1, 5)` | 53 | 3126 | 4,505,079 | UNSAT, DRAT 검증 | 1.6 s | 5.9 s / 3.9 s | 12.9 kB |
| `(0, 5)` | 51 | 3075 | 4,431,622 | UNSAT, DRAT 검증 | 1.5 s | 5.9 s / 4.3 s | 27.4 kB |
| `(1, 4)` | 35 | 2739 | 3,956,262 | UNSAT, DRAT 검증 | 10.0 s | 17.8 s / 13.7 s | 107.7 kB |
| `(0, 4)` | 33 | 2706 | 3,910,617 | UNSAT, DRAT 검증 | 4.8 s | 7.6 s / 5.7 s | 69.9 kB |
| `(2, 3)` | 23 | 2571 | 3,727,018 | UNSAT, DRAT 검증 | 10.8 s | 38.1 s / 35.9 s | 319.2 kB |
| `(1, 3)` | 21 | 2550 | 3,699,105 | UNSAT, DRAT 검증 | 10.5 s | 33.3 s / 29.1 s | 255.5 kB |
| `(0, 3)` | 19 | 2531 | 3,674,084 | UNSAT, DRAT 검증 | 3.5 s | 5.4 s / 4.2 s | 41.0 kB |
| `(2, 2)` | 13 | 2486 | 3,616,187 | UNSAT, DRAT 검증 | 3.0 s | 6.3 s / 5.0 s | 71.7 kB |
| `(1, 2)` | 11 | 2475 | 3,602,556 | UNSAT, DRAT 검증 | 2.5 s | 6.1 s / 4.7 s | 50.6 kB |
| `(0, 2)` | 9 | 2466 | 3,591,727 | UNSAT, 로컬에서 DRAT 검증 | 1061.3 s | 1465.1 s / 1263.0 s | 커밋 안 함 (28.44 MB) |
| `(3, 1)` | 9 | 2466 | 3,591,723 | UNKNOWN | > 1800 s | - | - |
| `(2, 1)` | 7 | 2459 | 3,583,680 | UNKNOWN | > 600 s | - | - |
| `(3, 0)` | 7 | 2459 | 3,583,676 | UNKNOWN | > 600 s | - | - |
| `(1, 1)` | 5 | 2454 | 3,578,403 | UNKNOWN | > 600 s | - | - |
| `(2, 0)` | 5 | 2454 | 3,578,401 | UNKNOWN | > 600 s | - | - |
| `(0, 1)` | 3 | 2451 | 3,575,874 | UNKNOWN | > 600 s | - | - |
| `(1, 0)` | 3 | 2451 | 3,575,874 | UNKNOWN | > 600 s | - | - |
| `(0, 0)` | 1 | 2450 | 3,576,077 | UNKNOWN | > 600 s | - | - |

다른 소수 위수. `p3-root-a`(`F = 33`)는 interlacing 상계로도 배제된다.

| 경우 | `Γ1` 위의 작용 또는 순환 유형 | `F` | 문헌 | 쌍 궤도 | 절 | 결과 | CaDiCaL | core 증명, xz |
|---|---|---|---|---|---|---|---|---|
| `p11-free` | 순환 유형 `11^9` | 0 | 재현 | 441 | 627,372 | UNKNOWN | > 1800 s | - |
| `p7-root` | 매칭 변 7개 위의 양의 7-순환 | 1 | 재현 | 693 | 1,000,545 | UNKNOWN | > 1800 s | - |
| `p5-root` | 양의 5-순환, 변 2개 점별 고정 | 9 | 재현 | 999 | 1,459,080 | UNKNOWN | > 1800 s | - |
| `p3-root-a` | 양의 3-순환 1개, 변 4개 점별 고정 | 33 | 재현 | 1969 | 2,838,689 | UNSAT, DRAT 검증 | 2.1 s | 28.6 kB |
| `p3-root-b` | 양의 3-순환 2개, 변 1개 점별 고정 | 3 | 재현 | 1619 | 2,359,468 | UNKNOWN | > 1800 s | - |
| `p3-free` | 순환 유형 `3^33` | 0 | 미해결 | 1617 | 2,354,814 | UNKNOWN | > 1800 s | - |

### 인코더 검증

`symmetric/validate_encoder.py`는 2026-10-24에 실행했다. 전체 900초가
걸렸고, 그중 약 14분은 srg(243,22,1,2) 풀이이다.

- Part A(풀이기 없음, `--semantic-only`, 1초 미만). 알려진 그래프에서 읽어 낸
  할당이 모든 절을 만족한다(보조 변수는 단위 전파로 계산한다). 대상은 다음과
  같다. rooted frame 위의 Paley(9)와, root를 고정하는 다섯 치환 중
  자기동형인 각 치환. rooted frame 위의 Berlekamp–van Lint–Seidel
  srg(243,22,1,2)와, root를 고정하는 위수 110의 군. Petersen, Clebsch,
  Shrikhande 그래프 각각의 자기동형 40개. 이것이 UNSAT 주장이 기대는 건전성
  방향이며, srg(243,22,1,2) frame CNF의 명시적 모델도 보여 준다.
- Part B(CaDiCaL). `S_n`의 모든 순환 유형에 대해, 그 유형인 치환 하나의
  CNF는 목록의 그래프가 그 유형의 자기동형을 가질 때에만 SAT여야 한다. 확인한
  결과: Paley(9) 30개 유형(SAT 6), Petersen 42개(SAT 7), Paley(13)
  101개(SAT 5), Clebsch 231개(SAT 12), srg(16,6,2,2)(rook 그래프와
  Shrikhande) 231개(SAT 13). 자명군을 쓰는 rooted frame에서는
  srg(9,4,1,2)가 SAT이고, srg(19,6,1,2)와 srg(33,8,1,2)는 UNSAT이다(이
  매개변수는 실현 불가능하다). 위수 110의 군 아래 BvLS는 SAT이다. 모든 SAT
  모델은 디코딩하여 불변 srg인지 확인했다.

### 재현

`problems/conway-99-graph/symmetric`에서 실행한다(표준 라이브러리 Python 3,
Apple M5 Max에서 2026-10-24에 측정).

```sh
python3 srg_sym_audit.py               # 군 데이터 + CNF 해시, 25개 경우 전체 (약 25초)
python3 verify_certificates.py         # 11개 절 core에 대한 drat-trim (약 15초)
python3 verify_certificates.py --full  # 같은 증명을 전체 CNF로 확인 (약 95초)
python3 validate_encoder.py --semantic-only   # Part A (1초 미만)
python3 validate_encoder.py            # Part A, B, cadical 필요 (900초)
python3 srg_sym_encode.py cnf p2-d1-e2 -o /tmp/p2-d1-e2.cnf   # CNF 하나 (약 5초)
python3 certify_case.py p2-d1-e2 --build /tmp/c99 --out /tmp/c99 --limit 5400   # 전체 파이프라인, 약 25초
python3 certify_case.py p2-d0-e2 --build /tmp/c99 --out /tmp/c99 --limit 5400   # 유형 (0, 2), 약 65분
```

`certify_case.py`는 CNF를 쓰고 바이트 단위로 감사한다. 그다음
`cadical -t LIMIT CNF PROOF`(CaDiCaL 3.0.1, 이진 DRAT)를 실행한다. UNSAT이면
`drat-trim CNF PROOF -i -l CORE -C`, 이어서 `drat-trim CNF CORE -i -c
CLAUSES`를 실행하고, `<case>.core.drat.xz`와 `<case>.clause-core.txt.xz`를
build 디렉터리에 쓴다. 커밋한 사본은 `certs/`에 있다. 두 drat-trim 실행이
모두 `s VERIFIED`를 출력할 때에만 종료 상태 0으로 끝난다. `--out`이 없으면
`results/<case>.json`과 `logs/<case>.log`를 덮어쓴다. 빠른 UNSAT 11개 경우에
한 번 더 실행했을 때 core 증명이 바이트 단위로 같게 재현되었다. `(0, 2)`에
대해서는 `cases.json`에 전체 증명, core 증명, 절 core의 SHA-256을 기록해
두었으므로 다시 만든 증명과 비교할 수 있다. `drat-trim`은 backward mode에서
단위절 삭제를 무시한다는 통상적인 경고를 출력하며, core lemma는 모두
RUP이다(RAT lemma 0개). CNF(11–109 MB)와 전체 증명(22–71 MB, `(0, 2)`는
549 MB)은 커밋하지 않는다.

### 문헌과 표시

- Wilbrink (1984), Cesarz–Woldar의 인용에 따름: `Γ`는 정점 추이적이 아니다.
- Makhnev–Minakova (2004), Cesarz–Woldar의 인용에 따름: `|Aut Γ|`는
  `2·3^3·7·11`을 나눈다.
- Behbahani–Lam (2011), Crnković–Maksimović (2020, Theorem 7.1)의 서술에
  따름: `|Aut Γ|`의 가능한 소인수는 2와 3뿐이며, 위수 3인 자기동형은
  고정점이 없다. 우리의 경우 `p11-free`, `p7-root`, `p5-root`,
  `p3-root-a`, `p3-root-b`가 여기에 해당한다.
- Crnković–Maksimović (2020): 위수 6 또는 9인 자기동형군(`Z6`, `S3`, `Z9`,
  `E9`)은 없다.
- Cesarz–Woldar (2025): `2 | |G|`이면 `|G| | 6`이고 `7 | |G|`이면
  `G ≅ Z7`임을 컴퓨터 없이 증명했다.
- Thakkar–Severini (arXiv:2608.11211, 2026): CP-SAT으로 고정점 하나인 `Z7`
  모델은 14코어 48시간 뒤에도 UNKNOWN이었고, 고정점 없는 `Z3` 모델은
  1800초 안에 UNKNOWN이었다.
- arXiv:2610.16266(심사 전, 2026)은 sum-of-squares 삼각형 상계로 비존재를
  주장한다. 여기서는 확인하지도 사용하지도 않는다.

이 출처들에서 고정점 수에 의한 involution 배제는 찾지 못했다. 우리가 읽은
문헌에서 involution 자체는 배제되지 않았다. 표에서 "재현"은 인용한 결과가
이미 배제하는 경우이고, "미해결"은 배제된 것을 찾지 못한 경우이다.

### 주장하지 않는 것

- srg(99,14,1,2), 또는 involution을 가진 srg(99,14,1,2)의 존재·비존재. 여덟
  가지 involution 유형(`F ∈ {1,3,5,7}`, 그리고 `F = 9`인 `(3, 1)`)과 고정점
  없는 위수 3은 여기서 미해결로 남는다.
- 유형 `(0, 2)`의 CI 검사 배제. 증명은 로컬에서 검증했지만 커밋하지 않았다.
- 어떤 새로움도 주장하지 않는다. interlacing 상계는 초등적이며, 배제한 유형은
  우리가 읽지 않은 문헌에 이미 있을 수 있다.
- 인용한 결과를 넘는 합성수 위수 군은 인코딩하지 않았다.
- UNKNOWN 항목은 시간 초과일 뿐 어느 쪽의 증거도 아니다.

## FormalConjectures 원본

[로컬 upstream snapshot](upstream/README.md)은 99개 정점에 대한 정확한
Lean 명제와 고정 commit 정보를 보존한다. 이 파일은 `sorry`가 있는 문제
명제이며, 여기의 상태 조사도 존재·비존재를 판정하지 않는다.

## 근거

- H. A. Wilbrink, On the (99,14,1,2) strongly regular graph, in *Papers
  dedicated to J. J. Seidel*, Eindhoven Univ. Tech. Report 84-WSK-03 (1984),
  342--355 (원문 미확인).
- A. A. Makhnev and I. M. Minakova, On automorphisms of strongly regular
  graphs with parameters λ = 1, μ = 2, *Diskret. Mat.* 16 (2004), no. 1,
  95--104 (원문 미확인).
- M. Behbahani and C. Lam,
  [Strongly regular graphs with non-trivial automorphisms](https://doi.org/10.1016/j.disc.2010.10.005),
  *Discrete Math.* 311 (2011), 132--144 (원문 미확인, Crnković–Maksimović를
  통해 인용).
- D. Crnković and M. Maksimović, Construction of strongly regular graphs
  having an automorphism group of composite order, *Contrib. Discrete Math.*
  15 (2020), no. 1, 22--41.
- A. Thakkar and S. Severini,
  [A forced-structure reduction and verifiable bounds for Conway's 99-graph](https://arxiv.org/abs/2608.11211),
  arXiv:2608.11211 (2026).
- M. Cesarz and A. Woldar,
  [On the automorphism group of a putative Conway 99-graph](https://alco.centre-mersenne.org/articles/10.5802/alco.418/),
  *Algebraic Combinatorics* 8 (2025), 379--398.
