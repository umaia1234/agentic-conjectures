[English](README.md) | **한국어**

# Chvatal 하향 닫힌 집합 추측: DRAT 인증서를 갖춘 SAT 환원

이 디렉터리는 하향 닫힌 집합(downset)의 교차 부분족에 관한 Chvatal 추측을
유한 범위에서 계산으로 공략한 기록입니다. 추측의 새로운 경우를 해결했다고
주장하지 **않습니다**. 원소가 일곱 개 이하인 바탕집합에 대한 인증된 배제
결과는 이미 출판된 정리를 재현한 것이며, 원소가 여덟 개인 경우는 여기서
해결되지 않았습니다.

## 명제

유한 하향 닫힌 집합 `D`(`A in D`이고 `B subseteq A`이면 `B in D`)에 대해

- `alpha(D)`는 `D`의 쌍마다 교차하는 부분족 중 가장 큰 것의 크기이고,
- `Delta(D) = max_i |{A in D : i in A}|`는 가장 큰 별(star)의 크기입니다.

Chvatal 추측은 다음과 같습니다.

```text
alpha(D) <= Delta(D) for every finite downset D.
```

일반적인 추측은 여전히 미해결입니다. 인증서를 생성하는 정수계획법 계산이
바탕집합의 원소가 일곱 개 이하인 경우를 증명했습니다. 같은 논문은 원소가
여덟 개인 경우에 대해서는 부동소수점 풀이만 보고합니다.

- L. Eifler, A. Gleixner, J. Pulaj, *A Safe Computational Framework for
  Integer Programming Applied to Chvatal's Conjecture*, ACM TOMS 48 (2022),
  <https://doi.org/10.1145/3485630> (아래에서 EGP).
- 프리프린트와 공개된 계산 설명:
  <https://optimization-online.org/2018/09/6802/>.

## 결과

| 바탕집합 | CNF | 결과 | 아래 증명 외의 가정 |
|---|---|---|---|
| 원소 6개 | `generate_cnf.py --n 6 --reduced --encoding cardnet` | UNSAT, drat-trim이 DRAT 증명을 승인 | Kleitman-Magnanti, Sterboul, 원소 5개 경우의 추측, PySAT 기수 네트워크 |
| 원소 3~7개 | `generate_rank_cnf.py`, 모든 계수 `3 <= r <= n` (CNF 15개) | 모두 UNSAT, drat-trim이 DRAT 증명을 승인 | Kleitman-Magnanti |
| 원소 8개 | `generate_rank_cnf.py`, 계수 3, 7, 8 | UNSAT, drat-trim이 DRAT 증명을 승인 | Kleitman-Magnanti |
| 원소 8개 | `generate_rank_cnf.py`, 계수 4, 5, 6 | 미결정: 제한 시간 안에 결과 없이 중단 | |

아래에서 증명하는 환원과 계수 분할 인증서를 합치면 다음이 성립합니다.
**Kleitman-Magnanti 정리를 가정하면, 원소가 일곱 개 이하인 바탕집합 위의
모든 하향 닫힌 집합에서 Chvatal 추측이 성립합니다.** 이는 EGP의 `n <= 7`
정리를 정확한 MILP 대신 SAT와 DRAT로 인증해 재현한 것이며 새로운 결과가
아닙니다. 원소가 여덟 개인 경우에는 집합 수가 가장 적은 반례가 있다면 그
계수(가장 큰 원소의 크기)가 4, 5, 6 중 하나라는 사실만 보입니다.

아래의 환원은 비형식적 증명이며 Lean 증명이 아닙니다. CNF 생성기는 신뢰
대상 코드입니다. `generate_rank_cnf.py`는 Python 표준 라이브러리만 쓰며
`--self-test`로 인코딩을 전수 탐색과 대조하고, `generate_cnf.py`는 기수
제약을 PySAT으로 만듭니다.

## 포화 보조정리

다음 환원은 초등적이지만 SAT 탐색에 유용합니다.

**보조정리.** Chvatal 추측에 반례가 있으면 다음을 만족하는 반례
`(D, Y)`도 있습니다.

1. `D = down(Y) := {S : S subseteq T for some T in Y}`;
2. `Y`는 `D`의 교차 부분족 중 크기가 최대인 것;
3. 모든 `T in D \ Y`에 대해 `T`와 서로소인 `S in Y`가 존재.

**증명.** 반례 `D0`에서 시작해 크기가 최대인 교차 부분족 `Y`를 고르고
`D = down(Y)`로 둡니다. `D0`가 하향 닫혀 있고 `Y subseteq D0`이므로
`Y subseteq D subseteq D0`입니다. `D0`에서 `D`로 옮겨 가도 어떤 별도
커지지 않고 `|Y|`는 그대로이므로 `|Y| > Delta(D0) >= Delta(D)`이고,
`(D, Y)`는 여전히 반례입니다. `D`의 교차 부분족은 모두 `D0`의 교차
부분족이기도 하므로 `Y`는 `D`에서도 최대입니다. 끝으로 `T in D \ Y`가
`Y`의 모든 원소와 만난다면 `Y union {T}`는 `Y`보다 큰 `D`의 교차
부분족이 되어 모순입니다. 따라서 세 주장이 모두 성립합니다. 증명 끝.

## 원래의 환원 인코딩 (`generate_cnf.py`)

불 변수 `x_T = [T in D]`, `y_T = [T in Y]`로 쓰면 보조정리의 주장 3은 다음
절(clause)입니다.

```text
not x_T or y_T or (or_{S intersect T = empty, S nonempty} y_S).
```

주장 1은 양방향으로 인코딩합니다.

```text
y_T -> x_S                         for every S subseteq T,
x_S -> or_{T superseteq S} y_T.
```

각 원소 `i`에 대해 반례의 엄격한 부등식 `|Y| >= |star_i(D)| + 1`은 다음
기수 제약으로 인코딩합니다.

```text
sum_{S nonempty} y_S + sum_{S contains i} (not x_S) >= 2^(n-1) + 1.
```

### `n = 6`에서 각 환원이 건전한 이유

원소가 다섯 개 이하인 바탕집합에서 추측이 성립한다고 가정하고(EGP
Proposition 3, 또는 아래의 계수 분할 연쇄), `D0`를 `{0, ..., 5}` 위의
반례라고 합시다. 최대 교차 부분족 `Y subseteq D0`를 고르고
`D = down(Y)`로 두면 `(D, Y)`는 모든 절을 만족합니다.

1. `Y`의 교차성, `D = down(Y)`, 포화 조건: 보조정리.
2. `y_{} = 0`, `x_{} = 1`: 공집합은 어떤 집합과도 만나지 않고,
   `|Y| > Delta(D) >= 0`이므로 `Y`는 공집합족이 아닙니다.
3. `1 <= |S| <= 2`이면 `y_S = 0` (EGP Corollary 3): `S in Y`이고
   `S subseteq {a, b}`이면 `Y`의 모든 원소가 `S`와 만나므로 `Y`는 `a`와 `b`의
   별의 합집합에 들어갑니다. Kleitman-Magnanti 정리(EGP Theorem 5: "Any
   intersecting family that is contained in the union of two stars generates
   a downset that satisfies Conjecture 1")에 따라 `D = down(Y)`는 추측을
   만족하므로 `|Y| > Delta(D)`와 모순입니다.
4. 모든 원소에 대해 `x_{i} = 1` (EGP Proposition 4): `{i}`가 `D`에 없으면
   `D`의 어떤 원소도 `i`를 포함하지 않으므로 `D`는 원소 다섯 개 위의
   반례가 됩니다.
5. `x_{0,1,2,3} = 1` (EGP Proposition 5): Sterboul 정리에 따르면 모든
   원소의 크기가 3 이하인 하향 닫힌 집합에서는 추측이 성립하므로, `D`에는
   원소가 네 개 이상인 집합이 있습니다. 그 4-부분집합 하나가 `D`에 있고,
   바탕집합의 이름을 바꾸어 그것을 `{0, 1, 2, 3}`으로 만들 수 있습니다.
   다른 모든 제약은 이름 바꾸기에 대해 불변입니다.
6. 기수 제약: 원소 `i`에 대해 리터럴 `y_S`가 63개, `not x_S`가 32개
   있고, 그중 참인 것은 정확히 `|Y| + 32 - |star_i(D)|`개입니다. 이 값이
   33 이상인 것은 `|Y| >= |star_i(D)| + 1`과 동치입니다.

따라서 원소 여섯 개 위의 모든 반례는 스크립트가 쓴 모든 절을 만족하는
주 변수 값을 줍니다. 보조 변수는 PySAT의
`CardEnc.atleast(..., encoding=cardnetwrk)`에서만 나옵니다. 그러한 모든
할당이 보조 변수까지 확장된다는 사실(기수 네트워크의 완전성)은 PySAT을
신뢰하는 것이며 여기서 검사하지 **않았습니다**. 아래의 계수 분할 인코딩이
카운터를 직접 작성하는 이유가 이것입니다.

### `n = 6`의 DRAT 인증서

이제 `generate_cnf.py --solve --proof PATH`가 PySAT 솔버의 DRAT 기록을
씁니다. CNF는 변수 16,238개, 절 25,356개이고 SHA256은
`f8d119eac17820ae405c590c13aa4fae93b8cf787faa21092f90a1384858f2eb`
(python-sat 1.9.dev17)입니다. 공유 중인 18코어 머신에서 잰 값은 다음과
같습니다.

- PySAT CaDiCaL 1.9.5: 충돌 156,925회 후 UNSAT. CNF 생성, 풀이, 41.3 MB
  텍스트 DRAT 기록에 14.4초가 걸렸고 drat-trim은 12.5초 뒤
  `s VERIFIED`를 출력했습니다.
- 독립 실행 CaDiCaL 3.0.1: 충돌 161,702회(3.3초) 후 UNSAT, 13.6 MB 이진
  DRAT, drat-trim `s VERIFIED` 3.3초.

증명은 커밋하기에 너무 큽니다. `certify_drat.py repo-n6`이 CNF를 다시
만들고 SHA256을 [`drat_manifest.json`](drat_manifest.json)과 비교한 뒤
PySAT 증명을 얻어 drat-trim으로 검사합니다. `n6_solver_result.json`은
증명 없이 실행했던 이전 기록이며 그대로 보존합니다.

같은 인코딩의 `n = 7` 실행은 CaDiCaL 3.0.1 CPU 시간 1015.6초, 충돌
11,613,975회 후 결과 없이 중단했고, 계수 분할 인코딩이 이를 대신합니다.

## 계수 분할 인코딩 (`generate_rank_cnf.py`)

바탕집합 `{0, ..., n-1}`과 `3 <= r <= n`인 계수(rank) `r`에 대해, 이 CNF는
다음을 만족하는 `(D, Y)`가 있을 때 그리고 그때에만 충족 가능합니다.

1. `Y`는 교차족이고 `Y`의 모든 원소는 원소를 세 개 이상 가짐;
2. `D = down(Y)`;
3. 포화: 모든 `T in D \ Y`는 `Y`의 어떤 원소와 서로소;
4. 모든 한원소 집합이 `D`에 속함;
5. 모든 원소 `i`에 대해 `|Y| >= |star_i(D)| + 1`;
6. 최소성: `Tight := {i : |star_i(D)| = |Y| - 1}`이 `D`에 속하지 않음;
7. 계수: `{0, ..., r-1}`은 `D`에 속하고 `(r+1)`-집합은 `D`에 없음;
8. 대칭 깨기: 각 블록 `{0, ..., r-1}`, `{r, ..., n-1}` 안의 연속한
   `j, j+1`에 대해 `|star_j(D)| >= |star_{j+1}(D)|`이고, 같을 때는 비트마스크
   `S`의 오름차순으로 나열한 벡터 `(x_S)`가 `j`와 `j+1`을 맞바꾼 족의 벡터보다
   사전식으로 크거나 같음.

여기에 `r < n`일 때 유도되는 단위 절 "`r`은 `Tight`에 속함"(아래 단계
(f))을 더합니다.

**명제.** `n >= 3`이고 원소가 `n - 1`개 이하인 바탕집합 위의 모든 하향
닫힌 집합에서 추측이 성립한다고 가정합시다. `{0, ..., n-1}` 위의 어떤
하향 닫힌 집합에서 추측이 실패하면, 어떤 `(D, Y)`와 어떤
`r in {3, ..., n}`에 대해 조건 1-8과 단위 절이 성립합니다.

**증명.** `{0, ..., n-1}` 위의 반례 하향 닫힌 집합 중 `|D|`가 최소인 `D`와
최대 교차 부분족 `Y subseteq D`를 고르면 `|Y| = alpha(D) > Delta(D)`입니다.

(a) `M`을 `D`의 극대 원소라 하고 `D' = D \ {M}`이라 합시다. `D'`는 하향
닫혀 있고, (`Y`에서 `M`을 빼면) `alpha(D') >= alpha(D) - 1`이며,
`|star_i(D')| = |star_i(D)| - [i in M]`입니다. 최소성에 의해 `D'`는 반례가
아닙니다. 조건 5는 `|Y| > Delta(D)`를 다시 쓴 것입니다.
`alpha(D) >= Delta(D) + 2`라면 `alpha(D') >= Delta(D) + 1 > Delta(D')`가
되어 모순이므로 `|Y| = Delta(D) + 1`이고, `Tight`는 가장 큰 별을 가진
원소들의 (공집합이 아닌) 집합입니다. `Tight subseteq M`이라면
`Delta(D') = Delta(D) - 1 < Delta(D) <= alpha(D')`가 되어 역시 모순입니다.
따라서 `Tight`는 `D`의 어떤 극대 원소에도 포함되지 않고, 곧 `Tight`는
`D`에 속하지 않습니다(조건 6).

(b) `down(Y) subseteq D`도 반례이므로(`|Y| > Delta(D) >= Delta(down(Y))`)
최소성에 의해 `D = down(Y)`입니다(조건 2). `T in D \ Y`가 `Y`의 모든
원소와 만난다면 `Y union {T}`가 더 큰 교차족이 됩니다(조건 3).

(c) `Y`의 어떤 원소 `S`(`Y`가 교차족이므로 공집합이 아님)의 크기가 2
이하라면 `Y`는 두 별의 합집합에 들어가고, Kleitman-Magnanti 정리에 의해 `D = down(Y)`는 추측을 만족하게
됩니다(조건 1).

(d) `{i}`가 `D`에 없다면 `D`는 원소 `n - 1`개 위의 반례가 됩니다(조건 4).

(e) `D`의 원소 중 가장 큰 크기를 `r`이라 하면 (c)에 의해 `r >= 3`입니다.
조건 1-6은 바탕집합의 이름 바꾸기에 대해 불변입니다.
`{0, ..., r-1} in pi(D)`인 모든 이름 바꾸기 `pi` 중에서 키
`(|star_0|, ..., |star_{n-1}|, x_0, x_1, ..., x_{2^n - 1})`가 사전식으로 가장
큰 것을 고릅니다(`x_S`는 비트마스크 순서, 참이 거짓보다 큼). 조건 7이
성립합니다. 같은 블록의 두 원소를 맞바꾸어도 `{0, ..., r-1}`은 `D`에
남으므로 키가 커질 수 없고, 연속한 `j, j+1`에 대해서는 이것이 조건
8입니다.

(f) `r < n`이면: `Tight`는 `D`에 없지만 `{0, ..., r-1}`은 `D`에 있으므로
`|star_i(D)| = Delta(D)`인 `i >= r`가 있습니다. 조건 8에 의해
`|star_r(D)| >= |star_i(D)|`이므로 `r in Tight`입니다. 증명 끝.

**따름정리.** 원소가 두 개 이하인 바탕집합에서는 공집합족이 아닌 모든
교차족이 크기 2 이하인 집합을 포함하므로 Kleitman-Magnanti 정리에 의해
추측이 성립합니다. 귀납법으로, 모든 `3 <= r <= n <= 7`에 대해 계수 분할
CNF가 UNSAT이면 원소가 일곱 개 이하인 바탕집합에서 추측이 성립합니다.
계수 3도 CNF 중 하나로 직접 풀기 때문에 Sterboul 정리는 필요하지 않고,
PySAT도 필요하지 않습니다.

**인코딩 세부 사항.** 개수 세기에는 양방향 절을 갖춘 totalizer를 써서 각
카운터 출력이 "입력 중 적어도 `t`개가 참"과 동치가 되게 합니다. 조건 6에서
보조 변수 `tight_i`는 `tight_i -> |star_i(D)| >= |Y| - 1`을 만족하고, 각
`S`마다 절 `not x_S or (or_{i not in S} tight_i)`를 둡니다. `D`가 하향
닫혀 있으므로 이 절들은 참인 `tight_i`들의 집합이 `D`에 없다는 뜻이고,
이는 `Tight`가 `D`에 없을 때 정확히 충족 가능합니다. 조건 8에서는 단항
카운터로 `|star_j| >= |star_{j+1}|`을 절 단위로 표현하고, 두 값이 같으면
`j in S`, `j+1 not in S`인 쌍 `(S, S xor {j, j+1})`을 비트마스크 오름차순으로
비교하는 사전식 사슬이 켜집니다.

**충실성 검사.** UNSAT 주장에는 조건 1-8을 만족하는 모든 `(D, Y)`가 모델로
확장된다는 사실이 필요합니다. `generate_rank_cnf.py --self-test`(약
40초)는 보조 변수의 정확한 값까지 포함한 확장을 직접 만들어 절마다
검사합니다. 대상은 `n = 4, 5`에서 크기 3 이상인 집합들로 이루어진 모든
족, `n = 6, 7, 8`에서 단계 (e)의 표준형으로 옮긴 무작위 포화족, 그리고
조건 6을 만족하는 순환 대칭족과 Fano 평면입니다. 실제 족을 검사할 수
있도록 개수 경계는 `|Y| - Delta(D)`로 완화합니다. 또한 표준형이 조건 7-8을
만족하는지, 입력이 아홉 개 이하인 totalizer가 정확한지도 검사합니다.

## 인증서

[`drat_manifest.json`](drat_manifest.json)은 모든 `(n, r)`에 대해 CNF의
크기와 SHA256, 인증서 종류, 측정한 솔버 작업량을 기록합니다. 커밋한
증명은 [`drat/`](drat/)에 있으며, CaDiCaL 3.0.1 증명을 `drat-trim -l`로
핵심 보조 절만 남긴 텍스트 DRAT입니다(합계 1.5 MB).

| `n` | 계수 | CaDiCaL 3.0.1 충돌 횟수 | 인증서 |
|---|---|---|---|
| 3, 4, 5 | 전부 | 최대 7 | 커밋됨 |
| 6 | 3, 4, 5, 6 | 334; 4,474; 381; 0 | 커밋됨 |
| 7 | 3, 6, 7 | 297; 9,849; 0 | 커밋됨 |
| 7 | 4 | 2,125,950 | `--solve`로 재생성 |
| 7 | 5 | 841,502 | `--solve`로 재생성 |
| 8 | 3, 8 | 550; 0 | 커밋됨 |
| 8 | 7 | 308,332 | `--solve`로 재생성 |

계수 `r = n`은 단위 전파만으로 반박됩니다. 조건 7에 의해
`{0, ..., n-1}`이 `D`에 들어가므로 `Tight`를 포함한 모든 집합이 `D`에
속하게 되어 조건 6과 모순입니다. 다시 생성한 이진 DRAT 증명의
크기는 145 MB(`n7_r4`, 풀이 184초, drat-trim 208초), 64 MB(`n7_r5`, 59초,
80초), 22 MB(`n8_r7`, 14초, 19초)이며, 공유 머신에서 `--solve` 실행 전체에
벽시계 시간 564초(CPU 287초)가 걸렸습니다.

### 재현

```bash
cd problems/chvatal-downset
# 커밋된 증명(CI): 15개 경우, 약 2초. PATH에 drat-trim 필요.
python3 certify_drat.py rank
# 커밋하기에 너무 큰 증명: n7_r4, n7_r5, n8_r7. PATH에 cadical과
# drat-trim 필요. 위 머신에서 약 10분.
python3 certify_drat.py rank --solve
# 원래 인코딩, n = 6 (PySAT 증명, 약 30초와 pip 설치 시간).
python3 -m venv /tmp/chvatal-drat-venv
/tmp/chvatal-drat-venv/bin/pip install "python-sat[pblib]==1.9.dev17"
/tmp/chvatal-drat-venv/bin/python certify_drat.py repo-n6
# 인코딩 자체 검사, 약 40초.
python3 generate_rank_cnf.py --self-test
```

한 경우를 직접 확인하려면:

```bash
python3 generate_rank_cnf.py --n 7 --rank 4 --output /tmp/n7_r4.cnf
cadical /tmp/n7_r4.cnf /tmp/n7_r4.drat
drat-trim /tmp/n7_r4.cnf /tmp/n7_r4.drat
```

인증서가 없던 이전 명령도 그대로 동작합니다.

```bash
python -m venv /tmp/chvatal-sat-venv
/tmp/chvatal-sat-venv/bin/pip install "python-sat[pblib]"
/tmp/chvatal-sat-venv/bin/python generate_cnf.py \
  --n 6 --reduced --encoding cardnet --solve
/tmp/chvatal-sat-venv/bin/python generate_cnf.py --self-test
```

## 원소가 여덟 개인 경우

계수 3, 7, 8은 인증되었습니다(위 표). 계수 4, 5, 6은 `generate_rank_cnf.py`가
만든 CNF(SHA256은 매니페스트에 기록)에 대해 `cadical -t 5400`(CaDiCaL 3.0.1,
증명 출력 없음)으로 실행했습니다. 세 실행은 공유 머신에서 동시에 돌았고,
벽시계 90분 제한에 걸려 결과 없이 중단되었습니다.

| 계수 | CPU 초 | 충돌 횟수 | 결과 |
|---|---|---|---|
| 4 | 3,690.8 | 35,463,210 | 미정 |
| 5 | 3,691.0 | 31,695,931 | 미정 |
| 6 | 4,068.9 | 44,748,818 | 미정 |

가장 어려운 계수의 비용은 빠르게 늘어납니다. 계수 4는 `n = 6`에서 충돌
4,474회, `n = 7`에서 2,125,950회가 필요합니다. 같은 배율(약 475배)이라면
`n = 8`의 계수 4는 충돌 약 `10^9`회(측정값이 아닌 외삽)와 수십 기가바이트
크기의 증명이 필요합니다. 탐색적 변형 두 가지(스크래치 스크립트, 커밋하지
않음)도 이 그림을 바꾸지 못했습니다. `n = 7` 계수 4에서 잰 결과는 다음과
같습니다.

- `|Y|`의 값에 대한 큐브 앤 컨커: "`|Y| = k`"에 해당하는 단위 절을 더하면
  큐브 99개가 생기고 모두 UNSAT입니다. 가장 어려운 큐브는 충돌 485,978회로
  끝났지만 합계는 3,901,795회로 단일 실행의 1.8배였습니다.
- 더 강한 대칭 깨기: 블록 안의 모든 맞바꿈과, "`{0, ..., r-1} - {j} + {k}`가
  `D`에 속함"을 조건으로 하는 블록 간 맞바꿈 `(j, k)` 각각(이 조건이면
  맞바꾼 뒤에도 `{0, ..., r-1}`이 `D`에 남음)에 사전식 제약을 더해도 충돌
  횟수는 2,125,950회에서 1,508,117회로 줄었을 뿐입니다.

[`n8_attempt_summary.md`](n8_attempt_summary.md)의 MILP 및 실현 가능성 실행
기록은 바뀌지 않았습니다. 따라서 원소가 여덟 개인 경우는 **이번 시도로
해결되지 않았습니다**.

## 신뢰 경계

- 새로움 없음: `n <= 7`은 EGP의 정리이며 여기서는 SAT로 재현했습니다.
- Kleitman-Magnanti 정리는 인용할 뿐 다시 증명하지 않습니다. 환원과
  충실성 논증은 서술된 증명과 무작위 및 전수 자체 검사이며 형식 증명이
  아닙니다.
- `generate_cnf.py`의 `n = 6` 인증서는 추가로 Sterboul 정리, 원소 다섯 개
  경우, PySAT 기수 네트워크에 의존합니다. 계수 분할 연쇄는 그렇지 않습니다.
- drat-trim과 두 생성기는 신뢰 대상 코드입니다.

## FormalConjectures 원문

정확한 상위 Lean 명제는 로컬
[FormalConjectures 스냅숏](upstream/README.md)에 보존되어 있습니다. 이
명제는 전체 추측을 `sorry`로 진술하며, 여기의 유한 범위 탐색은 그 선언을
증명하지 않습니다. 비형식적으로 말하면 위의 `n <= 7` 결과는
`Chvatal.exists_maximal_star`를 `Fintype.card α <= 7`인 타입 `α`로 제한한
것입니다(`Decreasing`은 하향 닫힘 성질이고, `Intersecting`은 여기서와
마찬가지로 공집합도 배제합니다). 이 결과는 Lean으로 형식화되어 있지
않습니다.
