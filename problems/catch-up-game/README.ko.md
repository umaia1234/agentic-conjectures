[English](README.md) | **한국어**

# {1, …, N} 위의 Catch-Up: T_N이 짝수이면 언제나 무승부인가?

**상태: partial(부분 결과).** 추측은 미해결이다. 이 디렉터리에는 다음이 있다.

- `N ≤ 10`에 대한 명제의 Lean 증명;
- upstream 평가 함수 `valueAux`에 관한 Lean 보조정리들;
- 서로 독립적인 두 C++ 프로그램으로 계산한 모든 `N ≤ 28`에 대한
  Catch-Up({1, …, N})의 정확한 값. 특히 `N ≤ 28`에서 `T_N`이 짝수인 경우는
  모두 무승부다;
- 명제를 함의하는 더 강한 추측과 작은 경우에 대한 그 검사
  ([DETAILS.ko.md](DETAILS.ko.md)).

## 문제

Catch-Up은 A. Isaksen, M. Ismail, S. J. Brams, A. Nealen의 논문
*Catch-Up: A Game in Which the Lead Alternates*, Game & Puzzle Design 1(2),
38–49 (2015)에서 소개되었다
([MPRA 프리프린트 108784](https://mpra.ub.uni-muenchen.de/108784/)). 두 플레이어가
양의 정수의 유한집합 `S`에서 수를 가져가고, 가져간 수는 가져간 사람의 점수에
더해진다. upstream 형식화는 규칙을 다음과 같이 정한다.

- 첫 번째 플레이어는 수를 **정확히 하나** 가져가며 시작한다.
- 그 뒤로 플레이어는 자기 점수가 상대 점수 **이상**이 될 때까지 수를 하나씩
  가져가며, 차례의 마지막 수를 가져가기 전까지는 **엄격히 뒤져** 있어야 한다.
- 남은 수를 모두 가져가도 따라잡을 수 없는 플레이어는 **즉시 진다**.
- `S`가 바닥나면 점수가 높은 쪽이 이기고, 점수가 같으면 무승부다.

논문은 `T_N = N(N + 1)/2`가 짝수일 때, 즉 `N ≡ 0` 또는 `3 (mod 4)`일 때
`{1, …, N}` 위의 Catch-Up이 최적 플레이에서 무승부로 끝난다고 추측한다.

### upstream 명제

명제는 google-deepmind/formal-conjectures의
[`FormalConjectures/Paper/CatchUpConjecture.lean`](upstream/CatchUpConjecture.lean)에서
가져왔다(Apache-2.0, 출처 기록은 [upstream/README.md](upstream/README.md)).

> Let $T_N = \sum_{k=1}^{N} k = \frac{N(N+1)}{2}$.
> If $T_N$ is even (equivalently $N \equiv 0 \pmod 4$ or $N \equiv 3 \pmod 4$),
> then under optimal play the game `Catch-Up($\{1, \ldots, N\}$)` ends in a draw.

```lean
theorem value_of_even_mul_succ_self_div_two
    (N : ℕ) (h_even : Even (N * (N + 1) / 2)) :
    value (.Icc 1 N) = .draw := by
  sorry
```

## 결과

값은 최적 플레이에서 첫 번째 플레이어의 결과다(win 승리, draw 무승부, loss
패배).

| N | T_N | 값 | | N | T_N | 값 |
|---:|---:|:---|---|---:|---:|:---|
| 1 | 1 | win | | 15 | 120 | **draw** |
| 2 | 3 | win | | 16 | 136 | **draw** |
| 3 | 6 | **draw** | | 17 | 153 | win |
| 4 | 10 | **draw** | | 18 | 171 | loss |
| 5 | 15 | win | | 19 | 190 | **draw** |
| 6 | 21 | win | | 20 | 210 | **draw** |
| 7 | 28 | **draw** | | 21 | 231 | win |
| 8 | 36 | **draw** | | 22 | 253 | win |
| 9 | 45 | loss | | 23 | 276 | **draw** |
| 10 | 55 | loss | | 24 | 300 | **draw** |
| 11 | 66 | **draw** | | 25 | 325 | win |
| 12 | 78 | **draw** | | 26 | 351 | win |
| 13 | 91 | win | | 27 | 378 | **draw** |
| 14 | 105 | loss | | 28 | 406 | **draw** |

이 표의 근거는 세 가지다.

- **Lean(커널 검사):** `N ≤ 10`인 행. `statement_of_le_ten`이 짝수 경우
  `N = 0, 3, 4, 7, 8`을 다루고, `value_Icc_ne_draw`가 홀수 경우는 무승부가
  아님을 보인다.
- **컴퓨터 보조:** 모든 행을 [`catchup_turn.cpp`](catchup_turn.cpp)와
  [`catchup_pick.cpp`](catchup_pick.cpp)가 각각 계산했고 결과가 일치한다.
  따라서 두 프로그램과 컴파일러가 옳다는 전제 아래 추측은 모든 `N ≤ 28`에서
  성립한다.
- **OEIS:** `3 ≤ N ≤ 20`인 행은 이를 1 / 0 / −1로 부호화한
  [OEIS A278587](https://oeis.org/A278587)과 일치한다.

`T_N`이 홀수인 행에는 단순한 패턴이 보이지 않는다. `N = 22`는 첫 번째
플레이어의 승리이지만 `N = 14`와 `N = 18`은 두 번째 플레이어의 승리다.

## 선행 연구와 이 작업이 더하는 것

- 논문은 `N ≤ 20`에 대한 최적 플레이 결과를 보고한다. `N = 23, 24, 27, 28`에
  대해서는 몬테카를로 트리 탐색(MCTS) 실험도 보고하는데, 추측과 모순되는 결과는
  찾지 못했다.
- OEIS A278587은 `N = 3..20`의 값을 싣고 있으며 "more"(항 추가 요망) 표시가
  있다.
- formal-conjectures 파일은 추측을 `sorry`로 진술한다.
- arXiv에는 이 논문의 판본이 없다. OpenAlex에는 이 논문을 인용한 문헌이 7편
  있다(2026-10-24 확인). 제목으로 보면 게임 휴리스틱, 게임 메커니즘으로서의
  비복원 추출, 스포츠의 따라잡기 규칙, 인공지능의 게임이론적 모형을 다룬다.
  전문을 읽지는 않았다.

여기서 구한 `N = 21..28`의 정확한 값은 논문, A278587, formal-conjectures 파일에
실린 값을 넘어선다. 여기에는 논문이 MCTS로만 시험한 네 경우도 포함된다. 문헌
조사는 위 출처들로 한정했다. 이는 우선권이나 새로움에 대한 주장이 아니며,
OEIS나 upstream에는 아무것도 제출하지 않았다.

## 값을 계산하는 방법

모형과 모든 가지치기 규칙의 근거는 [DETAILS.ko.md](DETAILS.ko.md)에 있다.

- **[`catchup_turn.cpp`](catchup_turn.cpp)**는 차례 전체를 단위로 탐색한다. 격차
  `D ≥ 1`에서 한 차례는 `ΣA ≥ D`이고 `ΣA − max A < D`인 집합 `A`를 가져가고, 격차
  0에서는 수 하나를 가져간다. 이 프로그램은 각 국면에서 "둘 차례인 쪽이 적어도
  무승부를 확보할 수 있다"와 "둘 차례인 쪽이 승리를 강제할 수 있다"라는 두 불리언
  값을 결정한다. 해시 테이블과 DETAILS 3절의 절반합 컷오프를 쓴다.
- **[`catchup_pick.cpp`](catchup_pick.cpp)**는 `valueAux`를 한 수씩 따라간다.
  Lean 정리 `gapValue_eq`가 upstream 정의에서 유도한 격차 점화식을 쓴다. 차례
  단위 프로그램과 코드를 공유하지 않으며, 메모이제이션과 단락 평가 외에는
  가지치기가 없다.
- **[`valueaux_transliteration.py`](valueaux_transliteration.py)**는 `Outcome.best`의
  접기까지 포함하여 upstream `valueAux`를 그대로 옮긴 Python 코드다. 큰 `N`에는
  너무 느리며, 작은 입력에서 기준 역할을 한다.

[`verify_values.py`](verify_values.py)는 두 C++ 프로그램을 컴파일하고 다음 세
가지를 위 표와 대조한다.

- `N ≤ 22`에 대한 C++ 값;
- `N ≤ 12`에 대한 Python 값;
- `R ⊆ {1, …, 10}`, `D ≤ 10`인 국면 `(R, D)` 11,264개 전부에 대한 세 구현의
  비교.

`python3 verify_values.py --nmax 12 --positions 12`는 같은 세 구현 비교를
`R ⊆ {1, …, 12}`, `D ≤ 12`인 국면 53,248개 전부로 넓힌다. 이 명령은 7초 만에
통과하고 최대 메모리는 0.8 GB이며, CI에서도 실행된다.

### 재현

이 디렉터리에서 실행한다(단일 스레드; 시간은 Apple clang 21과 `-O3`를 쓴 Apple
silicon Mac에서 쟀다).

```bash
python3 verify_values.py
```

```bash
python3 verify_values.py --nmax 28
```

```bash
g++ -O3 -std=c++17 catchup_turn.cpp -o build_turn && ./build_turn 1 28 && rm -f build_turn
```

```bash
g++ -O3 -std=c++17 catchup_pick.cpp -o build_pick && ./build_pick 1 28 && rm -f build_pick
```

| 실행 | 시간 | 최대 메모리 | 로그 |
|---|---|---|---|
| `verify_values.py` (CI 기본값) | 25초 | 0.5 GB | — |
| `catchup_turn 1 28` | 1,282초 | 6.4 GB | [로그](logs/catchup_turn_1_28.log) |
| `catchup_pick 1 28` | 454초 | 15.0 GB | [로그](logs/catchup_pick_1_28.log) |

`verify_values.py --nmax 28`은 두 전체 계산을 모두 실행하므로 두 시간의 합과 더
큰 쪽의 메모리가 필요하다. `N`별 시간은 로그에 있으며, 가장 큰 경우는 다음과
같다.

| N | 차례 단위 | 한 수 단위 |
|---:|---:|---:|
| 25 | 136초 | 71초 |
| 26 | 277초 | 157초 |
| 27 | 246초 | 64초 |
| 28 | 568초 | 140초 |

다음으로 `T_N`이 짝수인 경우는 `N = 31`과 `N = 32`다. `N = 24`에서 `N = 28`까지
차례 단위 프로그램의 테이블은 약 14.5배, 실행 시간은 약 22배 늘었다. 이를
외삽하면 차례 단위 프로그램만으로도 `N = 31`에는 약 50 GB와 1.5시간, `N = 32`에는
약 100 GB와 3.5시간이 필요하다. 한 수 단위 교차 검증에는 100 GB를 훨씬 넘는
메모리가 필요하다. 공유 머신에서는 이 계산들을 시도하지 않았다.

## 증명을 향하여

[DETAILS.ko.md](DETAILS.ko.md) 5절은 추측을 **추측 L**로 환원한다. 중복집합
`R + {D}`가 완비이고 `ΣR − D`가 짝수이면 `(R, D)`에서 둘 차례인 쪽은 적어도 비길
수 있다는 명제다. L은 "합이 짝수인 모든 완비 중복집합 위의 Catch-Up은
무승부다"와 동치다. 두 범위에서 검사했다.

- 원소가 `12` 이하이고 원소 수가 9 이하인 중복집합 위의 국면 1,272,753개.
  [`generalization_check.py`](generalization_check.py)로 검사했다.
- `R ⊆ {1, …, 16}`인 집합 국면 442,699개 전부.
  [`closure_check.cpp`](closure_check.cpp)로 검사했다.

반례는 나오지 않았다. DETAILS 6절은 L의 가장 단순한 귀납적 증명들이 실패하는
이유를 기록한다. L의 국면 모임은 두 수 아래에서 닫혀 있지 않으며, "동점을 만들고
완비 집합을 남긴다", "가장 큰 수를 가져간다", "가장 작은 수를 가져간다" 가운데
어느 것도 비기는 전략이 아니다.

```bash
python3 generalization_check.py 12 9
```

```bash
g++ -O3 -std=c++17 closure_check.cpp -o build_closure && ./build_closure 1 16 && rm -f build_closure
```

첫 번째 명령은 약 8분(497초, 0.37 GB) 걸리고([로그](logs/generalization_check_12_9.log)), 두 번째
명령은 7초 걸린다([로그](logs/closure_check_1_16.log)).

## Lean 형식화

모듈: [`AgenticConjectures/CatchUpGame.lean`](../../AgenticConjectures/CatchUpGame.lean).

| 선언 | 내용 |
|---|---|
| `Player` … `valueAux`, `value` | upstream 정의를 그대로 복사함([`check_upstream_copy.py`](check_upstream_copy.py)로 검사) |
| `statement` | upstream의 미해결 정리를 `Prop`으로 옮긴 것 |
| `statement_of_le_ten` | `N ≤ 10`으로 제한한 `statement` |
| `value_Icc_three`, `_four`, `_seven`, `_eight` | `decide +kernel`로 보인 `N = 3, 4, 7, 8`의 무승부 |
| `valueList`, `valueAux_toFinset` | 연료 인자를 둔 계산 가능한 리스트 버전 `valueAux`와, 둘이 같다는 증명 |
| `valueAux_ne_draw`, `value_Icc_ne_draw` | 점수와 남은 수의 합이 홀수인 국면은 결코 무승부가 아님 |
| `statement_iff` | `statement ↔ ∀ N, value (Icc 1 N) = draw ↔ Even (N (N + 1) / 2)` |
| `valueAux_add`, `valueAux_eq_gapValue` | 점수 차만이 중요함 |
| `gapValue_eq`, `value_eq_gapValue`, `value_eq_gapValue_zero` | `catchup_pick.cpp`가 쓰는 격차 점화식; 새 게임은 격차 0인 국면 |
| `best_eq`, `best_congr` | `Outcome.best`는 `loss < draw < win` 순서의 최댓값 |

`decide`는 메모이제이션 없는 재귀를 커널 안에서 평가하므로 `N = 8`을 넘어서면
실용적이지 않다(DETAILS 7절). `native_decide`는 쓰지 않았다. 사용된 공리는
`propext`, `Classical.choice`, `Quot.sound`다.

### 명제의 충실성

- **정의.** `Player`, `Outcome`, `Outcome.neg`, `Outcome.best`, `valueAux`,
  `value`는 docstring과 주석까지 upstream 스냅숏과 바이트 단위로 같다. 모듈
  머리(FormalConjectures 유틸리티 대신 `import Mathlib`)와 이름공간만 다르다.
- **명제.** `statement`는 upstream의 변수, 가정, 결론을 그대로 유지한다.
  `N * (N + 1) / 2`는 나머지가 없는 자연수 나눗셈이다. `N = 0`도 포함되며, 이는
  `∅` 위의 자명한 무승부다.
- **규칙의 관례.** 게임에 대한 비형식적 설명과 달라질 수 있는 세 관례는 모두
  `valueAux`의 것을 따른다.
  - 첫수는 정확히 수 하나를 가져가는 것이다.
  - 따라잡을 수 없는 플레이어는 즉시 진다.
  - 점수가 상대 점수 이상이 되는 순간 차례가 끝난다.
- **탐색 프로그램.** 두 C++ 프로그램과 Python 전사본은 모두 이 관례를 구현한다.
  차례 모형은 DETAILS 1–2절에서 `valueAux`로부터 유도되며, 세 프로그램은 작은
  입력에서 국면마다 일치한다.
- **수.** upstream의 `Finset ℕ`는 `0`을 허용한다. 탐색 프로그램은 양수만
  가정하는데, `Icc 1 N`에는 양수만 들어 있다.

## 파일

| 파일 | 역할 |
|---|---|
| `catchup_turn.cpp` | 차례 단위 정확 탐색기(주 계산) |
| `catchup_pick.cpp` | 한 수 단위 정확 탐색기(독립 검사) |
| `valueaux_transliteration.py` | `valueAux`를 그대로 옮긴 Python 코드(작은 입력의 기준) |
| `verify_values.py` | 세 구현을 컴파일하고 교차 검사 |
| `check_upstream_copy.py` | Lean 정의가 upstream 스냅숏과 바이트 단위로 같은지 검사 |
| `generalization_check.py` | 추측 L과 완비 중복집합 |
| `closure_check.cpp` | 집합 국면에서의 추측 L; 실패한 귀납 시도의 통계 |
| `logs/` | 전체 실행의 출력, 시간, 메모리 |
| `DETAILS.md` | 모형과 가지치기 규칙의 증명; 추측 L; 실패한 시도 |
| `upstream/` | formal-conjectures 스냅숏과 출처 |

## 주장하지 않는 것

- 모든 `N`에 대한 추측의 증명은 없으며, `N > 28`에 대해서는 아무것도 주장하지
  않는다.
- `11 ≤ N ≤ 28`의 값은 Lean으로 검사되지 않았다. 이 값들은 서로 독립적인 두 C++
  프로그램에 근거한다. 두 프로그램은 서로 일치하고, 작은 입력에서는 upstream
  정의를 그대로 옮긴 코드와도 일치한다.
- 추측 L은 추측이다. DETAILS 5–6절의 탐색은 증거이지 증명이 아니다.
- 새로움이나 우선권을 주장하지 않는다.
