[English](README.md) | **한국어**

# 덧셈형 싱크 빼기 게임: 싱크–벽 쌍대성

이 추측은 Anjali Bhagat, Urban Larsson, Hikaru Manabe, Takahiro Yamashita의
것으로, *Additive Sink Subtraction*
([arXiv:2601.18715v3](https://arxiv.org/abs/2601.18715v3))에서 따름정리 4
바로 뒤에 나오는 식 (3)입니다. 이 항목은 모든 덧셈형 빼기 집합에 대해 이
추측을 Lean 4로 증명합니다. 새로운 결과라고 주장하지 않습니다. 2026-10-25의
검색에서는 앞선 증명을 찾지 못했지만, 이 증명을 검토한 사람은 아직 없으며
저자들에게 알리거나 어디에 제출한 것도 없습니다.

## 게임

정수 $1\le s_1<s_2$를 고정하고 $S=\{s_1,s_2,s_1+s_2\}$라 합시다. 한 수는
위치에서 $S$의 원소 하나를 빼는 것이고, 둘 수 있는 수가 없는 사람이 집니다.
논문은 두 가지 규칙을 비교합니다.

- **벽 빼기**(wall subtraction)는 고전적인 게임입니다. 위치는 정수
  $x\ge0$이고, 어떤 수도 $0$ 아래로 내려갈 수 없습니다.
- **싱크 빼기**(sink subtraction)에서는 모든 $y\le0$이 종료 위치(싱크)이고,
  $y\ge1$에서는 $s\in S$에 대한 모든 수 $y-s$가 허용되며 싱크로 들어가는 수도
  허용됩니다. 따라서 싱크로 들어가는 사람이 이깁니다.

님 값은 mex 규칙을 따릅니다.

$$v_{\rm wall}(x)=\operatorname{mex}\{v_{\rm wall}(x-s): s\in S,\ s\le x\},$$

$$v_{\rm sink}(y)=0\ \text{ for } y\le0,\qquad v_{\rm sink}(y)=\operatorname{mex}\{v_{\rm sink}(y-s): s\in S\}\ \text{ for } y\ge1.$$

$m=s_1$, $\delta=s_2-s_1$, $d=\delta\bmod 2m$으로 두고, $d\le m$이면
$p=3m+2\delta-d$, 그렇지 않으면 $p=m(m+2\delta+d)/\gcd(m,d)$라 합시다. 논문의
정리 3은 싱크 님 수열이 주기 길이 $p$로 순수 주기적임을 증명하고, 따름정리
4는 이 주기 길이를 벽 게임의 결과(outcome)로 옮깁니다.

## 추측

**논문의 식 (3)** (의역). 모든 $x$에 대해

$$v_{\rm wall}([x]_p)=\sigma\bigl(v_{\rm sink}([-s_2-x]_p)\bigr)$$

입니다. 여기서 $[x]_p$는 $x$를 $p$로 나눈 음이 아닌 최소 나머지이고,
$\sigma$는 값 $0$과 $2$를 맞바꾸며 $1$과 $3$은 그대로 둡니다.

예를 들어 $S=\{2,5,7\}$의 주기 길이는 $p=22$입니다(논문의 예 5).
$x=0,1,\dots,21$에 대해 다음과 같습니다.

| 수열 | 값 |
| --- | --- |
| $v_{\rm wall}(x)$ | `0 0 1 1 0 2 1 3 2 2 0 3 1 0 0 1 1 2 2 3 3 2` |
| $[-5-x]_{22}$ | `17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 0 21 20 19 18` |
| $v_{\rm sink}([-5-x]_{22})$ | `2 2 1 1 2 0 1 3 0 0 2 3 1 2 2 1 1 0 0 3 3 0` |

마지막 행에 $\sigma$를 적용하면 첫 행이 됩니다.

## 결과

**정리 (Lean).** 식 (3)은 모든 쌍 $1\le s_1<s_2$와 모든 정수 $x$에 대해
성립합니다(`statement_holds`).

그 과정에서 Lean 파일들은 $\gcd(s_1,s_2)$에 대한 조건 없이 모든 쌍에 대해
다음을 증명합니다. 벽 값의 분류 (T1), 싱크 값의 분류 (T2), $p$가 두 님
수열의 주기라는 사실, 벽 $\mathcal P$-위치의 반사 대칭 (T3), 그리고 벽
$\mathcal P$-위치의 명시적 기술입니다. 이 기술이 고전적인 괄호 공식이라는
것은 DETAILS.ko.md 4절에서 Lean 밖에서 설명합니다.

## 증명 개요

$P$를 벽 $\mathcal P$-위치(값 $0$)의 집합, $c=s_1+s_2$라 합시다.

1. **(T1) 벽 값의 분류.** $v_{\rm wall}(x)$는 $x\in P$, $x-s_1\in P$,
   $x+s_2\in P$, 셋 다 아님에 따라 각각 $0$, $1$, $2$, $3$입니다.
2. **(T2) 싱크 값의 분류.** $v_{\rm sink}(t+1)$은 $t-c\in P$, $t\in P$,
   $t-s_1\in P$, 셋 다 아님에 따라 각각 $0$, $1$, $2$, $3$입니다. (T1)과
   (T2)는 mex 규칙과, $P$의 어떤 두 원소도 한 수만큼 차이 나지 않는다는
   사실로부터 귀납법으로 나옵니다.
3. **(간격).** $P$의 어떤 원소도 $[p-c,p)$에 있지 않습니다. $p$의 값이
   쓰이는 곳은 여기뿐입니다. 이는 괄호 공식에서 나옵니다. $P$의 $n$번째
   원소는 $n+s_1\lfloor n/s_1\rfloor+s_2\lfloor n/N\rfloor$이고, 여기서
   $N=s_1\lfloor s_2/2s_1\rfloor+\min(s_1,\ s_2\bmod 2s_1)$입니다. 우리는
   이와 동치인 $P$의 기술을 모든 쌍에 대해 증명하고, 항등식
   $p=2\operatorname{lcm}(s_1,N)+(s_1/\gcd(s_1,N))\,s_2$도 증명합니다. 둘을
   합치면 $[p-c,p)$에는 $P$의 원소가 남지 않습니다.
4. **(T3)과 주기성.** (간격)이 성립하면 $P$는 $p$-주기적이고,
   $P\cap[0,p-c-1]$은 $x\mapsto p-c-1-x$에 대해 대칭입니다. 따라서 $p$를
   법으로 하여 $P$는 $X\mapsto-X-c-1$에 대해 불변입니다.
5. **조립.** $y=-s_2-x$로 두면, 이 반사는 $y$에서의 (T2)의 세 조건을
   $x$에서의 (T1)의 세 조건으로 바꾸고, 그때 분류 $0$과 $2$가 서로 바뀝니다.
   이것이 바로 식 (3)입니다.

[DETAILS.ko.md](DETAILS.ko.md)에 각 단계의 Lean 이름과 함께 완전한 증명이
있습니다.

## Lean 형식 증명

모듈
[`AgenticConjectures/AdditiveSinkWallDuality.lean`](../../AgenticConjectures/AdditiveSinkWallDuality.lean)이
추측을 진술하고 `statement_holds : statement`를 증명합니다. 이 모듈은 다음
세 파일 위에 세워져 있습니다.

- [`Games.lean`](../../AgenticConjectures/AdditiveSinkWallDuality/Games.lean):
  mex 재귀로 정의한 두 게임, 주기 공식, $\sigma$
- [`Classes.lean`](../../AgenticConjectures/AdditiveSinkWallDuality/Classes.lean):
  mex 재귀만으로 얻는 (T1), (T2), 주기성, (T3), $p$를 법으로 한 조립
- [`Explicit.lean`](../../AgenticConjectures/AdditiveSinkWallDuality/Explicit.lean):
  $P$의 명시적 기술과, 논문의 $p$에 대한 (간격)

`sorry`, 추가 공리, `native_decide`, `decide +native`, `ofReduceBool`,
`ofReduceNat`은 쓰지 않습니다. 아래 정리들에 대해 `#print axioms`는
`propext`, `Classical.choice`, `Quot.sound`만 보여 줍니다. `lake env lean`으로
하나씩 컴파일하면 네 파일에 모두 합쳐 약 20초가 걸립니다(Mathlib 불러오기를
포함해 각각 4, 5, 7, 4초).

| 선언 | 내용 |
| --- | --- |
| `wall`, `sink`, `period`, `sigma` | 두 게임, 정리 3의 주기 길이, $\sigma$ |
| `wall_eq_iff`, `sink_eq_iff` | mex 재귀를 다시 쓴 것 |
| `statement`, `statement_holds` | 모든 $1\le s_1<s_2$와 $x\in\mathbb Z$에 대한 식 (3)과 그 증명 |
| `wall_eq_wallClass` | (T1) 벽 값의 분류 |
| `sink_eq_sinkClass` | (T2) 싱크 값의 분류 |
| `wall_periodic`, `sink_periodic` | $p$는 벽 님 수열($0$부터)과 싱크 님 수열($1$부터)의 주기 |
| `wall_zero_reflect_period` | (T3) $P\cap[0,p-c-1]$은 $x\mapsto p-c-1-x$에 대해 대칭 |
| `wall_ne_zero_of_gap` | (간격) $[p-c,p)$에는 벽 $\mathcal P$-위치가 없음 |
| `sink_period_eq_zero` | $v_{\rm sink}(p)=0$이므로 나머지 $0$의 대표로 어느 쪽을 써도 됨 |
| `conj_of_gap` | (간격)을 만족하는 임의의 $p>c$에 대한 식 (3) |
| `W`, `wall_zero_iff_W` | 모든 쌍에 대한 $P$의 괄호 기술 |
| `W_indep`, `W_cover`, `W_neg_gap`, `W_top_gap`, `period_gt` | 증명에 쓰는 명시적 집합의 성질 |
| `Explicit.period_spec` | 정리 3의 공식을 $s_1\ell=kN$, $\ell,k\ge1$인 $p=2s_1\ell+ks_2$ 꼴로 쓴 것 |

## 명제의 충실성

Formal Conjectures에는 이 추측의 명제가 없으므로 명제는 우리가 만든
것입니다. 그 선택은 모듈 docstring과
[DETAILS.ko.md](DETAILS.ko.md#6-명제의-충실성)에도 적혀 있습니다.

- 두 게임은 어떤 공식도 거치지 않고 mex 재귀로 직접 정의합니다. 모든 쌍에
  대해 재귀가 끝나도록 크기 $0$인 수는 건너뛰는데, $1\le s_1<s_2$이면 그런
  수는 없습니다.
- `period`는 정리 3의 공식이며, 논문은 이것이 주기 길이임을 증명합니다.
  우리는 이것이 두 님 수열의 주기임을 증명하지만 최소 주기임은 증명하지
  않습니다. 아래 검사기는 $s_2\le200$인 모든 경우에 이것이 최소 주기임을
  확인합니다.
- $x$는 $\mathbb Z$ 전체를 움직입니다. 양변은 $x\bmod p$에만 의존합니다.
- $[x]_p$는 음이 아닌 최소 나머지인 `x % p`입니다. 싱크 쪽에서 나머지 $0$은
  싱크 위치 $0$입니다. 논문의 예 5의 표는 대신 위치 $p$를 쓰는데, 그 값도
  $0$입니다.
- $\gcd(s_1,s_2)$나 영역(regime)에 대한 조건이 없고, $s_1=1$도 포함합니다.

## 계산 교차 검증

인증서는 Lean 증명입니다. 코드를 공유하지 않는 두 Python 스크립트가 표준
라이브러리만으로 정의로부터 사실들을 다시 계산합니다.
[`check_duality.py`](check_duality.py)는 식 (3), 주기와 그 최소성을 검사하고,
[`check_translates.py`](check_translates.py)는 (T1), (T2), (T3), (간격),
괄호 공식을 검사합니다. 인자는 $s_2$의 최댓값입니다.

```
python3 check_duality.py 100      # 4,950개 집합, 약 3초 (CI)
python3 check_translates.py 100   # 4,950개 집합, 약 7초 (CI)
python3 check_duality.py 200      # 19,900개 집합, 약 40초
```

세 실행 모두 실패 0건을 보고합니다.

## 선행 연구와 기여

- 추측과 주기 공식은 Bhagat, Larsson, Manabe, Yamashita의 것입니다
  ([arXiv:2601.18715v3](https://arxiv.org/abs/2601.18715v3)).
- 벽 쪽은 이미 알려져 있습니다. Manabe의 정리 `thm:additive`와 따름정리 46
  ([arXiv:2609.05358v2](https://arxiv.org/abs/2609.05358v2))은 $s_1\ge2$인
  서로소 쌍에 대해 벽 $\mathcal P$-위치, 최소 주기, 벽 값의 분류를 주며, 그
  논문에는 이들의 Lean 형식화가 함께 실려 있습니다. 우리는 이것을 참고로만
  썼고 그 코드는 전혀 복사하지 않았습니다. Larsson과 Manabe
  ([arXiv:2603.10414v2](https://arxiv.org/abs/2603.10414v2))는 원시 이차
  영역에서 벽 님 값을 결정합니다. 괄호 공식은 고전적인 결과입니다
  (*Winning Ways*; Flammenkamp).
- 이 프로젝트의 앞선 정찰 실행이 (T1), (T2), (T3)를 거치는 경로를 찾고
  수치로 확인했습니다.
- [DETAILS.ko.md](DETAILS.ko.md#8-논문-맺음말의-실수)에 논문 맺음말의 부호
  실수 세 곳과 값이 1씩 작은 표의 두 행을 기록했습니다. 어느 것도 식 (3)에는
  영향을 주지 않습니다.

이 증명을 검토한 사람은 아직 없습니다. 저자들에게 알리거나 MathDB,
OpenConjecture, Formal Conjectures 등 어디에도 제출한 것이 없습니다.
