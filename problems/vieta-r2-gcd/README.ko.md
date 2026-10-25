[English](README.md) | **한국어**

# $r=2$인 Vieta jumping: $2(a+b)/\gcd(a,b)^2$의 값

이 페이지의 문제와 추측은 Steven J. Miller, Dimitrios Nikolakopoulos, Anitha
Srinivasan의 것입니다. 세 저자는 논문 *Fibonacci Numbers and Vieta Jumping for
a Rational Diophantine Equation*
([arXiv:2605.19083v2](https://arxiv.org/abs/2605.19083v2))의 §4.1에서 이
추측을 Conjecture 4.2로 제시합니다. 이 항목은 그 추측을 Lean 4로 증명합니다.
어느 단계가 논문의 것이고 어느 단계를 이 항목이 더했는지는 수학적 상세 문서의
[출처와 기여](DETAILS.ko.md#출처와-기여) 절에 정리되어 있습니다.

## 추측

논문은 다음 식의 양의 정수해 $(a,b)$를 연구합니다.

\[
\frac{a+r}{b}+\frac{b+r}{a}=k,\qquad k\in\mathbb Z .
\]

$r=1$일 때 논문은 $k=3$과 $k=4$만 나타나며, 모든 해가 $(2,2)$($k=3$) 또는
$(1,1)$($k=4$)에서 Vieta jump로 얻어지고 $k=3$의 해는 피보나치 수로 주어짐을
보이고(Theorem 1.1), $(a+b)/\gcd(a,b)^2$가 $1,2,3,5$만 값으로 가짐을
증명합니다(Theorem 1.2). $r=2$에 대해서는 Remark 4.1에서 같은 강하
논증(descent)으로 대각선까지 내려가 $k\in\{3,4,6\}$을 얻고, $r\ge3$에서는 이
강하 논증이 통하지 않는다고 지적합니다.

Conjecture 4.2를 우리 말로 옮기면 다음과 같습니다. $r=2$인 모든 해에 대해

\[
\frac{2(a+b)}{\gcd(a,b)^2}\in\{1,2,3,4,5,8\}
\]

이고, 실제로 나타나는 값은 $k=3$이면 정확히 $1,5$, $k=4$이면 정확히 $2,3$,
$k=6$이면 정확히 $4,8$입니다.

## 결과

`AgenticConjectures.VietaR2Gcd.statement_holds`는 Conjecture 4.2의 형식적
판본인 `AgenticConjectures.VietaR2Gcd.statement`를
[`VietaR2Gcd.lean`](../../AgenticConjectures/VietaR2Gcd.lean)에서 `sorry`, 추가
공리, `native_decide` 없이 증명합니다. 증명은 네 단계로 이루어지며, 전체
내용은 [수학적 상세 문서](DETAILS.ko.md)에 있습니다.

1. 논문의 강하 논증(Remark 4.1)으로 $k\in\{3,4,6\}$을 얻습니다.
2. $g=\gcd(a,b)$, $a=gx$, $b=gy$로 두면 값 $m=2(a+b)/g^2$는
   $kxy-x^2-y^2$와 같고, $m$은 $2(k+2)$를 나눕니다.
3. 항등식 $(x+y)^2+m=(k+2)xy$를 $3,4,5,8,9,16$ 또는 $25$를 법으로 보면 나머지
   약수는 모두 배제됩니다.
4. 순서쌍 $(4,4),(4,6),(2,2),(2,4),(1,1),(1,3)$이 여섯 값을 줍니다.

같은 모듈은 모든 $r>0$에 대해서도(이름공간 `GeneralR`) 다음을 증명합니다.
$3\le k\le2r+2$이고 양 끝값이 모두 나타난다는 것, 모든 해가 유한 개뿐인
*기약해(reduced solution)* 로 내려간다는 것, 값 $r(a+b)/\gcd(a,b)^2$가 각
Vieta 사슬을 따라 주기 2로 반복된다는 것, 그리고 이로부터 얻는 $r=1,2,3$의
값 집합 전체입니다. $r=2$에서는 이것이 합동식을 쓰지 않는 값 집합의 두 번째
증명이 됩니다. $r=11$에서는 $k=3$의 값에 $11$이 포함되므로 "$k=3$이면 $1$과
$5$"라는 패턴은 모든 $r$에서 유지되지는 않습니다.

## Lean 선언

모든 이름은 이름공간 `AgenticConjectures.VietaR2Gcd` 안에 있습니다.

| 선언 | 내용 |
|---|---|
| `statement`, `statement_holds` | Conjecture 4.2와 그 증명 |
| `IsSolution.sol` | $\mathbb Q$ 위의 식에서 분모를 없애면 $a^2+2a+b^2+2b=kab$ |
| `k_cases` | $r=2$이면 $k\in\{3,4,6\}$ (논문의 Remark 4.1) |
| `key` | 서로소인 $x,y$와 임의의 $r$에 대해 $g\,m=r(x+y)$이고 $m\mid r(k+2)$ |
| `normSum_cases` | $r=2$인 모든 해에서 $(k,m)$은 허용된 여섯 쌍 중 하나 |
| `GeneralR.k_range`, `GeneralR.k_range_sharp` | $3\le k\le 2r+2$이고, $(1,1)$과 $(2r,2r)$가 양 끝값을 가짐 |
| `GeneralR.descent`, `GeneralR.reduced_bounds` | 모든 해는 기약해로 내려가고, 기약해는 $2(b-a)\le r$, $a\le 2r$를 만족 |
| `GeneralR.thm12` | 논문의 Theorem 1.2($r=1$)의 서로소 형태 |
| `GeneralR.two_periodic` | Vieta 단계를 두 번 거쳐도 값 $r(a+b)/\gcd(a,b)^2$는 그대로 |
| `GeneralR.values_eq` | 주어진 $k$의 값은 기약해와 그 이웃의 값 |
| `GeneralR.values_one`, `GeneralR.values_two`, `GeneralR.values_three` | $r=1,2,3$의 값 집합 |
| `GeneralR.eleven_three` | $r=11$, $(a,b)=(21,28)$: $k=3$이고 값은 $11$ |

`status.yaml`에는 모듈의 모든 공개 정리가 등록되어 있으므로 공리 감사가 이들
모두를 다룹니다.

## 명제의 충실성

이 추측에 대한 Formal Conjectures 파일은 없으므로 Lean 명제는 우리가 직접
작성했습니다. 명제는 다음 해석을 명시합니다.

- $k$는 논문 §1의 설정대로 정수입니다. $k$를 유리수로 허용하면 주장은
  거짓입니다. $(a,b)=(1,2)$는 $k=11/2$과 값 $6$을 줍니다.
- $a$와 $b$는 양의 자연수입니다. 두 분수와 $2(a+b)/\gcd(a,b)^2$는
  $\mathbb Q$에서 `Nat.gcd`로 계산합니다.
- "$k=3$이면 값은 $1$과 $5$"를 집합의 등식으로 읽습니다. 즉 $k=3$인 모든 해에
  걸친 값이 정확히 $1$과 $5$입니다. 이렇게 읽으면 포함과 실현이라는 두 해석이
  모두 포함됩니다. $k=4$와 $k=6$도 마찬가지입니다.

`statement`는 모든 정수 $k$에 대한 소속 주장과 세 집합 등식의 논리곱입니다.
모듈 docstring에도 같은 해석이 적혀 있습니다.

## 계산 (보조 증거일 뿐)

Lean 증명은 어떤 계산도 사용하지 않습니다. Lean 증명과도, 서로와도 따로
작성한 두 프로그램이 같은 사실을 수치적으로 확인합니다.

- [`programs/vieta_brute.c`](programs/vieta_brute.c)는 $1\le a\le b\le N$인
  모든 쌍을 직접 검사합니다. $r=2$에서는 각 해의 $(k,m)$이 허용된 쌍인지,
  여섯 값이 모두 나타나는지 확인합니다.
- [`programs/vieta_chains.py`](programs/vieta_chains.py)는 $r=2$의 Vieta
  사슬을 $10^{200}$까지 따라갑니다. 또 각 $r\le R$에 대해 기약해의 범위,
  나눗셈 관계 $m\mid r(k+2)$, 주기 2 패턴을 확인하고, 사슬을 약수에 대한
  별도의 열거($b\mid a(a+r)$)와 비교합니다.

이 디렉터리에서 실행합니다.

```bash
mkdir -p build && cc -O2 -std=c99 -Wall -Wextra -o build/vieta_brute programs/vieta_brute.c && build/vieta_brute 60000
build/vieta_brute 20000 3
build/vieta_brute 20000 11
python3 programs/vieta_chains.py --height 200 --max-r 40 --brute 20000
```

2026-10-25에 Apple silicon Mac에서 각각 1.05초(컴파일 포함), 0.11초,
0.11초, 4.92초가 걸렸고, 출력은 [`logs/`](logs/)에 있습니다. $r=2$ 열거는
$a\le b\le 60000$인 해 28개를 찾습니다. `status.yaml`의 CI 항목은 첫
번째와 마지막 명령을 다시 실행합니다. Lean 증명을 다시 빌드하려면 다음을
실행합니다.

```bash
lake build AgenticConjectures.VietaR2Gcd
```

## 상태와 출처

추측은 Lean으로 증명되었습니다. 증명과 이 글은 어떤 사람도 검토하지 않았고,
저자들에게 알리거나 어디에 제출한 것도 없습니다. 새로움은 주장하지 않습니다. 강하 논증과
$k\in\{3,4,6\}$으로의 환원은 논문의 것이고, 나머지 단계는 표준적인 Vieta
jumping 논증과 합동식 논증을 사용합니다. 전체 구분은
[출처와 기여](DETAILS.ko.md#출처와-기여) 절에 있습니다.

## 확인한 자료

2026-10-25(약 15:10 UTC)에 확인했습니다.

- arXiv: [2605.19083](https://arxiv.org/abs/2605.19083)의 최신 판은
  v2(2026-05-27)입니다. arXiv에서 "Vieta jumping"을 검색하면 이 논문과
  F. Lemmermeyer, *Vieta jumping and small norms in quadratic number fields*
  ([arXiv:2601.15229](https://arxiv.org/abs/2601.15229))만 나오며, 후자는 이
  논문이 관련 연구로 인용합니다.
- OpenAlex에는 이 논문(work W7161841799)을 인용하는 문헌이 없습니다. Vieta
  jumping에 관한 2026년 기록은 $r=1$ 식에 관한 것이거나 관련이 없습니다.
- Formal Conjectures: 이 논문, 그 제목 또는 Vieta jumping을 언급하는 issue나
  pull request가 없습니다.
- GitHub 코드 및 저장소 검색, Zenodo, MathDB: $r=2$나 이 추측에 관한 결과가
  없습니다.
- OpenConjecture 데이터셋(마지막 갱신 2026-09-25)은 이 추측을 2765번 항목으로
  싣고 미해결로 표시합니다.
