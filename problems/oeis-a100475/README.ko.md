[English](README.md) | **한국어**

# OEIS A100475 — 어떤 시작값도 고리에 빠지지 않는다

## 결론

upstream 추측을 **반박했다**. $p_k$를 $k$번째 소수($p_1=2$),
$\operatorname{rev}$를 십진 자릿수를 뒤집는 연산이라 하자. 모든 시작값
$x\ge1$에 대해 궤도

\[
x,\ f(x),\ f(f(x)),\ \ldots \qquad f(k)=\operatorname{rev}(p_k)
\]

는 결국 주기적(ultimately periodic)이 되지 않는다. 특히 $1$이 아닌 어떤
시작값도 "고리에 빠지지" 않는다. OEIS 수열 자체에 해당하는 시작값 $x=1$도
마찬가지로 고리에 빠지지 않는다.

반박 전체가 Lean 4 증명이며 `sorry`, 추가 공리, `native_decide` 없이
검사된다. 유한한 부분(소수 개수 세기와 $1230$ 미만의 탐색)은
`decide +kernel`을 이용한 커널 계산이다. 이 디렉터리의 Python 스크립트는
같은 수치를 독립적으로 다시 계산할 뿐이며, 증명은 이 스크립트에 의존하지
않는다.

## 원문 명제와 선행 결과

2026-10-24에 확인한 [OEIS A100475](https://oeis.org/A100475)(개정 #21,
2025년 2월 16일)는 "Prime-th recurrence with reversal at each step"이며,
$a(0)=1$, $a(n)=\operatorname{reversal}(p_{a(n-1)})$로 정의된다. 주석은
다음과 같이 묻는다.

> “Starting at other than a(n) = 1, does this sequence ever go into a loop?”

Formal Conjectures 파일
[`FormalConjectures/OEIS/100475.lean`](upstream/100475.lean)
([upstream/README.md](upstream/README.md) 참고)은 "그렇다"는 답을 미해결
추측으로 진술한다.

```lean
theorem conjecture :
    ∃ x : ℕ, 0 < x ∧ x ≠ 1 ∧ IsUltimatelyPeriodic (aStartAt x)
```

OEIS 항목은 답을 제시하지 않으며 여전히 키워드 `more`가 붙어 있다. 이 질문은
OEIS Open 목록에도 없다. 항목은 Rosser 정리 $p_n>n\ln n$에 관한 MathWorld
페이지를 링크하는데, 이 정리만으로도 큰 수에서는 자릿수가 늘어날 수밖에
없다. 아래 논증은 초등적이어서 이미 알려져 있을 가능성이 크며, 새로움을
주장하지 않는다. 외부 제출에는 사람의 승인이 필요하므로 이 결과는 OEIS에
보고하지 않았다.

## 증명

$L(n)$을 $n$의 십진 자릿수 개수라 하자.

1. **자릿수는 줄어들지 않는다.** 어떤 소수도 $10$으로 나누어떨어지지
   않으므로 $\operatorname{rev}(p)$의 자릿수는 $p$와 같다. 또한
   $p_k\ge k+1$이다. 따라서 $L(f(k))=L(p_k)\ge L(k)$이다. $x\ge1$에서
   시작한 궤도는 $0$에 도달하지 않으므로, 궤도를 따라 $L$은 감소하지
   않는다.
2. **고리는 한 자릿수 구간 안에 있다.** $P>0$이고 모든 $n\ge N$에 대해
   $a_{n+P}=a_n$이면, $n\ge N$일 때
   $L(a_N)\le L(a_n)\le L(a_{N+nP})=L(a_N)$이다. 이 공통 길이를 $d$라 하자.
3. **개수 세기.** $n\ge N$에 대해 $k=a_n$으로 두면 $10^{d-1}\le k$이고
   $L(p_k)=L(a_{n+1})=d$이다. 따라서 $p_1<\dots<p_k<10^d$이므로
   $\pi(10^d)\ge k\ge10^{d-1}$이다.
4. **$d\ge5$이면 불가능하다.** $\pi(10^d)<10^{d-1}$이기 때문이다.
   - $d=5$: 정확한 계산으로 $\pi(100112)=9600$이므로
     $\pi(10^5)\le9600<10^4$이다.
   - $d=6$: $(m,2m]$의 소수들은 $\binom{2m}{m}\le4^m$을 나누므로,
     $(m+1)^{K+1}>4^m$이면 그런 소수는 많아야 $K$개이다. $m=500000$,
     $K=52821$과 정확한 값 $\pi(509712)=42269$로부터
     $\pi(10^6)\le42269+52821=95090<10^5$를 얻는다.
   - $d=7$: 같은 꼴의 구간 네 개, 곧 $m=625000,1250000,2500000,5000000$과
     $K=64923,123435,235255,449367$로부터 $\pi(10^7)\le968070<10^6$을
     얻는다.
   - $d\ge8$, 귀납법: $[10^{d-1},10^d)$의 소수들의 곱은
     $\operatorname{primorial}(10^d)\le4^{10^d}$ 이하이고, 각 소수는
     $10^{d-1}$ 이상이다. 그런 소수가 $9\cdot10^{d-2}$개 이상이면
     $10^{9(d-1)}\le4^{100}<10^{63}$이 되어 모순이다. 따라서
     $\pi(10^d)<10^{d-2}+9\cdot10^{d-2}=10^{d-1}$이다.
5. **$d\le4$인 경우는 유한하다.** $n\ge N$이면 $p_{a_n}<10^d\le10^4$이므로
   $a_n\le\pi(10^4)=1229$이다. 따라서 꼬리는 $1229$ 이하의 $d$자리 수들로
   이루어진 구간 안에 머문다. 커널 계산으로, 그런 모든 $k$에서 $f$를
   반복하면 이 구간을 벗어남을 확인한다. (실제로는 많아야 네 번이면
   충분하며, Lean 검사는 $1230$번까지 허용한다.) 이는 2단계와 모순이다.

**수집 단계 triage의 수정 사항.** triage의 논증은 옳지만 두 가지 세부
사항이 바뀐다. 첫째, $d\le4$인 경우에는 $p_{9999}$까지가 아니라 $10^4$
미만의 소수만 있으면 된다. 네 자리 이하인 꼬리 값은 $\pi(10^4)=1229$
이하이기 때문이다. triage가 $20000$ 미만의 시작값만 탐색해도 충분했던
이유도 이것이다. 둘째, Rosser–Schoenfeld 추정은 필요 없다. $d=5,6,7$은
정확한 개수와 중심 이항계수 구간으로, $d\ge8$은
$\operatorname{primorial}(n)\le4^n$으로 처리된다.

## Lean 형식화

[`AgenticConjectures/OeisA100475.lean`](../../AgenticConjectures/OeisA100475.lean)
(이름공간 `AgenticConjectures.OeisA100475`):

| 선언 | 내용 |
| --- | --- |
| `not_statement` | `¬ statement`, 곧 upstream `conjecture`의 부정 |
| `not_isUltimatelyPeriodic` | `0 < x → ¬ IsUltimatelyPeriodic (aStartAt x)` |
| `length_digits_reverseDigits` | `p % 10 ≠ 0`이면 뒤집어도 자릿수가 같다 |
| `count_prime_pow_ten_lt` | `5 ≤ d → Nat.count Nat.Prime (10 ^ d) < 10 ^ (d - 1)` |
| `count_dyadic_le`, `count_step` | 이진 구간 상계와 `d ≥ 8`의 귀납 단계 |
| `prime_iff_gcd_factorial` | `B < n < (B + 1) ^ 2 → (n.Prime ↔ Nat.gcd n B ! = 1)` |
| `count_prime_10000` | `Nat.count Nat.Prime 10000 = 1229` (표의 커널 검사) |
| `cnt_A`, `cnt_B`, `cnt_C` | 세 구간의 소수 개수 7649, 722, 32669의 커널 계산 |
| `escape_check` | 커널 검사: 모든 `k ≤ 1229`에서 `d ≤ 4` 구간을 벗어난다 |

커널 계산은 `Decidable` 인스턴스를 피하고 `Nat.gcd`, `Nat.pow`,
`Nat.ble`, `Nat.rec`을 직접 쓴다. 각 계산은 증명된 보조정리
(`isPrimeB_iff`, `cntCop_eq`, `nth_prime_eq_table`, `step_eq_G`,
`escapes_spec`)로 `Nat.Prime`과 `Nat.nth`에 연결된다. 두 주정리에 대한
`#print axioms`는 `propext`, `Classical.choice`, `Quot.sound`만 출력한다.

## 명제 충실성

- `reverseDigits`, `a`, `aStartAt`, `IsUltimatelyPeriodic`은 upstream
  파일에서 항 그대로 복사했고, `statement`는 upstream `conjecture`의
  본문이다. `module` 머리말, `FormalConjecturesUtil` import,
  `@[expose] public section`, 분류 속성만 제거했다. upstream 보조정리
  `a_succ`, `a_0`–`a_4`, `aStartAt_zero`, `conjecture_with_zero`는 다시
  싣지 않았다.
- 첨자 기준: `Nat.nth Nat.Prime 0 = 2`이므로 $k\ge1$에서
  `Nat.nth Nat.Prime (k - 1)`은 OEIS의 $p_k$이다. 이는 OEIS 예시
  $a(6)=13$, $p_{13}=41$, $a(7)=14$와 일치한다.
- ℕ 뺄셈: `k - 1`은 `k ≠ 0`일 때만 계산되므로 잘림이 일어나지 않는다.
- 경계값: upstream은 `0 < x`로 `x = 0`(궤도가 상수 `0`이며 upstream의
  `conjecture_with_zero` 참고)을 제외하고 `x = 1`도 제외한다. 우리의 더
  강한 정리는 `x = 1`도 포함한다.
- `reverseDigits`는 OEIS 프로그램(`FromDigits[Reverse[IntegerDigits[...]]]`)
  처럼 끝자리 0을 버린다. 소수는 끝자리가 0이 아니므로 여기서는 이 선택이
  영향을 주지 않는다.
- 점화식 $a_{n+1}=f(a_n)$에서 "고리에 빠진다"(어떤 값이 다시 나온다)는
  것은 결국 주기적이라는 것과 같다. 따라서 `IsUltimatelyPeriodic`은 OEIS
  질문을 올바르게 옮긴 것이다.

## 기계 검증과 재현

저장소 루트에서 다음을 실행한다.

```bash
lake build AgenticConjectures.OeisA100475
python3 problems/oeis-a100475/a100475_certificate.py
```

2026-10-24 개발 실행(다른 작업과 공유한 Apple M5 Max)에서 모듈 빌드는 약
20초 걸렸다. 대부분은 커널 계산이며, $[100112,509712)$의 수 409600개를
검사하는 `cnt_C`가 11–14초를 차지했다. Python 스크립트는 표준 라이브러리만
쓰며 약 3초 만에 끝났다. 이 스크립트는 $10^7+1$ 미만의 소수를 체로 걸러
다음을 확인한다.

- Lean 증명이 쓰는 모든 소수 개수와 구간별 개수, 그리고 정확한 값
  $\pi(10^5)=9592$, $\pi(10^6)=78498$, $\pi(10^7)=664579$;
- 다섯 부등식 $4^m<(m+1)^{K+1}$을 정확한 정수 연산으로, 그리고 각 구간
  $(m,2m]$에 실제로 소수가 많아야 $K$개 있음을;
- 모든 $k\le664579$에 대해 $L(f(k))=L(p_k)\ge L(k)$임을;
- Lean 검사와 코드를 공유하지 않는 고리 탐색으로, 모든 $k\le1229$에서
  $d\le4$ 구간을 벗어남을;
- 점검 삼아, $1\le x<20000$에서 시작한 어떤 궤도도 $664579$를 넘기 전에
  같은 값을 반복하지 않음을.

## 주장하지 않는 것

- 새로움을 주장하지 않는다. 논증은 표준적인 도구만 쓰며, OEIS 항목이
  Rosser 정리를 링크한 것을 보면 증가 논증은 이미 알려져 있었던 것으로
  보인다.
- 고리가 없다는 것 외에, 예컨대 A100475 항들의 증가 속도에 대해서는 아무것도
  주장하지 않는다.
- 이 결과는 검토를 거치지 않았으며 OEIS나 Formal Conjectures에 제출하지
  않았다.
