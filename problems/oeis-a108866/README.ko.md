[English](README.md) | **한국어**

# OEIS A108866 — Ordowski의 소수 판정 추측

## 결론

**부분 결과.** 다음과 같이 두자.

\[
S_n=\sum_{k=1}^{n}\frac{2^k}{k},\qquad E_n=-\frac{2}{n}+S_n .
\]

Thomas Ordowski는 $n>3$일 때 $E_n$의 분자가 $n^2$으로 나누어떨어질 필요충분조건은
$n$이 소수인 것이라고 추측했다. 이 문제의 Lean 모듈은 `sorry`, 추가 공리,
`native_decide` 없이 다음을 증명한다.

- 소수 방향: 모든 소수 $p>3$에 대해 $E_p$의 분자는 $p^2$으로 나누어떨어진다
  (`prime_imp`). 논증은 짧고 고전적이며, 독창성을 주장하지 않는다.
- 합성수 방향($n^2$이 분자를 나누지 않음): 모든 짝수 $n$, 3의 거듭제곱이 아닌
  모든 3의 배수, 그리고 어떤 홀수 소수 $q\mid n$에서 두 가지 최고 자릿수 조건 중
  하나를 만족하는 모든 $n$([증명](#증명) 참고).

독립적인 두 프로그램으로 모든 $3<n\le 2\cdot10^6$에서 합성수 방향을 확인했다.
전체 추측은 여전히 **미해결**이다. Lean으로 증명한 족은 $k\ge2$인 홀수 소수
거듭제곱 $q^k$를 하나도 포함하지 않는다. 그 밖의 $2\cdot10^6$ 이하 합성수
중에서 빠지는 것은 1027과 55225뿐이다.

## 원문 명제와 선행 결과 조사

[OEIS A108866](https://oeis.org/A108866)(개정 #37, 2020-03-07; 2026-10-24
확인)은 “Numerator of Sum_{k=1..n} 2^k/k.”이다. 이 항목의 주석은 다음과 같다.

> “Conjecture: for n > 3, numerator(-2/n + Sum_{k=1..n} 2^k/k) == 0 (mod n^2)
> if and only if n is prime. See my formula below. Cf. A332786. - Thomas
> Ordowski, Mar 02 2020”

상류 형식화는 google-deepmind/formal-conjectures의
`OeisA108866.conjecture`이다. 출처 정보와 바이트 단위로 동일한 스냅샷은
[`upstream/`](upstream/README.md)에 있다.

OEIS 항목에는 어느 방향의 증명도 기록되어 있지 않다. 페르마 몫
$q_p(2)=(2^{p-1}-1)/p$에 대해 $E_p=2q_p(2)+\sum_{k=1}^{p-1}2^k/k$이므로,
소수 방향은 다음 합동식과 동치이다.

\[
\sum_{k=1}^{p-1}\frac{2^k}{k}\equiv-2\,q_p(2)\pmod{p^2}\qquad(p\ge5).
\]

페르마 몫에 관한 이런 종류의 합동식은 고전적이며, 아래 증명은 Wolstenholme
정리에서 바로 따라 나오는 짧은 논증이다. OEIS 항목 외에는 문헌 조사를 하지
않았다. 항목이 인용하는 A. M. Robert, *A Course in p-adic Analysis*
(Springer, 2000), p. 278도 확인하지 않았다. 독창성을 주장하지 않으며, OEIS나
상류 저장소에 아무것도 보고하지 않았다.

## Lean 결과

모든 선언은
[`AgenticConjectures/OeisA108866.lean`](../../AgenticConjectures/OeisA108866.lean)의
`AgenticConjectures.OeisA108866` 이름공간에 있다. 아래에서 `num`은 기약분수의
분자이고, $a(c)$는 $S_c$의 분자, 곧 A108866 자신이다.

| 정리 | 내용 |
|---|---|
| `prime_imp` | $p$ 소수, $p>3$ ⇒ $p^2 \mid \mathrm{num}(E_p)$ |
| `not_modEq_of_even` | $n>0$, $2\mid n$ ⇒ $n^2\nmid\mathrm{num}(E_n)$ |
| `not_modEq_of_three_dvd` | $n>0$, $3\mid n$, $n$은 3의 거듭제곱이 아님 ⇒ $n^2\nmid\mathrm{num}(E_n)$ |
| `not_modEq_of_lead_one` | $q$ 홀수 소수, $q\mid n$, $q^e<n<2q^e$ ⇒ $n^2\nmid\mathrm{num}(E_n)$ |
| `not_modEq_of_top_digit` | $q$ 홀수 소수, $q\mid n<q^{e+1}$, $q^e\nmid n$, $q\nmid a(\lfloor n/q^e\rfloor)$ ⇒ $n^2\nmid\mathrm{num}(E_n)$ |
| `not_modEq_of_mul_pow` | $q$ 홀수 소수, $e>0$, $c<q$, $n=cq^e$, $q\nmid\mathrm{num}(E_c)$ ⇒ $n^2\nmid\mathrm{num}(E_n)$ |
| `statement_iff_composite` | `statement` ⇔ 모든 $n>3$에서의 합성수 방향 |
| `iff_of_families` | 소수이거나 위 정리 중 하나의 가정을 만족하는 모든 $n>3$에서 동치가 성립 |

전체 `statement`는 증명하지 못했다.

## 증명

### 소수 방향

1. 파스칼 법칙과 $n$에 대한 귀납법으로
   $S_n=H_n+\sum_{k=1}^{n}\binom nk/k$를 얻는다. 여기서
   $H_n=\sum_{k\le n}1/k$이다(`sum_two_pow_div`).
   $\binom pk/k=p\binom{p-1}{k-1}/k^2$이므로 이는
   \[
   E_p=H_{p-1}+p\sum_{k=1}^{p-1}\frac{\binom{p-1}{k-1}}{k^2}
   \]
   이 된다(`ratExpression_succ`).
2. $p\ge5$에 대한 Wolstenholme 정리 $p^2\mid H_{p-1}$
   (`padicNorm_harmonic_le`). $k$와 $p-k$를 짝지으면
   $2H_{p-1}=p\sum_{k=1}^{p-1}1/(k(p-k))$이다. 또한
   $1/(k(p-k))\equiv-1/k^2 \pmod p$이고, $p\ge5$이면
   $\sum_{x\in\mathbb F_p^\times}x^{-2}=\sum_{x\in\mathbb F_p}x^2=0$이다.
3. $p\mid\sum_{k=1}^{p-1}\binom{p-1}{k-1}/k^2$(`padicNorm_sum_choose_le`).
   $k$와 $p-k$를 짝지으면 이 합의 두 배는 $p$를 법으로
   $\sum_k\binom pk/k^2$와 합동이고, $0<k<p$이면 $p\mid\binom pk$이다.

따라서 $v_p(E_p)\ge2$이며, 이것이 `prime_imp`이다.

### 합성수 방향

$\lVert\cdot\rVert_q$를 $q$진 절댓값이라 하자. 어떤 소수 $\ell\mid n$에서
$\lVert E_n\rVert_\ell>1/\ell$이면 $\ell$은 $E_n$의 분자를 나누지 않으므로
$n^2$도 분자를 나누지 않는다(`not_modEq_of_padicNorm`).

- **$\ell=2$, $n$ 짝수.** 모든 항이 $\lVert 2^k/k\rVert_2<1$을 만족하고
  $\lVert2/n\rVert_2\ge1$이다. 따라서 $\lVert E_n\rVert_2\ge1$이다.
- **$\ell=q$ 홀수.** $q^e\le n<q^{e+1}$이라 하고, $n$의 $q$진 최고 자릿수를
  $c=\lfloor n/q^e\rfloor$라 하면 $1\le c<q$이다. $q^e\nmid k$인 항 $2^k/k$의
  절댓값은 $q^e$보다 작다. 나머지 항 $k=jq^e$($1\le j\le c$)의 합은
  $q^{-e}\sum_{j\le c}2^{jq^e}/j$이다. 페르마 소정리로
  $2^{jq^e}\equiv2^j\pmod q$이고 $c<q$이므로
  $\sum_{j\le c}2^{jq^e}/j\equiv S_c\pmod q$이다. $S_c$의 분자는 $a(c)$이다.
  - $q^e\nmid n$이면 $\lVert2/n\rVert_q<q^e$이다. 따라서 $q\nmid a(c)$이면
    $\lVert E_n\rVert_q=q^e$이다(`not_modEq_of_top_digit`).
    - $c=1$, $a(1)=2$인 경우가 `not_modEq_of_lead_one`이다.
    - $q=3$이면 자릿수 $c\in\{1,2\}$에 대해 $a(1)=2$, $a(2)=4$이다. 짝수
      경우와 합치면 3의 거듭제곱이 아닌 모든 3의 배수가 포함된다
      (`not_modEq_of_three_dvd`).
  - $e\ge1$이고 $n=cq^e$이면 $-2/n$이 최고 차수 항들에 합류한다. 이들의 합은
    $q$를 법으로 $E_c$와 합동인 수에 $q^{-e}$를 곱한 것이다. 따라서
    $q\nmid\mathrm{num}(E_c)$이면 $\lVert E_n\rVert_q=q^e$이다
    (`not_modEq_of_mul_pow`).

**족이 다루지 못하는 경우.** $k\ge2$인 홀수 소수 거듭제곱 $n=q^k$에서는
$c=1$이고 $E_1=0$이어서 최고 차수 항들이 상쇄된다. 더 세밀한 $q$진 전개가
필요하다. $2\cdot10^6$ 이하에서 어느 정리로도 다루지 못하는 다른 합성수는
다음 두 개뿐이며, 둘 다 모든 소인수에서 두 조건을 모두 만족하지 못한다.

- $1027=6\cdot13^2+13=13\cdot79$: $13\mid a(6)=416$이고
  $79\mid\mathrm{num}(E_{13})$이다.
- $55225=3\cdot5^6+8350=25\cdot47^2$: $5\mid a(3)=20$이고
  $47\mid\mathrm{num}(E_{25})$이다.

두 수 모두 계산으로는 배제된다($v_{13}(E_{1027})=-1$,
$v_5(E_{55225})=-4$).

## 명제 충실도

- `a`와 `ratExpression`은 상류 정의를 항 단위로 그대로 옮긴 것이다.
  `statement`는 `∀ n : ℕ, n > 3 → ((ratExpression n).num ≡ 0
  [ZMOD (n^2 : ℤ)] ↔ n.Prime)`로, 상류 `conjecture`의 가정을 한정기호 안으로
  옮긴 것이다. 두 명제는 같다.
- `∑ i ∈ range n, 2^(i+1)/(i+1)`은 $\sum_{k=1}^n2^k/k$이다(첨자 이동
  $k=i+1$). `if n > 0` 분기는 $n=0$에서만 의미가 있다.
- `Rat.num`은 OEIS 문구와 같이 기약분수의 분자이다. 합동식
  `≡ 0 [ZMOD (n^2 : ℤ)]`는 그 정수가 $n^2$으로 나누어떨어진다는 뜻이며,
  부호는 상관없다.
- 합성수 방향 정리들은 각자의 가정(예: $n>0$)을 가지며 $n>3$을 가정하지 않는다.
  `iff_of_families`는 이들을 $n>3$에서의 동치의 사례로 다시 진술한다.
- 상류의 테스트 보조정리 `a_0`–`a_4`와 `eval_a` 매크로는 옮기지 않았다. 이들은
  추측이 아니라 `a`의 값을 확인한다.

## 기계 검증과 재현

$E_n$은 0이 아닌 유리수이다(실제로 $n\ge2$이면 $E_n>0$). 따라서 $n^2$이 그
분자를 나눌 필요충분조건은 모든 소수 $q\mid n$에 대해
$v_q(E_n)\ge2v_q(n)$인 것이다. 두 프로그램은 $q$가 $n$의 소인수인 모든 쌍
$(n,q)$에 대해 상한을 둔 값 $\min(v_q(E_n),2v_q(n))$을 계산한다.

- [`a108866_check.py`](a108866_check.py)는 Python 표준 라이브러리만 사용한다
  (gmpy2는 `--gmpy2`로 선택적으로 사용). 세 가지 계산을 수행한다.
  - `Fraction`으로 분자를 $n^2$으로 나눈 나머지를 직접 확인하는 검사
  - 방법 A: 정확한 정수 표현 $A_n/\mathrm{lcm}(1,\dots,n)$
  - 방법 B: $q^{3L}$을 법으로 하는 $q$진 누적합

  `--compare FILE`은 FILE의 모든 `n q v` 줄을 방법 A와 대조한다. 스크립트는
  Lean 정리의 가정을 $q$를 법으로 정확히 계산하여, 어느 정리로도 다루지 못하는
  합성수 목록도 출력한다.
- [`a108866_qadic.cpp`](a108866_qadic.cpp)는 $q$진 방법을 128비트 모듈러
  곱셈으로 따로 구현한 C++ 프로그램이며, 알고리즘이 방법 A와 독립적이다.
  $q\le\sqrt N$인 각 소수 $q$의 모든 배수를 처리하고, 증인이 없는 합성수를 위한
  대체 경로를 갖추고 있다. $2\cdot10^6$ 이하에서는 대체 경로가 필요한 합성수가
  없었다. 또한 $p\le10^5$인 소수의 쌍 $(p,p)$도 확인한다.

| 실행 | 범위 | 결과 | 실행 시간 |
|---|---|---|---|
| `python3 a108866_check.py` (CI) | $3<n\le10^4$ | 직접 검사($n\le3000$), A, B 일치; Lean 족 밖의 합성수 40개(홀수 소수 거듭제곱 39개와 1027) | 3초 |
| C++ + 방법 A, `--compare` (CI) | $3<n\le10^5$ | C++ 출력 211,744줄 모두 방법 A와 일치; Lean 족 밖의 합성수 95개(홀수 소수 거듭제곱 93개, 1027, 55225) | 컴파일 포함 22초 |
| C++ + gmpy2를 쓴 방법 A, `--compare` (로컬, `ci_feasible: false`) | $3<n\le2\cdot10^6$ | 아래 참고 | 부하 상태에서 6.4분 |

로컬 실행은 2026-10-24에 다른 작업과 함께 쓰이던 Apple M5 Max에서 했다. 로그
요약은 다음과 같다.

- C++: 합성수 1,851,066개, 대체 경로가 필요한 수와 배제되지 않은 수는 모두
  0개. 9,590개의 소수 $5\le p\le10^5$에서 $\min(v_p(E_p),2)$의 최솟값은 2.
  4,498,598줄 출력. 거의 유휴 상태에서 21초, 부하 상태에서 26초.
- 방법 A(Python 3.12.13, gmpy2 2.3.2): $3<n\le2\cdot10^6$의 소수 148,931개와
  합성수 1,851,066개, $(n,q)$ 쌍 5,808,798개. $E_n$의 분자가 $n^2$으로
  나누어떨어지는 것은 정확히 $n$이 소수일 때이며, 모든 소수
  $5\le p\le2\cdot10^6$에서 $\min(v_p(E_p),2)=2$이다. C++ 출력 4,498,598줄이
  모두 일치한다. 적용 범위 보고에 따르면 Lean 족 밖의 합성수는 285개로, 홀수
  소수 거듭제곱 283개와 1027, 55225이다. 부하 상태에서 방법 A와 보고에
  357초, 명령 전체에 384초가 걸렸다. 앞서 거의 유휴 상태에서 방법 A만 실행했을
  때는 306초였다.

저장소 루트에서 다음을 실행한다.

```bash
lake build AgenticConjectures.OeisA108866
cd problems/oeis-a108866
python3 a108866_check.py
mkdir -p build && g++ -O2 -std=c++17 -o build/a108866_qadic a108866_qadic.cpp
./build/a108866_qadic 100000 > build/qadic_1e5.tsv
python3 a108866_check.py --limit 100000 --skip-qadic --literal-limit 0 --compare build/qadic_1e5.tsv
# 로컬 전용: 59 MB 파일을 만든다
./build/a108866_qadic 2000000 > build/qadic_2e6.tsv
python3 a108866_check.py --limit 2000000 --skip-qadic --literal-limit 0 --gmpy2 --compare build/qadic_2e6.tsv
```

gmpy2가 없으면 마지막 명령은 Python 정수를 사용한다. 이 경우의
$2\cdot10^6$ 실행 시간은 측정하지 않았다.

## 주장하지 않는 것

- 추측은 증명되지 않았다. $k\ge2$인 홀수 소수 거듭제곱 $q^k$($2\cdot10^6$
  이하에 283개)와, 모든 홀수 소인수가 두 자릿수 조건을 만족하지 못하는 합성수
  1027, 55225($2\cdot10^6$ 이하에서 유일한 나머지)는 어느 Lean 정리로도 다루지
  못한다.
- 계산은 $3<n\le2\cdot10^6$에 대한 유한 검증일 뿐이다.
- 독창성을 주장하지 않는다. 이 결과는 심사를 받지 않았고 OEIS나 상류 저장소에
  보고하지 않았다. 외부 제출에는 사람의 승인이 필요하다.
