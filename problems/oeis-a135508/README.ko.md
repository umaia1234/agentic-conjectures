[English](README.md) | **한국어**

# OEIS A135508: McEachen 추측 a(p−1) = p — 판정 기준과 부분 결과

## 명제

[OEIS A135508](https://oeis.org/A135508)(Benoit Cloitre, 2008; 2026-10-24에 개정판
#47 확인)은 오프셋 1로 다음과 같이 정의한다.

\[
a(n)=\frac{x(n+1)}{x(n)}-2,\qquad x(1)=1,\quad x(n)=2\,x(n-1)+\operatorname{lcm}(x(n-1),n).
\]

따라서 \(a(1),a(2),\dots = 2, 3, 1, 1, 1, 7, 2, 1, 1, 11, 1, 1, \dots\)이다. 항목에는
다음 추측이 실려 있다.

> "Conjecture: For prime p such that p-2 is not a prime, a(p-1) = p. The set of sorted
> primes, except 7, is A025584." — Bill McEachen, Sep 26 2025

Formal Conjectures 파일([상류 스냅샷](upstream/README.md))은 이를

```lean
theorem conjecture (p : ℕ) (hp : p.Prime) (hp_twin : ¬ (p - 2).Prime) : a (p - 1) = p
```

로 적고, 미해결(`sorry`)로 남겨 둔다.

## 결과

상태: **partial**. 추측 전체는 증명하지 **못했다**.

상류 정의를 항 그대로 옮겨 Lean 4로 증명한 내용
([`AgenticConjectures/OeisA135508.lean`](../../AgenticConjectures/OeisA135508.lean))은
다음과 같다.

1. **판정 기준.** 모든 소수 \(p\ge5\)에 대해
   \(a(p-1)=p \iff \gcd(x(p-3),\,p-2)>1\)이다.
2. **법 3과 법 5 잉여류.** \(p\equiv2\pmod 3\) 또는 \(p\equiv2\pmod 5\)인 모든 소수
   \(p\ge7\)에서 \(a(p-1)=p\)이다. \(p-2\)에 대한 가정은 필요 없다. 이런 소수는 전체
   소수 중 상대 밀도 \(5/8\)를 차지한다.
3. **인증서.** 1009보다 작은 모든 소수 \(r\)는 \(x(r^2-1)\)을 나눈다.
4. **따름 결과.** \(p-2\)가 합성수이고 그 최소 소인수가 1009보다 작은 모든 소수
   \(p\)에서 추측이 성립한다. 특히
   - 1009보다 작은 각 소수 \(r\)에 대해, \(p-2\)가 소수가 아니고 \(p\equiv 2\pmod r\)인
     모든 소수 \(p\)에서 성립하고,
   - \(1009^2+2=1018083\)보다 작은 모든 소수 \(p\)에서 성립한다.

   Dirichlet 정리에 따르면 덮이지 않는 소수의 상대 밀도는
   \(\prod_{3\le q<1009}\frac{q-2}{q-1}\approx0.107\)이므로, 이 정리는 약 89%를 덮는다.
5. **조건부 환원.** 추측 전체는 "모든 소수 \(r\)가 \(x(r^2-1)\)을 나눈다"에서
   나오고, 따라서 OEIS 주석 "이 수열은 1 또는 소수로만 이루어진다"에서도 나온다.
   거꾸로 그 주석이 참이면, 모든 소수 \(r\ge5\)에 대해 \(s<r^2\)이고
   \(s\equiv-2\pmod r\)인 소수 \(s\)가 존재해야 한다. 등차수열의 최소 소수에 대한 이런
   상계는 우리가 아는 한 알려져 있지 않으므로, 이 경로로는 증명이 되지 않는다.

Lean이 아니라 스크립트로 확인한 내용이다. 서로 독립적으로 작성한 두 프로그램이
\(a(1),\dots,a(10^9)\) 전체의 지문(fingerprint)에서 일치한다.

- 모든 \(n\le10^9\)에 대해 \(a(n)\)은 1 또는 소수이다.
- \(p-2\)가 소수가 아닌 소수 \(p\le10^9+1\) 47,423,028개 모두에서 추측이 성립한다.
- 31622 이하의 모든 소수 \(r\)는 \(x(r^2-1)\)을 나눈다. Lean 보조정리
  `a_pred_eq_of_minFac_dvd`와 합치면, \(p-2\)가 합성수이고 최소 소인수가 31622 이하인
  모든 소수 \(p\)에서 추측이 성립한다(상대 밀도 약 93%). 이것은 스크립트와 Lean을
  합친 결과이며, 커널이 검사한 결과가 아니다.
- \(p-2\)가 소수이면서 \(a(p-1)=p\)인 소수 \(p\le10^9+1\)은 \(p=7\)뿐이다.

주장하지 않는 것: \(p-2\)의 모든 소인수가 31622보다 큰 소수 \(p>10^9+1\)에서의 추측
(순수 Lean 명제로는 \(p-2\)의 모든 소인수가 1008보다 큰 소수 \(p\ge1018083\)).
마지막 스크립트 관찰 외에는, 항목의 쌍둥이 소수 관련 주석에 대해 아무것도 주장하지 않는다.

## 증명

**구조.** \(n\ge1\)이면 \(x(n)>0\)이고, \(g=\gcd(x(n),n+1)\)로 두면
\(\operatorname{lcm}(x(n),n+1)=x(n)\cdot\frac{n+1}{g}\)이다. 따라서
\(x(n+1)=x(n)\bigl(\frac{n+1}{g}+2\bigr)\)이고 \(a(n)=\frac{n+1}{g}\)이다. 그러므로
\(a(n)\mid n+1\), \(x(n+1)=x(n)\,(a(n)+2)\), \(x(n)=\prod_{m=1}^{n-1}(a(m)+2)\)이고,
\(1\le m\le n\)이면 \(x(m)\mid x(n)\)이다.

**판정 기준.** \(p\ge5\)를 소수라 하자. \(a(p-1)=p/\gcd(x(p-1),p)\)이므로
\(a(p-1)=p\)는 \(p\nmid x(p-1)=x(p-3)\,(a(p-3)+2)\,(a(p-2)+2)\)와 동치이다.
- \(x(p-3)\)의 인수 \(a(m)+2\)는 모두 \(m\le p-4\)이므로 \(3\le a(m)+2\le p-1\)이다.
  따라서 \(p\nmid x(p-3)\)이다.
- \(a(p-2)\mid p-1\)에서 \(a(p-2)+2\le p+1\)이다. \(p\)로 나누어떨어지려면
  \(a(p-2)=p-2\)여야 하는데, \(p-2\nmid p-1\)이다. 따라서 \(p\nmid a(p-2)+2\)이다.
- \(a(p-3)\mid p-2\)에서 \(a(p-3)+2\le p\)이다. 따라서 \(p\mid a(p-3)+2\)는
  \(a(p-3)=p-2\), 곧 \(\gcd(x(p-3),p-2)=1\)과 동치이다.

**전이와 잉여류.** \(1\le N\le p-3\)이고 \(q>1\)이 \(x(N)\)과 \(p-2\)를 모두 나누면
\(q\mid\gcd(x(p-3),p-2)\)이다. \(x(4)=60\)이므로 \(N=4\), \(q=3\) 또는 \(q=5\)로 두면
2번 항목을 얻는다.

**최소 소인수.** \(p-2\)가 최소 소인수 \(r\)를 갖는 합성수이면 \(r^2\le p-2\)이다.
그러므로 \(r\mid x(r^2-1)\)이면 \(r\mid x(p-3)\)이고 \(a(p-1)=p\)이다.
\(F(r)=\min\{n: r\mid x(n)\}\)로 두자. Lean 인증서는 세 부분으로 이루어진다.
- 211보다 작은 소수 46개에 대해, 커널이 \(r\mid x(F(r))\)와 \(F(r)\le r^2-1\)을
  확인한다. 가장 빠듯한 경우는 \(F(7)=47\le48\)이다. \(m\le45\)인 \(a(m)\) 중 7을
  법으로 5와 합동인 것은 없고, \(a(46)+2=49\)이다.
- \(211\le r\le997\)인 소수 122개에 대해, 그 곱이 \(x(42611)\)을 나눈다는 것을
  확인한다. 여기서 \(42611=F(991)\)은 1009 미만에서 가장 큰 첫 등장 첨자이고
  \(42611\le211^2-1\)이다.
- 1009 미만의 모든 소수가 빠짐없이 덮인다. 커널은 \([211,1009)\)의 각 \(r\)가 그 곱을
  나누거나 \([2,32)\)에 약수를 갖는다는 것을 확인한다.

\(p-2<1009^2\)가 합성수이면 최소 소인수가 1009보다 작으므로, 유한 범위 결과가
나온다.

**조건부 환원과 그 한계.** 모든 \(n\ge1\)에서 \(a(n)\)이 1 또는 소수라고 하자. 어떤
소수 \(r\)가 \(x(r^2-1)\)을 나누지 않는다면 \(\gcd(x(r^2-1),r^2)=1\)이고
\(a(r^2-1)=r^2\)인데, 이는 1도 소수도 아니다. 따라서 모든 소수 \(r\)가
\(x(r^2-1)\)을 나누고, 추측이 따라 나온다. 거꾸로 소수 \(r\ge5\)에 대해
\(r\mid x(r^2-1)\)은 어떤 \(m\le r^2-2\)에서 \(r\mid a(m)+2\)라는 뜻이다. 그러면
\(a(m)\ne1\)이므로 \(a(m)\)은 \(s\equiv-2\pmod r\)이고 \(s\mid m+1<r^2\)인 소수
\(s\)이다. 등차수열의 최소 소수에 관한 Linnik 정리에서 가장 좋은 무조건 지수는
5(Xylouris)이고, GRH 아래에서는 대략 \((\varphi(q)\log q)^2\)이다. 어느 쪽도 모든
\(r\)에 대해 \(s<r^2\)를 주지 못한다. 자료는 예상과 맞는다. 31622 이하의 모든 소수
\(r\)에서 \(F(r)/r^2\le0.96\)이고, 최댓값은 \(r=7\)에서 나온다.

## Lean 형식화

`lake build AgenticConjectures.OeisA135508`는 약 25초 걸리며, 대부분은
\(x(42611)\)의 커널 평가에 쓰인다. 커널 계산은 모두 `decide +kernel`을 쓰고,
`sorry`, 추가 공리, `native_decide`는 없다.

| 선언 | 내용 |
|---|---|
| `x`, `a` | 상류 정의 그대로 |
| `statement` | 상류 `conjecture`를 `Prop`으로 옮긴 것 |
| `a_0` … `a_4` | 상류 시험값, 같은 `rfl` 증명 |
| `a_eq`, `x_succ_eq` | `n ≥ 1`이면 `a n = (n + 1) / gcd (x n) (n + 1)`, `x (n + 1) = x n * (a n + 2)` |
| `x_dvd_x` | `1 ≤ m ≤ n`이면 `x m ∣ x n` |
| `a_pred_eq_iff` | `p.Prime → 5 ≤ p → (a (p - 1) = p ↔ ¬ Nat.Coprime (x (p - 3)) (p - 2))` |
| `a_pred_eq_of_dvd` | `q ≠ 1`, `q ∣ x N`, `q ∣ p - 2`, `1 ≤ N`, `N + 3 ≤ p`이면 `a (p - 1) = p` |
| `a_pred_eq_of_mod_three_or_five` | `p.Prime → 7 ≤ p → p % 3 = 2 ∨ p % 5 = 2 → a (p - 1) = p` |
| `prime_dvd_x_sq_sub_one` | `r.Prime → r < 1009 → r ∣ x (r ^ 2 - 1)` |
| `a_pred_eq_of_minFac_dvd` | `p.Prime → ¬ (p - 2).Prime → (p - 2).minFac ∣ x ((p - 2).minFac ^ 2 - 1) → a (p - 1) = p` |
| `a_pred_eq_of_minFac_lt` | `p.Prime → ¬ (p - 2).Prime → (p - 2).minFac < 1009 → a (p - 1) = p` |
| `a_pred_eq_of_mod_eq_two` | `p.Prime → ¬ (p - 2).Prime → r.Prime → r < 1009 → p % r = 2 → a (p - 1) = p` |
| `a_pred_eq_of_lt` | `p.Prime → ¬ (p - 2).Prime → p < 1009 ^ 2 + 2 → a (p - 1) = p` |
| `statement_of_forall_prime_dvd` | `(∀ r, r.Prime → r ∣ x (r ^ 2 - 1)) → statement` |
| `statement_of_a_eq_one_or_prime` | `(∀ n, 1 ≤ n → a n = 1 ∨ (a n).Prime) → statement` |
| `exists_prime_of_a_eq_one_or_prime` | 같은 가정에서, 각 소수 `r ≥ 5`에 대해 `r ∣ s + 2`인 소수 `s < r ^ 2`가 존재 |

인증서 자료 `smallCerts`(쌍 \((r,F(r))\))와 `largePrimes`는
`a135508_scan.cpp --certs`로 만들었다. 커널이 모든 나눗셈 관계를 다시 검사하므로
증명은 이 자료를 신뢰하지 않는다. `a135508_check.py`는 이 첨자들이 첫 등장 첨자라는
것도 확인한다.

### 명제 충실성

- `x`와 `a`는 상류 정의 그대로이다. `x 0 = 0`, `x 1 = 1`이고 세 번째 절은 첨자
  \(\ge2\)에서의 점화식이다. `a 0 = 0`은 상류의 경계값이다. `a`는 자연수 나눗셈과
  절단 뺄셈을 쓴다. \(n\ge1\)에서는 `a_eq`가 두 절단 모두 작동하지 않음을 보인다.
  \(x(n)\mid x(n+1)\)이고 몫은 \(a(n)+2\ge3\)이다.
- 오프셋은 OEIS와 같다. \(n\ge1\)이면 `a n`은 OEIS의 \(a(n)\)이다. 스크립트는 DATA의
  92개 항을 문자 그대로의 정의와 대조한다. (항목의 공식 "a(2*4^k) = 2"는 Schepke의
  \(q_2\)처럼 첨자가 하나 밀려 있다. OEIS 오프셋에서는 정확히 \(n=2\cdot4^k-1\)일 때
  \(a(n)=2\)이며, 스크립트가 검사 범위까지 이것도 확인한다.)
- `statement`는 상류 `conjecture`와 묶음 변수가 같고, 절단된 `p - 2`와 `p - 1`도
  같다. \(p=2,3\)이면 절단된 \(p-2\)는 \(0,1\)로 소수가 아니므로, OEIS 문구처럼 이
  소수들도 포함된다. `a 1 = 2`와 `a 2 = 3`이 성립한다. 소수 \(p\ge2\)에서는 \(p-1\)이
  절단되지 않는다.
- 부분 정리들은 필요한 곳에 `¬ (p - 2).Prime` 가정을 그대로 둔다. 법 3·법 5 정리는
  이 가정이 필요 없다. `(p - 2).minFac`은 Mathlib의 `Nat.minFac`이다.
- 상류의 속성(`@[category ...]`, `@[AMS ...]`), `module` / `public section` /
  `@[expose]` 머리말, `FormalConjecturesUtil` import는 뺐다. 어느 것도 명제에 영향을
  주지 않는다.

## 수치 검증 (스크립트 검사)

| 프로그램 | 방법 | 실행 |
|---|---|---|
| [`a135508_scan.cpp`](a135508_scan.cpp) | C++ 지수 장부; 최소 소인수 Eratosthenes 표(`uint16`, 홀수); 지수 상한 255 | \(N=10^9\): 65초, 1.5 GB |
| [`a135508_scan_numba.py`](a135508_scan_numba.py) | Python + numba로 따로 작성; 선형 체(`uint32`); \(q<65536\)은 정확한 지수, 그 위는 포함 여부 표시 | \(N=10^9\): 92초, 3.7 GB |
| [`a135508_check.py`](a135508_check.py) | 표준 라이브러리만 사용; 상류 정의를 큰 정수로 그대로 계산하고, 순수 Python 지수 장부로 \(10^6\)까지 계산 | 문자 그대로 계산 범위 5000: 2초(CI); 200000: 62초 |

지수 장부 프로그램은 Lean에서 증명한(`a_eq`, `x_succ_eq`)
\(a(n)=(n+1)/\gcd(x(n),n+1)\)과 \(x(n+1)=x(n)(a(n)+2)\)를 쓴다. `a135508_check.py`는
\(1\le n\le200000\)에서 이 관계를 문자 그대로의 점화식과도 대조한다. 각 프로그램이
검사하는 항목은 다음과 같다. (C1) 모든 \(a(n)\)이 1 또는 소수; (C2) 소수 \(p\le N+1\)에
대한 추측; (C3) 판정 기준; (C4) \(p-2\)가 합성수인 모든 소수 \(p\le N+1\)에서
\(\operatorname{minFac}(p-2)\mid x(p-3)\); (C5) \(r\le\sqrt{N+1}\)인 모든 소수 \(r\)에서
\(F(r)\le r^2-1\). \(N=10^9\)에서 두 지수 장부 프로그램 모두 실패가 없고, 같은 지문을
출력한다.

```
count_a1=843268629 count_a2=15 sum_a=35999661488869551 hash=d10d4d138b066d11
```

(해시는 \(n=1,\dots,N\)에 걸쳐 \(h\leftarrow 1000003\,h+a(n) \bmod 2^{64}\)이다.)
로그는 [`logs/`](logs/)에 있다. 저장소 루트에서 다음과 같이 재현한다.

```bash
python3 problems/oeis-a135508/a135508_check.py                      # 2초
python3 problems/oeis-a135508/a135508_check.py --literal 200000     # 62초
g++ -O3 -std=c++17 problems/oeis-a135508/a135508_scan.cpp -o /tmp/a135508_scan
/tmp/a135508_scan 10000000                                         # 0.4초
/tmp/a135508_scan 1000000000                                       # 65초, 1.5 GB
python3 problems/oeis-a135508/a135508_scan_numba.py 1000000000      # 92초, 3.7 GB; numpy, numba 필요
lake build AgenticConjectures.OeisA135508                          # 25초
```

실행 시간은 2026-10-24에 Apple M5 Max에서 측정했다.

## 선행 연구와 제출 상태

- 추측은 Bill McEachen의 것이다(Sep 26 2025). OEIS 항목은 "sequence consists of 1's or
  primes only"와 "largest primes in twin pairs never occur"라는 주장도 증명 없이 적어
  둔다(\(a(6)=7\)은 예외이다).
- Markus Schepke의 학위논문 *Über Primzahlerzeugende Folgen*(U. Hannover, 2009; 항목에서
  링크됨) §3.2.2는 이 수열을 \(q_2\)(첨자가 하나 밀림)로 다룬다. 거기서
  \(q_2(n)=n/\gcd(n,b_2(n-1))\)을 보이므로 \(a(n)\mid n+1\)이고, 수열이 1과 소수로만
  이루어지며 7보다 큰 쌍둥이 소수의 큰 쪽이 빠진다는 것을 실험적으로 보고한다. 짝
  수열 \(b_1(n)=b_1(n-1)+\operatorname{lcm}(n,b_1(n-1))\)(§3.2.1)에 대해서는 소인수
  \(p\)의 첫 등장을 \(-1\pmod p\)인 최소 소수와 연결하고, 그에 필요한 상계(그런 소수가
  \(p^2\)보다 작다는 것)는 초등적 방법으로 증명되기 어렵다고 적는다. 여기의 구조 보조정리와 위의 장애물은 A135508에서
  같은 유형을 따른다.
- 2026-10-24 수집 분류(harvest triage)에서 판정 기준과 법 3·법 5 잉여류를 찾았다.
  또 OEIS Open 벤치마크(arXiv:2608.11941; 점수 파일은
  epoch-research/LeanOpenProblems-results)가 전체 명제
  `oeis_135508_conjecture_0`에 대한 시도들을 기록하며, 모두 I(증명 실패)로 채점되었음을
  확인했다.
- 새로움은 주장하지 않는다. 결과는 외부 검토를 거치지 않았고, OEIS나 Formal
  Conjectures에 보고하지 않았다.
