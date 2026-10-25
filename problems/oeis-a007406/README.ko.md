[English](README.md) | **한국어**

# OEIS A007406 — Eldar–Ordowski gcd 추측

## 결론

**부분 결과(partial)다.** 추측 자체는 증명하지 못했다. 이 디렉터리에는 다음이 있다.

- 소수 경우(고전적 결과), `2`·`3`·`5` 부분, 추측을 `q`진 값매김(valuation)에 대한
  상계로 바꾸는 정확한 환원, 그리고 `n = t q` (`2 ≤ t ≤ 6`, 모든 소수 `q`)와 모든
  `5`-매끄러운 `n > 3`의 경우에 대한 Lean 4 증명.
- 모든 소수 `5 ≤ q ≤ 2,642,245`에 대해 환원된 상계를 확인하는 Boyd 트리 인증서.
  Lean 환원과 합치면 모든 `3 < n ≤ 5,284,491`에서 추측이 성립한다(계산에 의존하며,
  아래 신뢰 모델 참조).
- 정의로부터 `3 < n ≤ 10^6` 범위를 직접 확인하는 서로 독립적인 두 구현.

Lean 증명에는 `sorry`, 추가 공리, `native_decide`가 쓰이지 않는다.

## 수열과 추측

[OEIS A007406](https://oeis.org/A007406)(Wolstenholme 수, offset 1)은

\[
H_2(n)=\sum_{k=1}^{n}\frac{1}{k^2}:\qquad 1, 5, 49, 205, 5269, 5369, 266681, \dots
\]

의 분자다. 2026-10-24에 확인한 항목에는 다음 주석이 있다.

> “Conjecture: for n > 3, gcd(n, a(n-1)) = A089026(n). Checked up to n = 10^5.”
> — Amiram Eldar and Thomas Ordowski, Jul 28 2019

여기서 [A089026](https://oeis.org/A089026)`(n)`은 `n`이 소수이면 `n`, 아니면
`1`이다. Jonathan Sondow는 소수 경우가 Wolstenholme 정리에서 나오므로 합성수
`n > 3`에 대해 `gcd(n, a(n-1)) = 1`임을 보이는 일만 남는다고 덧붙였다.

upstream 형식화는 google-deepmind/formal-conjectures의 커밋
`c094b979118b89adb77cf5f8d923ac9dd2e51b1d`에 있는 `OeisA7406.conjecture`다.
`7406.lean`과 이 파일이 가져오는 `89026.lean`의 바이트 단위 사본은
[upstream/](upstream/README.md)에 있다.

## 수학적 내용

`v_q`를 `q`진 값매김, `a(m)`을 `H_2(m)`의 분자라 하고, 소수 `q`에 대해

\[
U_q(m)=\sum_{k\le m,\ q\nmid k}\frac1{k^2},\qquad
H_2(m)=U_q(m)+\frac{H_2(\lfloor m/q\rfloor)}{q^2}
\]

로 둔다. `U_q(m)`은 `q`-정수다. `q ≥ 5`이면 블록 합이 `q`를 법으로 사라진다.
즉 `U_q(qt) ≡ t·Σ_{x∈F_q^×} x^{-2} = t·Σ_{x∈F_q^×} x^2 ≡ 0 (mod q)`이다.

1. **소수 경우**(고전적, Wolstenholme 유형). `t = 1`로 두면 소수 `p ≥ 5`에 대해
   `p ∣ a(p-1)`이고, 따라서 `gcd(p, a(p-1)) = p`다.
2. **정확한 환원.** 소수 `q ≥ 5`와 `t ≥ 2`에 대해
   `H_2(qt-1) = U_q(qt) + H_2(t-1)/q^2`이고 `v_q(U_q(qt)) ≥ 1`이므로,
   `q ∣ a(qt-1)`일 필요충분조건은 `v_q(H_2(t-1)) ≥ 3`이다.
3. **작은 소수.** 모든 `m ≥ 1`에 대해 `v_2(H_2(m)) ≤ 0`, `v_3(H_2(m)) ≤ 0`이고
   (즉 `a(m)`은 `2`나 `3`으로 나누어지지 않는다), `v_5(H_2(m)) ≤ 2`다.
4. **동치.** 추측은 모든 소수 `q ≥ 5`와 모든 `m ≥ 1`에 대해
   `v_q(H_2(m)) ≤ 2`인 것과 동치다.
5. **가지치기와 트리.** `s ≥ 1`, `0 ≤ r < q`, `v_q(H_2(s)) ≤ 1`이면
   `v_q(H_2(qs+r)) = v_q(H_2(s)) - 2`다. 따라서 `v_q(H_2(m)) ≥ 2`인 모든 `m`은
   뿌리가 `1, …, q-1`이고, 노드 `s`가 `v_q(H_2(s)) ≥ 2`일 때만 자식
   `qs, …, qs+q-1`을 갖는 트리 안에 있다. 이는 조화수에 대한 Boyd 트리의
   대응물이다. 모든 노드에서 `v_q ≤ 2`인 유한 트리를 찾으면 모든 `m ≥ 1`에 대해
   `v_q(H_2(m)) ≤ 2`가 증명된다.

`2`·`3` 부분은 모든 뿌리에서 `v_q ≤ 0`인 트리이고, `5` 부분은 뿌리에서
`v_5 ≤ 1`인 트리다.

## Lean 결과

모듈 `AgenticConjectures.OeisA007406`
([소스](../../AgenticConjectures/OeisA007406.lean)):

| 선언 | 내용 |
|---|---|
| `statement` | upstream과 같은 추측(증명하지 않음) |
| `prime_dvd_a_pred`, `statement_at_prime` | 소수 `p ≥ 5`에 대해 `p ∣ a(p-1)`; 소수 `n > 3`에서의 추측 |
| `two_not_dvd_a`, `three_not_dvd_a` | `m ≥ 1`이면 `2 ∤ a(m)`, `3 ∤ a(m)` |
| `padicValRat_five_H2_le_two`, `five_not_dvd_a` | `m ≥ 1`이면 `v_5(H_2(m)) ≤ 2`; `t ≥ 2`이면 `5 ∤ a(5t-1)` |
| `dvd_a_iff` | 소수 `q ≥ 5`, `t ≥ 2`에 대해 `q ∣ a(qt-1) ↔ 3 ≤ v_q(H_2(t-1))` |
| `statement_iff` | 추측 `↔` 모든 소수 `q ≥ 5`, `m ≥ 1`에 대해 `v_q(H_2(m)) ≤ 2` |
| `padicValRat_H2_mul_add` | 가지치기 보조정리(위 5번) |
| `padicValRat_H2_le_two_of_tree` | 계산이 사용하는 트리 인증서 인터페이스 |
| `statement_le_of_padicValRat_le_two` | 모든 소수 `5 ≤ q ≤ Q`에서의 상계가 `3 < n ≤ 2Q+1`에서의 추측을 준다 |
| `statement_at_of_padicValRat_le_two` | `n`의 소인수 `q ≥ 5`에서의 상계가 `n`에서의 추측을 준다 |
| `statement_at_of_five_smooth`, `statement_at_two_pow` | 모든 `5`-매끄러운 `n > 3`; `n = 2^k`, `k ≥ 2` |
| `statement_at_two_mul` … `statement_at_six_mul` | `t = 2, 3, 4, 5, 6`과 모든 소수 `q`에 대해 `n = tq` |
| `statement_at_mul` | `n = qt`, `q` 소수, `t ≥ 2`는 `5`-매끄러움, `q ≥ 5`이면 `q^3 ∤ a(t-1)` |
| `statement_at_sq` | `n = q^2`, `q ≥ 5` 소수, `q^3 ∤ a(q-1)` |
| `statement_at_prime_pow` | `n = q^k`, `k ≥ 2`, `q ≥ 5` 소수, `q^2 ∤ a(q-1)` |
| `a_zero` … `a_five` | `a(0..5) = 0, 1, 5, 49, 205, 5269` |

마지막 세 행의 가정은 주어진 `q`나 `t`마다 유한한 확인으로 끝난다.
`q^2 ∤ a(q-1)` 조건은 정확히 `v_q(H_2(q-1)) ≥ 2`일 때 깨진다. 고전적으로 이는
Wolstenholme 소수(`q ∣ B_{q-3}`)와 정확히 일치하며, 알려진 것은 `16843`과
`2124679`뿐이다. 아래 뿌리 탐색에서도 `2,642,245` 이하의 다른 `q`는 나오지 않았다.

## 계산

### `5 ≤ q ≤ 2,642,245`에 대한 Boyd 트리 인증서

각 소수 `q`마다 뿌리 `1 ≤ m < q` 가운데 `H_2(m) ≡ 0 (mod q^2)`, 즉
`v_q(H_2(m)) ≥ 2`인 것을 찾는다. 그런 뿌리는 모두 `q^15`를 법으로 정확히 다시
계산하고(`v_q ≥ 3`인 뿌리가 있으면 반례다), 그 자식들은 다음 식으로 `q^13`을 법으로
계산한다.

\[
H_2(qs+r)=U_q(qs)+\sum_{\rho=1}^{r}\frac{1}{(qs+\rho)^2}+\frac{H_2(s)}{q^2},\qquad
U_q(qs)\equiv\sum_{j<P}(-1)^j(j+1)\,q^j F_j(s)\,A_{j+2}\pmod{q^P}
\]

여기서 `F_j(s) = Σ_{i<s} i^j`, `A_t = Σ_{ρ=1}^{q-1} ρ^{-t}`다. `v_q = 2`인 자식이
나오면 다시 같은 방식으로 전개한다.

뿌리 탐색은 서로 독립적인 두 C 구현으로 했다(소수 `192,723`개, 각각 약
`2.4·10^11`개의 뿌리 값).

- `a007406_roots_mont.c` (R1): `q^3`을 법으로 하는 Montgomery 연산과 일괄 역원
  계산. `v_q ≥ 2`와 `v_q ≥ 3`을 따로 보고한다.
- `a007406_roots_lin.c` (R2): `q^2`을 법으로 하는 선형 시간 역원 표와 일반
  128비트 나머지 연산.

두 탐색기는 `v_q(H_2(m)) ≥ 2`인 뿌리로 같은 다섯 개를 보고하며, R1은
`v_q ≥ 3`인 뿌리를 찾지 못했다. Python 검사기는 각 뿌리를 `q^15`를 법으로 다시
계산하고 자식을 전개하며, `a007406_children.gp`가 이 전개를 독립적으로 반복한다.

| `q` | 뿌리 `m` | `v_q(H_2(m))` | `v_q = 0 / 1 / ≥2`인 자식 수 |
|---|---|---|---|
| 7 | 3 = (q−1)/2 | 2 | 6 / 1 / 0 |
| 16843 | 8421 = (q−1)/2 | 2 | 16841 / 2 / 0 |
| 16843 | 16842 = q−1 | 2 | 16842 / 1 / 0 |
| 2124679 | 1062339 = (q−1)/2 | 2 | 2124678 / 1 / 0 |
| 2124679 | 2124678 = q−1 | 2 | 2124679 / 0 / 0 |

따라서 모든 트리는 깊이 1에서 멈추고, 모든 소수 `5 ≤ q ≤ 2,642,245`와 모든
`m ≥ 1`에 대해 `v_q(H_2(m)) ≤ 2`다. 다섯 뿌리는 모두 고전적인 합동식
`H_2(q−1) ≡ (2/3) q B_{q−3}`, `H_2((q−1)/2) ≡ (7/3) q B_{q−3} (mod q^2)`로
설명된다(여기서는 `q ≤ 300`에 대해 수치로 확인했다). `q = 16843`과
`q = 2124679`는 알려진 Wolstenholme 소수(`q ∣ B_{q−3}`)이고, `q = 7`은 계수
`7/3`을 나눈다. 두 탐색기는 또한 모든 `q`에서 `q ∣ a(q−1)`임을 확인하며,
`v_q ≥ 1`인 뿌리 `m ≤ q−2`의 개수 `385,031`에서도 일치한다.

`statement_le_of_padicValRat_le_two`(`Q = 2,642,245`)와 합치면 모든
`3 < n ≤ 5,284,491`에서 추측이 성립하고, `statement_at_of_padicValRat_le_two`와
합치면 모든 소인수가 `2,642,245` 이하인 모든 `n > 3`에서도 성립한다.

### 정의로부터의 직접 확인

정의로부터 `gcd(n, a(n-1))`을 `A089026(n)`과 직접 비교하는 독립적인 두 구현이
있으며, 둘 다 환원을 쓰지 않는다.

- `a007406_certificate.py --direct-max N`은 정수 `B(m) = lcm(1..m)^2 H_2(m)`을
  유지하면서 `n = m+1`의 소인수 `q`마다
  `v_q(a(m)) = max(0, v_q(B(m)) - 2 v_q(lcm(1..m)))`를 읽어 낸다.
  `--fraction-max N`은 같은 일을 `fractions.Fraction`으로 한다.
- `a007406_direct.gp`는 PARI/GP의 정확한 유리수로 `1/k^2`을 더한 뒤
  `gcd(분자, n)`을 계산한다.

두 구현 모두 `3 < n ≤ 10^6`에서 불일치를 찾지 못했다(Python 12분,
PARI/GP 3.2분). 이 범위는 위에서 다룬 `n ≤ 5,284,491` 안에 있으며, 이 실행의
의미는 환원을 전혀 쓰지 않는다는 데 있다. Eldar–Ordowski의 확인(`n ≤ 10^5`)을
넓힌 것이기도 하다.

### 신뢰 모델

- Lean: 환원, 위의 수열족, 그리고 "모든 소수 `5 ≤ q ≤ Q`에서의 상계 ⇒
  `3 < n ≤ 2Q+1`에서의 추측"이라는 함의.
- 계산(Lean 아님): `5 ≤ q ≤ 2,642,245`에서의 상계. `q = 20,000`을 넘는 범위에서
  CI가 다시 돌리지 않는 부분은 뿌리 탐색뿐이며, 이는 히트 목록과 소수 개수가 일치하는
  독립적인 두 구현으로 실행했다. 자식 전개는 Python 검사기와, 이와 독립적인
  `a007406_children.gp`(Stirling 수 대신 Bernoulli 다항식으로 거듭제곱 합을 계산)가
  각각 수행하며, 모든 자식 값매김 개수에서 일치한다.
- 검사기의 자체 시험은 전개식을 정확한 분수 계산과 비교하고, `q = 5, 7, 11, 13`에
  대해서는 트리를 `v_q(H_2(m)) ≥ 2`인 모든 `m ≤ 700…2500`의 전수 목록과 비교한다.

## 재현

모든 명령은 이 디렉터리에서 Python 3.8 이상(표준 라이브러리만)으로 실행한다.
시간은 다른 작업과 함께 쓰던 Apple M5 Max, Python 3.12, PARI/GP 2.19.0,
Apple clang 21에서 잰 값이다. CI는 첫 번째 명령을 실행한다.

```bash
# 자체 시험; n <= 3000(Fraction)과 n <= 30000(스케일한 정수)에서 정의 그대로의
# 확인; 모든 소수 5 <= q <= 20000(2260개)에 대한 완전한 Boyd 트리.
python3 a007406_certificate.py --self-test --fraction-max 3000 \
  --direct-max 30000 --tree-max 20000                          # 약 7초

# 커밋된 탐색 로그 재검증: 히트 목록과 개수가 같은지 확인하고, 각 히트를
# q^15를 법으로 다시 계산한 뒤 그 자식을 q^13을 법으로 전개한다.
python3 a007406_certificate.py --hits logs/roots_R1_2642245.txt \
  logs/roots_R2_2642245.txt                                    # 약 30초
```

CI 밖에서 실행하는 명령(출력과 시간은 [`logs/RUNS.txt`](logs/RUNS.txt)):

```bash
# 두 뿌리 탐색(우리는 각각 스레드 2개로 실행했다; 스레드 수는 결과에 영향이 없다).
cc -O3 -std=c11 -pthread a007406_roots_mont.c -o /tmp/a007406_roots_mont
cc -O3 -std=c11 -pthread a007406_roots_lin.c -o /tmp/a007406_roots_lin
/tmp/a007406_roots_mont 5 2642245 4 > /tmp/a007406_R1.txt     # R1: 실제 23분, CPU 38분
/tmp/a007406_roots_lin 5 2642245 4 > /tmp/a007406_R2.txt      # R2: 실제 81분, CPU 153분
python3 a007406_certificate.py --hits /tmp/a007406_R1.txt /tmp/a007406_R2.txt

# 다섯 히트의 독립적인 자식 전개(모든 줄에 "v>=2: []"가 나와야 한다).
printf 'children(7, 3, 13)\nchildren(16843, 8421, 13)\nchildren(16843, 16842, 13)\nchildren(2124679, 1062339, 13)\nchildren(2124679, 2124678, 13)\n' \
  | gp -q -D parisizemax=4G a007406_children.gp                # 약 30초

# 3 < n <= 10^6에 대한 직접 확인.
python3 a007406_certificate.py --direct-max 1000000            # 12분
echo 'check(10^6)' | gp -q -D parisizemax=2G a007406_direct.gp # 3.2분
```

## 주장하지 않는 것

- 추측 자체. `5,284,491`보다 큰 합성수 `n`은 `n`의 소인수 `q ≥ 5`가 모두
  `2,642,245` 이하인 경우(계산), `2 ≤ t ≤ 6`인 `n = tq`인 경우, `n`이
  `5`-매끄러운 경우, 또는 `statement_at_mul`, `statement_at_sq`,
  `statement_at_prime_pow`의 명시적 가정 아래에서만 다룬다.
- `q ≤ 2,642,245`에 대한 상계는 계산 결과이며 Lean으로 형식화하지 않았다. Lean은
  그런 상계가 주어진 범위에서 추측을 함의한다는 것만 증명한다.
- `q = 20,000`을 넘는 범위에서 뿌리 히트 목록이 완전하다는 사실은 두 C 탐색기에
  의존한다. CI는 이 탐색을 다시 실행하지 않는다.

## 명제의 충실성

- `a`는 upstream `OeisA7406.a`와 항 하나하나까지 같다:
  `(∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ) ^ 2).num.natAbs`. `n ≥ 1`이면 합이
  양수이므로 분자의 `natAbs`는 분자 그 자체이고, OEIS 정의(offset 1)와 일치한다.
  Lean의 `a 0 = 0`(빈 합)은 OEIS 범위 밖의 값이며 명제에 쓰이지 않는다.
- `a089026`은 upstream `OeisA89026.a`(`if n.Prime then n else 1`)와 항 하나하나까지
  같고, 두 정의를 한 이름공간에 두려고 이름만 바꿨다. `n ≥ 1`에서 A089026과 일치하며,
  추가 값 `a089026 0 = 1`은 명제에 쓰이지 않는다.
- `statement`는 `∀ n : ℕ, 3 < n → Nat.gcd n (a (n - 1)) = a089026 n`으로,
  `OeisA7406.conjecture (n) (hn : 3 < n)`의 명제와 같다. `3 < n`이면 자연수 뺄셈
  `n - 1`은 보통의 뺄셈이고, 첨자 `n - 1 ≥ 3`은 OEIS 범위 안에 있다.
- upstream은 `a_0 … a_4`를 `decide +native`로 증명하지만, 여기서는 같은 값을 정확한
  유리수 계산으로 증명한다(`a_zero` … `a_four`).

## 선행 결과

- 소수 경우는 고전적이다. 소수 `p ≥ 5`에 대해 `H_2(p-1) ≡ 0 (mod p)`이다
  (Wolstenholme 정리. OEIS 항목에 T. D. Noe와 J. Sondow가 적어 두었다).
- OEIS 항목은 `n = 10^5`까지 확인했다고 적고 있다(Eldar–Ordowski).
- `q`진 값매김으로의 환원과 트리 가지치기는 표준 기법이다(조화수에 대한 Boyd의
  `p`진 연구). `H_2(q-1)`이 `q^2`으로 나누어지는 조건은 고전적인 Wolstenholme 소수
  조건이다. 여기 있는 어떤 것도 새롭다고 주장하지 않는다.
- 2026-10-24 수집 단계의 분류(triage)에서는 `q ≤ 3000`까지의 Boyd 트리 탐색과
  `n ≤ 2500`까지의 직접 확인을 했다.

이 결과는 OEIS나 upstream에 보고하지 않았다. 외부 제출에는 사람의 승인이 필요하다.

## 파일

- [`a007406_certificate.py`](a007406_certificate.py) — 표준 라이브러리만 쓰는 검사기
  (정의 그대로의 확인, 스케일한 정수 확인, Boyd 트리, 히트 파일 모드, 자체 시험).
- [`a007406_roots_mont.c`](a007406_roots_mont.c),
  [`a007406_roots_lin.c`](a007406_roots_lin.c) — 두 뿌리 탐색기.
- [`a007406_children.gp`](a007406_children.gp) — 독립적인 자식 전개.
- [`a007406_direct.gp`](a007406_direct.gp) — PARI/GP 직접 확인.
- [`logs/`](logs/) — 대규모 실행의 출력과 실행 시간.
- [`upstream/`](upstream/README.md) — upstream 사본과 출처.
