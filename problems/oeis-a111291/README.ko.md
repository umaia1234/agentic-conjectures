[English](README.md) | **한국어**

# OEIS A111291 — 콜턴 추측 $\pi(n)\le 2T(n)$

## 결론

refactorable 수에 관한 콜턴(Colton)의 추측은 **모든** $n$에 대해 성립한다. $\tau(k)$를 $k$의
약수의 개수, $T(n)=\#\{1\le k\le n:\ \tau(k)\mid k\}$, $\pi(n)$을 $n$ 이하의 소수의 개수라 하면

\[
\pi(n)\le 2\,T(n)\qquad(n\ge 0)
\]

이고, 등호는 $n=0$과 $n=7$에서만 성립한다. 이는 **컴퓨터 보조 증명**이다. $n\le 10^6$은 전수
검사로, $10^6\le n\le 1.13\cdot 10^{13}$은 $T$와 $\pi$의 정확한 값으로 만든 격자 인증서로,
$n\ge 10^{12}$은 Zelinsky의 $p$-생성수, 정확히 계산한 상수, Dusart의 명시적 $\pi$ 부등식에
기반한 해석적 꼬리 논증으로 다룬다. CI가 세 부분을 모두 다시 실행한다. Lean 4는 명제와 논증에
쓰이는 기초 보조정리를 검증하지만 계산 자체는 검증하지 않는다. 전체 논증은
[DETAILS.ko.md](DETAILS.ko.md)에 있다.

꼬리 논증과 별개로, 점별(pointwise) 체가 $n\le 10^{12}$인 모든 $n$을 직접 검사하고, 격자는
Zelinsky가 2002년에 부등식을 증명한 경계 $7.42\cdot 10^{13}$을 넘어 $10^{15}$까지 이어진다.
따라서 이 결과는 Zelinsky의 정리 8과 격자를 합쳐서도 얻어진다.

## 정식 명제와 선행 연구 확인

2026-10-24에 확인한 [OEIS A111291](https://oeis.org/A111291)은 $10^n$ 이하의 refactorable 수
([A033950](https://oeis.org/A033950))의 개수이며, 데이터는 $a(0..11)$까지 있다. 이 항목의
주석은 $x$ 미만의 개수가 적어도 $x/(2\log x)$라는 추측을 콜턴의 것으로 소개한다. 상류 Formal
Conjectures는 충분히 큰 $x$에 대한 이 형태를 `conjecture`(분류 `research solved`)로 적어 두었고,
이것은 여기서 다루는 대상이 아니다. 여기서 다루는 점별 형태는 Zelinsky(J. Integer Seq. 5
(2002), Article 02.2.8)가 콜턴의 추측을 읽은 방식이다: “Colton's conjecture becomes:
$T(n)\ge\pi(n)/2$ for all $n$.” Zelinsky는 이를 $n>7.42\cdot 10^{13}$에서 증명했다.

상류 형식화 [`FormalConjectures/OEIS/111291.lean`](upstream/111291.lean)
(google-deepmind/formal-conjectures, 커밋 `c094b979`, 2026-10-23)은 이를
`colton_conjecture`로 진술하고 분류를 `research open`으로 두었으며, docstring에는 Zelinsky의
경계 아래 구간이 미해결이라고 적혀 있다.

2026-10-24의 검색(refactorable 수, tau 수, 콜턴 추측에 관한 OpenAlex·arXiv 질의와 Zelinsky
논문을 인용한 OpenAlex 문헌 목록)에서는 Colton(1999), Zelinsky(2002), 그리고 다항식에 상대적인
$\tau$-수를 다룬 Abel, Lauer, Redi(Acta Comment. Univ. Tartu. Math. 25 (2021))를 찾았다. 이 중
어느 것도 $7.42\cdot 10^{13}$ 아래 구간을 해결하지 않는다. 이는 검색에서 찾지 못했다는 결과일
뿐 문헌 조사나 새로움의 주장이 아니다. 이 증명은 검토를 받지 않았고 OEIS, 상류 저장소, 그 밖의
어떤 곳에도 보고하지 않았다(외부 제출에는 사람의 승인이 필요하다).

## 증명 개요

| 범위 | 방법 | 재실행 |
|---|---|---|
| $n\le 10^6$ | 약수 개수 체 | `python3 verify_small.py` (CI) |
| $10^6\le n\le 1.13\cdot 10^{13}$ | $\pi(x_{i+1})\le 2T(x_i)$를 만족하는 격자 $x_0<\dots<x_{65}$와 단조성 | `verify_grid.py` + `tau_count.cpp` (CI) |
| $n\ge 10^{12}$ | $28\,653\,696$ 이하의 $p$-생성수 413,980개에 대한 $T(x)\ge\sum_{d\in G}(\pi(x/d)-\pi(P(d)))$, Dusart의 부등식, 정확한 상수 | `verify_tail.py` + `generators.cpp` (CI) |

$p$-생성수란 $2\tau(d)\mid d$인 $d$를 말한다. 이때 $d$를 나누지 않는 모든 소수 $p$에 대해
$dp$는 refactorable이다. $p$를 $d$의 가장 큰 소인수 $P(d)$보다 큰 소수로 제한하면, $n=dp$에서
$d=n/P(n)$이므로 서로 다른 생성수가 주는 곱의 모임이 서로 겹치지 않는다(이 제한이 없으면
$640\cdot 3=384\cdot 5$처럼 겹친다). 그러면 꼬리 부분은 $f$가 증가함수인
$2T(x)-\pi(x)>f(x)-2B$의 꼴이 되고, 스크립트가 정확한 산술로 $f(10^{12})>2B$를
확인한다(여유 약 9.6%).

## 명제의 충실성

[`AgenticConjectures/OeisA111291.lean`](../../AgenticConjectures/OeisA111291.lean)은 상류 파일의
`countRefactorableNat`, `a`, `countRefactorable`을 항(term) 그대로 옮겨 왔고,
`AgenticConjectures.OeisA111291.statement`는 상류 `colton_conjecture`의 명제와 정확히 같다:

```lean
def statement : Prop :=
  ∀ n : ℕ, Nat.primeCounting n ≤ 2 * countRefactorableNat n
```

`countRefactorableNat n`은 `k.divisors.card ∣ k`인 $k\in[1,n]$의 개수이므로 OEIS와 같이 $k=0$을
제외하고, `Nat.primeCounting n`은 $n$ 이하의 소수의 개수이다. 명제는 양변이 모두 0인 $n=0$도
포함하며 뺄셈을 쓰지 않는다. 상류의 모듈 머리말, 속성, `native_decide` 테스트는 옮기지 않았다
(모듈 docstring 참고).

`statement`는 `def … : Prop`으로 남아 있으며 Lean에서 **증명되지 않았고**, 주장하는 상태
`proved`는 여기서 설명한 컴퓨터 보조 증명을 가리킨다. Lean 정리들은 모두 이름공간
`AgenticConjectures.OeisA111291`에 있으며 논증의 구성 요소이다(사실 번호는
[DETAILS.ko.md](DETAILS.ko.md)를 따른다).

| 선언 | 내용 |
|---|---|
| `a_0`, `a_1`, `a_2` | 상류 테스트 $a(0)=1$, $a(1)=4$, $a(2)=16$ (`rfl`) |
| `primeCounting_seven` | $\pi(7)=2T(7)$ (`decide`; F6) |
| `countRefactorableNat_mono` | $T$는 감소하지 않는다(단조) |
| `grid_step` | $\pi(y)\le 2T(x)$이고 $x\le n\le y$이면 $\pi(n)\le 2T(n)$ (F5) |
| `isSquare_of_odd_refactorable` | 홀수 refactorable 수는 제곱수이다 (F1) |
| `two_mul_refactorable_iff` | 홀수 $u$에 대해 $2u$가 refactorable인 것과 $u$가 refactorable인 것은 동치이다 (F2) |
| `refactorable_mul_prime` | $2\tau(d)\mid d$이고 $p$가 $p\nmid d$인 소수이면 $dp$는 refactorable이다 (F3) |
| `card_filter_prime_Ioc` | $(x,y]$에 있는 소수의 개수는 $\pi(y)-\pi(x)$이다 |
| `sum_card_primes_le_count`, `sum_primeCounting_sub_le` | 서로소인 모임 하계 $T(x)\ge\sum_{d\in G}(\pi(x/d)-\pi(P(d)))$ (F4) |

## 기계 검증과 재현

이 디렉터리에서 실행한다(CI는 처음 세 명령을 실행한다).

```bash
python3 verify_small.py
g++ -O3 -std=c++17 tau_count.cpp -o /tmp/oeis_a111291_tau_count && python3 verify_grid.py /tmp/oeis_a111291_tau_count 10000000000000
g++ -O3 -std=c++17 generators.cpp -o /tmp/oeis_a111291_generators && python3 verify_tail.py /tmp/oeis_a111291_generators
```

CI에서 실행하지 않는 추가 검사(Apple M5 Max 기준 시간):

| 명령 | 시간 | 로그 |
|---|---|---|
| `python3 verify_grid.py /tmp/oeis_a111291_tau_count` ($10^{15}$까지의 전체 격자, 0.7 GB) | 2.3분 | `logs/verify_grid_full.log` |
| `g++ -O3 -std=c++17 -pthread colton_sieve.cpp -o /tmp/oeis_a111291_sieve && /tmp/oeis_a111291_sieve 1000000000000 3 logs/sieve_1e12_checkpoints.txt` | 16.3분 | `logs/sieve_1e12.log` |
| `python3 crosscheck_sieve_log.py /tmp/oeis_a111291_tau_count` | 65초 | `logs/crosscheck_sieve_log.log` |
| `python3 spot_check.py /tmp/oeis_a111291_sieve /tmp/oeis_a111291_tau_count` | 4.5분 | `logs/spot_check.log` |
| `python3 crosscheck_primecount.py` (primecount 필요) | 1초 | `logs/crosscheck_primecount.log` |
| `python3 test_bruteforce.py /tmp/oeis_a111291_sieve /tmp/oeis_a111291_tau_count` (numpy 필요) | 13초 | `logs/test_bruteforce.log` |

`logs/tau_count_powers_of_ten.log`에는 $0\le k\le 15$에 대한 $T(10^k)$와 $\pi(10^k)$가 있다.
$k\le 11$의 값은 OEIS 데이터와 일치한다. $a(12)=26\,568\,322\,474$, $a(13)=251\,342\,379\,436$,
$a(14)=2\,388\,671\,712\,980$, $a(15)=22\,789\,342\,999\,100$은 여기서 계산한 값이며 OEIS에
제출하지 않았다.

Lean:

```bash
lake build AgenticConjectures.OeisA111291
```

## 검토자를 위한 메모

- 계산과 Dusart의 부등식은 형식화하지 않았다. mathlib에는 이런 명시적 부등식이 없다.
- $n\le 10^{12}$에서는 서로 독립적인 두 프로그램(구조적 계수기 `tau_count`를 쓰는 격자와 점별
  체)이 각각 명제를 증명한다. $10^{12}$ 이상에서 꼬리 논증은 둘 중 어느 것도 쓰지 않는다. 두
  $T$ 구현은 $10^{12}$까지의 검사점 1433개, $10^{13}$, $7.42\cdot 10^{13}$, $10^{14}$,
  $10^{15}$ 근처의 네 구간, 그리고 $2\cdot 10^7$까지의 전수 계산과 일치하며, $\pi$ 값은
  primecount와 일치한다.
- Zelinsky의 보조정리 9는 제시된 정당화만으로는 성립이 보장되지 않지만, 그의 정리 8은 이에
  의존하지 않는다(DETAILS.ko.md 3.4절).
- 인용한 소수 계량 부등식은 Dusart 논문의 arXiv 판으로만 확인했다.
