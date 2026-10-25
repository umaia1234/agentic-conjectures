[English](README.md) | **한국어**

# OEIS A056777 / Choudhury–Wei Conjecture 1.1

## 부분정리

원 추측은 합성수 \(n\ge4\)가

\[
\varphi(n+12)=\varphi(n)+12,
\qquad
\sigma(n+12)=\sigma(n)+12
\]

을 동시에 만족하면

\[
n=p(p+8),
\qquad p,p+2,p+6,p+8\text{ all prime}
\]

인지 묻는다. 이 폴더에서는 다음을 증명한다.

> 위 두 식을 만족하는 합성수 \(n\ge4\)에 대해 \(n+12\)는 소수
> 거듭제곱일 수 없다.

자세한 불변량과 모든 소수별 경우 분류는 [PROOF.md](PROOF.ko.md)에 있으며,
이 정리는 [`AgenticConjectures/OeisA056777.lean`](../../AgenticConjectures/OeisA056777.lean)에서
**Lean 4로 커널 검증**되어 있다([아래](#lean-4-형식화) 참조).
이 결과는 논문이 이미 배제한 “\(n\)이 소수 거듭제곱”인 경우의 반대쪽
끝을 배제하지만 원 추측 전체를 해결하지 않는다. 남은 해는 양쪽 모두
소수 거듭제곱이 아니며, 논문의 semiprime 정리 밖에서는 적어도 한쪽에
서로 다른 소인수가 세 개 이상 있거나 중복 소인수가 있다.

같은 Lean 모듈은 이제 모든 해 \(n\)에 대해 위 문장의 나머지 요소와 제약
하나를 더 커널 검증한다. \(n\) 자체는 소수 거듭제곱이 아니다(논문의
Theorem 3.1). \(n\)과 \(n+12\)가 모두 서로 다른 두 소수의 곱이면 어떤
소수 사중쌍에 대해 \(n=p(p+8)\)이다(논문 Theorem 2.2의 (⇒) 방향이며,
totient 등식만 있으면 된다). 그리고 \(\sigma(n)\)과 \(\sigma(n+12)\)는
짝수, 즉 \(n\)과 \(n+12\)는 모두 제곱수도 제곱수의 두 배도 아니다. 이와
별도로, 두 구현을 사용한 [독립 전수 탐색](#1012까지의-독립-전수-탐색)이
모든 \(n\le10^{12}\)에 대해 추측을 확인하여 저자들이 보고한 탐색을
재현한다. 이는 유한 계산일 뿐 증명이 아니다.

## 원문 상태와 검증 범위

- 2026-07-22의 [Choudhury–Wei 논문 v3, Conjecture
  1.1](https://arxiv.org/abs/2606.10331v3)은 이 문제를 명시적으로 open으로
  두었다. 논문의 Theorem 2.2는 \(n,n+12\)가 모두 서로 다른 두 소수의
  곱인 경우를 판정하고, Theorem 3.1은 \(n\) 자체가 소수 거듭제곱인
  경우를 배제한다.
- 저자들은 공개한 [OpenMP
  코드](https://github.com/bvrtoverfitprimes/integersequencetesting/blob/main/search_omp.cpp)로
  정확히 \(2\le n<10^{12}\)을 검사해 얻은 166개 해가 모두 예상한
  형태라고 보고했다. 아래 [탐색 절](#1012까지의-독립-전수-탐색)은
  독립적으로 작성한 코드로 그 범위(\(10^{12}\) 포함)를 다시 실행하여 같은
  166개 해를 얻었다.
- Lean 결과는 어떤 유한 탐색에도 의존하지 않는다. \(n+12\)의 소수
  거듭제곱 배제는 [PROOF.md](PROOF.ko.md)의 초등 정수론 논증이며, 그
  논증과 추가 제약들은 아래의 Lean 모듈로 기계 검증된다(CI가 no-`sorry`
  게이트와 공리 감사를 거쳐 다시 빌드한다). 탐색은 이와 별개인 유한 계산
  결과이며 자체 로그와 검증 스크립트를 갖는다.
- 같은 공개 부분정리를 2026-08-11 당시 공개 웹, arXiv, 수학 Q&A,
  SeqFan, GitHub에서 찾지 못했으나 이는 음성 검색 결과일 뿐이다.
  동료평가 전에는 신규성을 단정하지 않는다.

## Lean 4 형식화

부분정리는 mathlib만을 사용해 `sorry` 없이
[`AgenticConjectures/OeisA056777.lean`](../../AgenticConjectures/OeisA056777.lean)
(네임스페이스 `AgenticConjectures.OeisA056777`)에 형식화되어 있다.

| 선언 | 내용 |
|---|---|
| `A n` | 상류 술어 `OeisA56777.A`를 항 단위로 그대로 옮긴 것: `¬ n.Prime ∧ 1 < n ∧ φ (n+12) = φ n + 12 ∧ σ 1 (n+12) = σ 1 n + 12` (상류는 `φ`를 `totient`로 표기) |
| `statement` | 미해결인 Choudhury–Wei 추측 1.1, `∀ n, A n → ComesFromPrimeQuadruple n` (`Prop`일 뿐 **증명되지 않음**) |
| `totient_mul_sigma_add_lt_of_not_isPrimePow` | 소수 거듭제곱이 아닌 모든 \(m>1\)에 대한 핵심 부등식 \(\varphi(m)\sigma(m)+m<m^2\) (PROOF.md의 부등식 (7)) |
| `add_twelve_ne_prime_pow` | **주정리**: `A n → q.Prime → n + 12 ≠ q ^ ℓ` |
| `not_isPrimePow_add_twelve` | 같은 내용의 mathlib `IsPrimePow` 형태: `A n → ¬ IsPrimePow (n + 12)` |
| `not_isPrimePow` | 논문의 Theorem 3.1: `A n → ¬ IsPrimePow n` |
| `semiprime_case` | 논문 Theorem 2.2의 (⇒) 방향을 totient 등식만으로: 소수 `p < q`, `p' < q'`에 대해 `n = p * q`, `n + 12 = p' * q'`, `φ (n+12) = φ n + 12`이면 `p' = p + 2 ∧ q' = p + 6 ∧ q = p + 8` |
| `comesFromPrimeQuadruple_of_semiprime` | 같은 내용을 `A n → … → ComesFromPrimeQuadruple n` 형태로 |
| `sq_or_two_mul_sq_of_odd_sigma` | `Odd (σ 1 m) → ∃ k, m = k ^ 2 ∨ m = 2 * k ^ 2` |
| `even_sigma`, `even_sigma_add_twelve` | `A n → Even (σ 1 n)`와 `A n → Even (σ 1 (n + 12))`: \(n\)과 \(n+12\)는 모두 제곱수도 제곱수의 두 배도 아니다 |

진술의 충실성. `A`는 상류 스냅샷에서 항 단위로 그대로 복사했으므로(유일한
표기 차이는 mathlib의 `Nat.totient` 표기 `φ`뿐이다) "합성수 \(n\ge4\)"는
`¬ n.Prime ∧ 1 < n`으로 부호화된다(이는 \(n\ge4\)를 강제한다). 두 등식 모두 `ℕ`에서 덧셈 형태이므로 절단 뺄셈 문제가 없고,
\(\varphi\)는 `Nat.totient`, \(\sigma\)는 `ArithmeticFunction.sigma 1`이다.
"소수 거듭제곱"은 소수 `q`와 임의의 `ℓ`에 대한 `q ^ ℓ`이며(`ℓ = 0`이면
자명), 이는 mathlib의 `IsPrimePow`와 동치다.

Lean 증명은 PROOF.md를 경우별(\(q\ge5\), \(q=3\), \(q=2\))로 따라가되
한 가지를 의도적으로 바꾸었다. \(q=2\)인 경우 "\(\sigma(n)\)이 홀수 ⇒
\(n\)은 제곱수이거나 제곱수의 두 배"를 쓰지 않고, \(n=4w\)(\(w\) 홀수,
\(8\mid w+3\))로 쓰면 두 등식이 \(\varphi(w)=w-3\)과
\(7\sigma(w)=8w+11\)을 준다. \(w\)가 소수 거듭제곱이면
\(\varphi(w)=w-3\)이 \(w=9\)를 강제하지만 \(8\nmid12\)이고, 아니면 핵심
부등식이 \(w\le9\)를 주므로 \(8\mid w+3\)으로 \(w=5\)만 남는데 이는
\(7\sigma(w)=8w+11\)이 배제한다(\(7\nmid51\)). 증명된 정리는 동일하다.

추가 선언과 논문의 대응은 다음과 같다.

- `not_isPrimePow`. 논문의 Theorem 3.1은 어떤 소수 \(p\)와 \(k\ge2\)도
  \(n=p^k\)에서 두 등식을 동시에 만족하지 않는다는 것이다. 이런 \(n\)은
  \(1\)보다 큰 합성수이고 \(k=1\)(소수)은 양쪽 모두에서 제외되므로, 이는
  정확히 `A n → ¬ IsPrimePow n`이다. 증명: \(n=r^{b+2}\),
  \(x=r^{b+1}\)로 두면 \(\varphi(n)\sigma(n)+x=n^2\), \(\varphi(n)+x=n\),
  \(\sigma(n)\ge n+x\)이다. \(n+12\)는 소수 거듭제곱이 아니므로(주정리)
  \(n+12\)에 대한 핵심 부등식을 두 등식으로 다시 쓰면 \(n+12<x\)가
  되는데, \(x<n\)이므로 불가능하다. (논문은 \(n+12\)가 소수 거듭제곱인
  경우를 따로 다루지만 여기서는 주정리가 그 경우를 처리한다.)
- `semiprime_case`, `comesFromPrimeQuadruple_of_semiprime`. 논문의
  Theorem 2.2는 소수 \(p<q\), \(p'<q'\)에 대해 \(n=pq\),
  \(n+12=p'q'\)와 두 등식을 가정하고
  \((p,p',q',q)=(p,p+2,p+6,p+8)\)을 결론짓는다(논문은 \(p\ge5\)도
  적는데, 이는 네 수가 모두 소수라는 데서 따라 나온다). `semiprime_case`는
  totient 등식만 가정하므로 조금 더 강하다. 역방향(⇐)은 상류 정리
  `a_of_comesFromPrimeQuadruple`로 상류 파일에서 증명되어 있으며 여기서
  반복하지 않는다. 증명: totient 등식에서 \(p'+q'=p+q\)를 얻고, 이어
  \(p<p'\)와 \((p'-p)(q'-p)=12\)를 얻는다. \(p'-p<q'-p\)인 인수분해
  가운데 \((1,12)\)는 \(p=2\), \(q'=14\)를 강제하고, \((3,4)\)는
  홀짝성으로 불가능하며, \((2,6)\)이 바로 사중쌍이다.
- `even_sigma`, `even_sigma_add_twelve`(논문에 없는 결과). \(\sigma(n)\)이
  홀수라면 \(\sigma(n+12)=\sigma(n)+12\)도 홀수이므로,
  `sq_or_two_mul_sq_of_odd_sigma`에 의해 \(n\)과 \(n+12\)가 모두
  제곱수이거나 제곱수의 두 배가 된다. 그러면 \(k^2+12=j^2\)는 \(n=4\)를
  강제하는데 4는 A056777에 속하지 않는다(\(\varphi(16)=8\ne\varphi(4)+12\)).
  \(k^2+12=2j^2\)와 \(2k^2+12=j^2\)는 32를 법으로 해가 없고,
  \(2k^2+12=2j^2\)는 8을 법으로 해가 없다(잉여 검사는 `ZMod 32`와
  `ZMod 8` 위의 `decide`).

재현(저장소 루트에서; `lake build`와 `check_axioms.py`는 mathlib 캐시
`lake exe cache get`이 필요하다):

```bash
lake build AgenticConjectures.OeisA056777   # 이 모듈만, mathlib 캐시가 있으면 약 20초
lake build                                  # 라이브러리 전체 (check_axioms.py에 필요)
python3 scripts/check_sorry.py
python3 scripts/check_axioms.py             # propext / Classical.choice / Quot.sound만 허용
```

## 10^12까지의 독립 전수 탐색

> **계산 결과(유한 범위).** \(\varphi(n+12)=\varphi(n)+12\)이고
> \(\sigma(n+12)=\sigma(n)+12\)인 합성수 \(n\le10^{12}\)은
> \(p,p+2,p+6,p+8\)이 모두 소수인 \(n=p(p+8)\) 꼴의 수 166개뿐이며,
> \(65=5\cdot13\)부터 \(967164068009=983441\cdot983449\)까지이다. 따라서
> 추측 1.1은 모든 \(n\le10^{12}\)에서 성립한다.

이는 저자들이 보고한 \(2\le n<10^{12}\) 탐색(166개 해, 모두 예측된
형태)을 그들의 코드를 참고하지 않고 작성한 코드로 재현한 것이며, 166개
항으로 된 OEIS b-file(`b056777.txt`, 2026-10-24 내려받음, SHA-256
`8a4d205fea5761af6deac8c2bf23d709c4e7844e792f48bf8616135376835ccf`)과 항마다
일치한다. 새로운 결과도 증명도 아니며 \(n>10^{12}\)에 대해서는 아무것도
말하지 않는다. 해 목록은 [`a056777_hits.txt`](a056777_hits.txt)에 있고
모두 \(\equiv65\pmod{72}\)이다. 소수 \(n\)은 \(n+12\)도 소수일 때 정확히
두 등식을 만족한다(\(\varphi(p)=p-1\), \(\sigma(p)=p+1\)). A056777은
이들을 제외하므로 프로그램은 그 개수만 센다(`primehits`).

### 프로그램

- **구현 1**, [`a056777_search.cpp`](a056777_search.cpp) (C++17,
  `std::thread`): 구간 분할 인수분해 체. 각 구간에서 모든 \(m\)은 자신의
  홀수 부분에서 시작하고(2-부분의 \(\varphi\), \(\sigma\)는 `ctz`로
  얻는다), 모든 홀수 소수 \(p\le\sqrt{N+12}\)를 \(p\)의 2-진 역원을 이용한
  정확한 나눗셈으로 그 배수들에서 완전히 나누어 낸다. 마지막에 남은
  \(>1\)인 여인수는 하나의 소수이다. 모든 값은 정확한 64비트 정수이다
  (여기서 \(\sigma(m)<2^{43}\)). 연속한 \(n\) \(10^9\)개로 이루어진
  블록마다(블록 \(k\)는 \(k\cdot10^9<n\le(k+1)\cdot10^9\)) 합성수 해, 소수
  해의 개수, 정확한 합 \(\sum\varphi(n)\)과 \(\sum\sigma(n)\), 위치 가중
  해시 \(\sum(\varphi(n)C+\sigma(n))(2n+1)\bmod2^{64}\)
  (\(C=\texttt{0x9E3779B97F4A7C15}\))를 기록한다. 논문이 설명한 일반적인
  방식(여인수와 누적 \(\varphi\), \(\sigma\))을 독립적으로 구현한 것이다.
- **구현 2**, [`a056777_independent.py`](a056777_independent.py) (numba
  커널을 쓰는 Python, `multiprocessing`): 다른 알고리즘인 지수 계수 체.
  구간 안에서 모든 소수 거듭제곱 \(p^k\)(2 포함)의 배수마다 계수기를 1씩
  올리고, 두 번째 패스에서 표로 만든 \(\varphi(p^e)\), \(\sigma(p^e)\),
  \(p^e\)를 곱하며, 마지막 여인수는 \(m\)을 찾아낸 소수 거듭제곱 부분들의
  곱으로 나눈 값이다. 같은 형식의 블록 줄을 출력한다(통계는 numpy로
  계산).
- **닫힌 식**, [`a056777_sums.cpp`](a056777_sums.cpp): 어떤 \(n\)도
  인수분해하지 않고 \(\sum_{n\le x}\sigma(n)=\sum_{d\le x}d\lfloor x/d\rfloor\)를
  계산하고, \(\Phi(x)=\sum_{n\le x}\varphi(n)\)은
  \(\Phi(x)=x(x+1)/2-\sum_{d=2}^{x}\Phi(\lfloor x/d\rfloor)\)로 계산한다.
- **검증 스크립트**, [`a056777_verify.py`](a056777_verify.py) (Python +
  sympy + g++, CI에서 실행): 두 C++ 프로그램을 빌드하고, \(n\le10^6\)에서
  구현 1을 순수 Python 최소 소인수 점화식과 블록마다 비교하며,
  \(n\le10^9\)에서 구현 1을 실행해 해는 소수 사중쌍 값과, 합계는 닫힌
  식과 대조하고, 커밋된 로그를 감사한다(블록들이 빈틈이나 겹침 없이
  \([1,10^{12}]\)를 덮는지, 실행별 합계, 해가 소수 사중쌍 값 및
  `a056777_hits.txt`와 같은지, 모든 실행 경계에서의 닫힌 식, 구현 2와의
  블록별 일치).

### 교차 검증

| 검사 | 범위 | 결과 |
|---|---|---|
| 구현 2가 구현 1의 모든 블록 줄(합성수·소수 해, \(\sum\varphi\), \(\sum\sigma\), 해시)을 재현 | \(n\le10^{11}\), 블록 100개 | 동일 |
| 로그의 합계 \(\sum\varphi(n)\), \(\sum\sigma(n)\) 대 닫힌 식 | \(x=10^{11},\,4\cdot10^{11},\,7\cdot10^{11},\,10^{12}\) | 일치 |
| 로그의 해 대 별도의 소수 체로 구한 \(p(p+8)\) 값 | \(n\le10^{12}\) | 동일(166개) |
| 모든 해를 sympy `totient`, `divisor_sigma`로 재검사 | 166개 | 통과 |
| 로그의 해 대 OEIS b-file | \(n\le10^{12}\) | 동일(166개) |
| 순수 Python 기준 구현 대 구현 1, 블록별(CI) | \(n\le10^6\) | 동일 |

### 실행

모든 실행은 다른 작업과 공유하는 Apple M5 Max(18코어, 실행 중 부하 평균
약 20–140)에서 했다. 구현 1은 Apple clang 21, `g++ -O3 -std=c++17 -pthread`로
빌드했고, 구현 2는 Python 3.12.13, numpy 2.5.4, numba 0.68.0으로 실행했다.

| 로그 | \(n\)의 범위 | 프로그램 | 병렬도 | 실행 시간 |
|---|---|---|---|---|
| [`logs/main_1e11.log`](logs/main_1e11.log) | \(1\)부터 \(10^{11}\)까지 | 구현 1 | 스레드 3개 | 473초 |
| [`logs/main_1e12_part1.log`](logs/main_1e12_part1.log) | \(10^{11}+1\)부터 \(4\cdot10^{11}\)까지 | 구현 1 | 스레드 3개 | 1339초 |
| [`logs/main_1e12_part2.log`](logs/main_1e12_part2.log) | \(4\cdot10^{11}+1\)부터 \(7\cdot10^{11}\)까지 | 구현 1 | 스레드 3개 | 1145초 |
| [`logs/main_1e12_part3.log`](logs/main_1e12_part3.log) | \(7\cdot10^{11}+1\)부터 \(10^{12}\)까지 | 구현 1 | 스레드 3개 | 957초 |
| [`logs/independent_1e11.log`](logs/independent_1e11.log) | \(1\)부터 \(10^{11}\)까지 | 구현 2 | 프로세스 2개 | 1600초 |

실행 당시의 소스 SHA-256: `a056777_search.cpp`
`a49af0162285cdc4f792e6e17d7f68bce4528a6c582ff1fc23b233145854f1d6`,
`a056777_independent.py`
`9a64d87424d43eb558a9dca4f505a7226f6ac7588ef33d77bd12c82f1dc41f75`,
`a056777_sums.cpp`
`ac639d75e41078700ad12e6f60c6121f1af6b9aa1d85fc6041668fb0e5177b95`.

재현(이 디렉터리에서; `build/`는 gitignore 대상이다):

```bash
python3 a056777_verify.py                    # CI 검사, 여기서 약 17초
mkdir -p build
g++ -O3 -std=c++17 -pthread -o build/a056777_search a056777_search.cpp
./build/a056777_search --start 1 --end 100000000000 --threads 3 > build/main_1e11.log
./build/a056777_search --start 100000000001 --end 400000000000 --threads 3 > build/main_1e12_part1.log
./build/a056777_search --start 400000000001 --end 700000000000 --threads 3 > build/main_1e12_part2.log
./build/a056777_search --start 700000000001 --end 1000000000000 --threads 3 > build/main_1e12_part3.log
# 구현 2 (numpy와 numba 필요)
python3 a056777_independent.py --start 1 --end 100000000000 --procs 2 > build/independent_1e11.log
g++ -O3 -std=c++17 -o build/a056777_sums a056777_sums.cpp
./build/a056777_sums 100000000000 400000000000 700000000000 1000000000000   # 약 10초
```

`python3 a056777_verify.py --limit 1000000000000 --threads 3`은 모든
검사와 함께 구현 1을 전체 범위에서 다시 실행하고,
`python3 a056777_verify.py --independent 100000000000 --threads 2`(sympy,
numpy, numba가 있는 Python으로 실행)는 구현 2를 다시 실행해 커밋된 로그와
비교한다.

주장하지 않는 것. 이 탐색은 유한 계산이다. 추측 1.1을 증명하지 않으며
\(10^{12}\) 너머에 대해서는 아무것도 말하지 않는다. 새로운 결과도 아니다.
저자들이 보고한 탐색과 OEIS 데이터를 재현할 뿐이다. 구현 1은 저자들의
프로그램과 같은 일반적인 방식을 따르며, 알고리즘이 다른 구현 2는
\(n\le10^{11}\)만 다루므로 \(10^{11}\) 위에서는 개별 값이 집계로만
(\(4\cdot10^{11}\), \(7\cdot10^{11}\), \(10^{12}\)에서의 닫힌 식 합계)
그리고 해 목록이 별도로 계산한 소수 사중쌍 값과 일치한다는 점을 통해서만
뒷받침된다. 탐색에는 형식(Lean) 인증서가 없으며 컴파일된 코드와
하드웨어에 의존한다. 위의 독립 구현들과 감사가 이 위험을 줄인다.

## 상류 Lean 형식화

감사에 사용한 FormalConjectures 원문과 고정 출처는
[upstream 기록](upstream/README.md) 및 [`56777.lean`](upstream/56777.lean)에
보존했다. 중심 추측은 `by sorry`로 닫힌 **statement**이지 형식 증명이 아니며,
이 폴더의 `n+12` 소수거듭제곱 배제 정리와 추가 제약들은 그 상류 파일에는
형식화되어 있지 않다 — 위에 적은 이 저장소 자체의 모듈에 들어 있으며, (독립 빌드가 불가능한)
스냅샷을 import하는 대신 상류 술어를 항 단위로 그대로 다시 적는다.
