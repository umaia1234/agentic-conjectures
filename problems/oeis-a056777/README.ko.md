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

## 원문 상태와 검증 범위

- 2026-07-22의 [Choudhury–Wei 논문 v3, Conjecture
  1.1](https://arxiv.org/abs/2606.10331v3)은 이 문제를 명시적으로 open으로
  두었다. 논문의 Theorem 2.2는 \(n,n+12\)가 모두 서로 다른 두 소수의
  곱인 경우를 판정하고, Theorem 3.1은 \(n\) 자체가 소수 거듭제곱인
  경우를 배제한다.
- 저자들은 공개한 [OpenMP
  코드](https://github.com/bvrtoverfitprimes/integersequencetesting/blob/main/search_omp.cpp)로
  정확히 \(2\le n<10^{12}\)을 검사해 얻은 166개 해가 모두 예상한
  형태라고 보고했다. 이는 출처가 보고한 계산이며 이 작업에서 그 범위를
  독립 재실행했다는 뜻이 아니다.
- 이 폴더에는 계산 인증서가 없다. 결과는 유한 탐색에 의존하지 않고
  [PROOF.md](PROOF.ko.md)의 초등 정수론 논증으로 모든 소수 거듭제곱
  \(n+12\)을 배제하며, 그 논증은 아래의 Lean 모듈로 기계 검증된다
  (CI가 no-`sorry` 게이트와 공리 감사를 거쳐 다시 빌드한다).
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

재현(저장소 루트에서; `lake build`와 `check_axioms.py`는 mathlib 캐시
`lake exe cache get`이 필요하다):

```bash
lake build AgenticConjectures.OeisA056777   # 이 모듈만, mathlib 캐시가 있으면 약 20초
lake build                                  # 라이브러리 전체 (check_axioms.py에 필요)
python3 scripts/check_sorry.py
python3 scripts/check_axioms.py             # propext / Classical.choice / Quot.sound만 허용
```

## 상류 Lean 형식화

감사에 사용한 FormalConjectures 원문과 고정 출처는
[upstream 기록](upstream/README.md) 및 [`56777.lean`](upstream/56777.lean)에
보존했다. 중심 추측은 `by sorry`로 닫힌 **statement**이지 형식 증명이 아니며,
이 폴더의 `n+12` 소수거듭제곱 배제 정리는 그 상류 파일에는 형식화되어 있지
않다 — 위에 적은 이 저장소 자체의 모듈에 들어 있으며, (독립 빌드가 불가능한)
스냅샷을 import하는 대신 상류 술어를 항 단위로 그대로 다시 적는다.
