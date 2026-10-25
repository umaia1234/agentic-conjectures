[English](README.md) | **한국어**

# OEIS A108864: 1155는 마지막 홀수 항이 아니다

## 결론

[OEIS A108864](https://oeis.org/A108864)는 perfect deficiency
([A109883](https://oeis.org/A109883))가 10 이하인 수들의 수열이다. 이 항목의
유일한 주석은 다음과 같이 묻는다.

> “Is 1155 the last odd number in this sequence?”

답은 **아니다**이다. 홀수

\[
n_0=815634435=3\cdot5\cdot7\cdot11\cdot547\cdot1291
\]

은

\[
\sigma(n_0)=4\cdot6\cdot8\cdot12\cdot548\cdot1292=1631268864=2n_0-6
\]

을 만족하므로 perfect deficiency가 \(6\le10\)이다. 따라서 이 수는 1155 뒤에
오는 항이다. Formal Conjectures의 명제
`OeisA108864.conjecture : ∀ n > 58, Even (a n)`은 거짓이다.
`AgenticConjectures.OeisA108864.not_statement`가 Lean 4에서 그 부정을
증명하며, 독립적인 Python 인증서가 반례를 다시 확인한다.

## 원문 명제

2026-10-24에 확인한 OEIS A108864(개정판 #3, 마지막 수정 2017년 12월 15일,
작성자 Jason Earls, 2005년 7월 12일)의 원문은 다음과 같다.

> Numbers n such that the perfect deficiency of n (A109883) is <= 10.
>
> Is 1155 the last odd number in this sequence?

이 항목의 offset은 1이고 데이터는 61개 항이며
`…, 1012, 1024, 1155, 1188, 1248`로 끝난다. 즉 \(a(59)=1155\)이다.
OEIS A109883(개정판 #28)은 perfect deficiency를 다음과 같이 정의한다.

> Start subtracting from n its divisors beginning from 1 until one reaches a
> number smaller than the last divisor subtracted or reaches the last
> nontrivial divisor < n. Define this to be the perfect deficiency of n.

이 항목의 PARI 프로그램은
`a(n) = {my(r = n); fordiv(n, d, if (r < d, return (r)); r -= d;); 0;}`이다.

[상류 스냅샷](upstream/README.ko.md)(commit
`c094b979118b89adb77cf5f8d923ac9dd2e51b1d`의
`FormalConjectures/OEIS/108864.lean`)의 명제는 다음과 같다.

```lean
def perfectDeficiency (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun m d => if d ∣ n ∧ d ≤ m then m - d else m) n

def A (n : ℕ) : Prop :=
  0 < n ∧ perfectDeficiency n ≤ 10

noncomputable def a (n : ℕ) : ℕ :=
  n.nth A

theorem conjecture :
    ∀ n > 58, Even (a n) := by
  sorry
```

## 증명

**핵심 보조정리.** \(n\ge2\)라 하고, \(s(n)=\sigma(n)-n\)을 \(n\)의 진약수의
합이라 하자. \(s(n)\le n\)이면 `perfectDeficiency n`
\(=n-s(n)=2n-\sigma(n)\)이다.

fold는 \(d=0,1,\ldots,n\)을 차례로 훑으며, 나머지 값은 \(n\)의 약수에서만
바뀐다. 진약수 \(d\)보다 작은 약수가 모두 이미 빼졌다고 하자. 그러면 나머지
값은 \(n-\sum_{d'<d,\ d'\mid n}d'\)이고,
\(\sum_{d'\le d,\ d'\mid n}d'\le s(n)\le n\)이므로 이 값은 \(d\) 이상이다.
따라서 \(d\)도 빼진다. 귀납적으로 모든 진약수가 빼지고 \(n-s(n)\)이 남는다.
\(1\)이 진약수이므로 이 나머지는 \(n\)보다 작고, 마지막 후보 \(d=n\)은
건너뛴다.

**반례.** \(n_0\)은 위의 여섯 소인수를 갖는 제곱 인수 없는 수이다.
곱셈성에 의해
\(\sigma(n_0)=(3+1)(5+1)(7+1)(11+1)(547+1)(1291+1)=1631268864\)이므로
\(s(n_0)=815634429\le n_0\)이다. 보조정리에 의해 perfect deficiency는
\(n_0-s(n_0)=6\)이다. 따라서 `A n₀`가 성립하고 \(n_0\)은 홀수이다.

**색인.** `Nat.nth_count`에 의해 `a (Nat.count A n₀) = n₀`이다. OEIS
데이터의 59개 수 \(1,2,\ldots,1155\)는 \(n_0\)보다 작은 `A`의 원소이며, 이는
상류 fold를 커널에서 평가해 확인한다. 따라서
`Nat.count A n₀ ≥ 59 > 58`이고, `conjecture`는 색인 `Nat.count A n₀`에서
성립하지 않는다.

## Lean 형식화

[`AgenticConjectures/OeisA108864.lean`](../../AgenticConjectures/OeisA108864.lean),
이름공간 `AgenticConjectures.OeisA108864`:

| 선언 | 내용 |
|---|---|
| `perfectDeficiency`, `A`, `DecidablePred A` 인스턴스, `a` | 상류 정의를 항 단위로 그대로 옮긴 것 |
| `statement` | 상류 `conjecture`의 타입: `∀ n > 58, Even (a n)` |
| `foldl_range_eq` | `n`의 진약수 합이 `n` 이하이면, 후보 `0, …, k - 1`(`k ≤ n`)을 처리한 뒤 fold는 `k`보다 작은 약수를 정확히 모두 뺀 상태이다 |
| `perfectDeficiency_eq` | 핵심 보조정리: `2 ≤ n`이고 `∑ d ∈ n.properDivisors, d ≤ n`이면 `perfectDeficiency n = n - ∑ d ∈ n.properDivisors, d` |
| `sigma_one_prime`, `sigma_witness` | 소수 \(p\)에 대해 \(\sigma(p)=p+1\); 곱셈성에 의한 \(\sigma(815634435)=1631268864\) |
| `sum_properDivisors_witness`, `perfectDeficiency_witness`, `A_witness` | 반례의 진약수 합은 815634429, perfect deficiency는 6, 그리고 `A 815634435` |
| `firstTerms`, `firstTerms_spec` | 59개 항 `1, …, 1155`: 서로 다르고, `A`에 속하며, 반례보다 작다(`decide +kernel`) |
| `count_witness`, `a_count_witness` | `58 < Nat.count A 815634435`와 `a (Nat.count A 815634435) = 815634435` |
| `not_statement` | **주정리:** `¬ statement` |

`#print axioms AgenticConjectures.OeisA108864.not_statement`는 `propext`,
`Classical.choice`, `Quot.sound`만 보고한다. 모듈에는 `sorry`도
`native_decide`도 없다. 규모가 있는 커널 평가는 `firstTerms_spec` 하나뿐이며,
약 11,500번의 fold 단계가 든다. 반례 자체에 대해서는 fold를 한 번도 평가하지
않는다.

## 명제 충실성

- **정의.** `perfectDeficiency`, `A`, `DecidablePred A` 인스턴스, `a`는
  같은 `open Nat Finset Int` 아래에서 상류 스냅샷의 항을 그대로 옮겼다.
  `statement`는 상류 `conjecture`의 타입이다. Formal Conjectures 유틸리티
  없이 컴파일하기 위해 다음 세 가지만 바꾸었다.
  - `module`, `public import FormalConjecturesUtil`,
    `@[expose] public section` 대신 `import Mathlib`을 쓴다.
  - 이름공간 앞에 `AgenticConjectures.`를 붙인다.
  - `category`/`AMS` 속성과 다섯 개의 `test` 정리를 뺀다.

  이 변경들은 어떤 명제에도 영향을 주지 않는다. 확인 삼아 상류의 다섯 test
  증명 `a_0`–`a_4`를 속성만 빼고 그대로 로컬 정의에 대해 실행했으며 모두
  통과했다.
- **색인 기준.** `Nat.nth`는 0부터 색인하므로 상류의 `a 58`은 OEIS의
  \(a(59)=1155\)이고, `∀ n > 58`은 “1155 뒤의 모든 항”을 뜻한다. 인증서는
  \(\le1155\)인 항이 정확히 59개임을 확인하여 상류의 `a 58 = 1155`를
  뒷받침한다. Lean 증명에는 이 사실이 필요 없고, 반례보다 작은 항이 59개
  이상이라는 것만 쓴다. `Nat.count A 1155 = 58`을 커널에서 직접 계산하면
  Lean의 기본 heartbeat 한도를 넘으므로, 색인 기준은 Python에서만 확인한다.
- **OEIS 질문의 문자 그대로의 의미.** 색인과 무관하게, `A_witness`와
  \(n_0\)이 홀수이고 \(n_0>1155\)라는 사실만으로 1155가 마지막 홀수 항이
  아님이 바로 나온다.
- **자연수 뺄셈.** fold는 `d ≤ m`이라는 조건 아래에서만 `m - d`를 계산하므로
  뺄셈이 잘리지 않는다. 핵심 보조정리의 `n - ∑ d ∈ n.properDivisors, d`도
  가정 아래에서 진짜 차이다.
- **경계값.** `0 < n`이 0을 제외한다. \(n=1\)에서는 후보 \(d=n=1\)이
  빼지므로 perfect deficiency가 0이 되어 A109883의 \(a(1)=0\)과 일치한다.
  핵심 보조정리가 \(n\ge2\)를 가정하는 이유가 이것이다.
- **상류 fold와 A109883의 비교.** 상류 정의는 나머지보다 큰 약수를 건너뛰고
  계속 진행하지만, A109883의 PARI 프로그램은 그런 약수를 처음 만나면 멈춘다.
  약수를 오름차순으로 훑고 나머지가 절대 늘지 않으므로, 한 약수를 건너뛰면
  그 뒤의 약수도 모두 건너뛰게 되어 두 정의는 일치한다. 인증서는
  \(1\le n\le2000\)에서 두 정의가 일치함을 확인하고 OEIS 데이터 61개 항을
  모두 재현한다. 반박 자체는 상류 정의만 사용하며, \(n_0\)에 대해서는 두
  정의 모두 6을 준다.

## 기계 검증과 재현

저장소 루트에서 다음을 실행한다.

```bash
lake build AgenticConjectures.OeisA108864
python3 problems/oeis-a108864/a108864_certificate.py
```

2026-10-24에 Apple M5 Max에서(Mathlib은 이미 빌드된 상태) 모듈 컴파일은 약
7초, 인증서 실행은 약 0.15초 걸렸다.

[인증서](a108864_certificate.py)는 Python 표준 라이브러리만 사용하며 Lean
증명과 독립적이다. 인증서는 다음을 수행한다.

- Lean의 `0 ∣ n ↔ n = 0`까지 포함해 상류 fold를 문자 그대로 옮기고,
  \(1\le n\le2000\)에서 A109883의 PARI 프로그램과 비교한다.
- 1248 이하의 OEIS 데이터 항, 0부터 센 색인 기준 \(a(58)=1155\), Lean의
  `firstTerms` 목록을 다시 계산한다.
- \(n_0\)을 시행 나눗셈으로 소인수분해하고, 여섯 소인수가 소수임을 시행
  나눗셈으로 증명하며, 64개 약수를 서로 독립적인 두 방법으로 나열하고,
  \(\sigma(n_0)=\prod_{p\mid n_0}(p+1)=2n_0-6\)을 확인한다.
- 두 정의 아래에서 \(n_0\)의 perfect deficiency를 계산하고, 홀짝성과 색인
  하한을 확인한다.

## 주장하지 않는 것

- \(n_0\)의 정확한 색인, 즉 `Nat.count A 815634435`의 값은 결정하지 않는다.
  증명한 것은 하한 \(>58\)뿐이다.
- \(n_0\)이 1155 다음의 가장 작은 홀수 항이라고 주장하지 않는다.
- A108864의 홀수 항이 유한한지 무한한지에 대해서는 아무것도 주장하지 않는다.

## 선행 연구와 제출 상태

\(\sigma(n_0)=2n_0-6\)이라는 산술적 사실은 오래전부터 알려져 있다. \(n_0\)은
[A087485](https://oeis.org/A087485)(\(2m-\sigma(m)=6\)인 홀수 \(m\)),
[A141548](https://oeis.org/A141548)(deficiency 6),
[A077374](https://oeis.org/A077374)(\(|\sigma(m)-2m|\le10\)인 홀수 \(m\)),
[A088012](https://oeis.org/A088012)에 실려 있다. 핵심 보조정리가 있으면
A108864에 속한다는 사실은 한 줄로 따라 나온다. 2026-10-24 현재 A108864
항목은 여전히 같은 질문을 던지고 있다. 815634435를 포함하는 OEIS 항목 15개
가운데 A108864를 언급하는 것은 없으며, A108864를 상호 참조하는 다른 항목도
없다. 이 검색 결과가 새로움의 증거는 아니다. 이 결과는 검토되지 않았고,
새로움을 주장하지 않으며, OEIS, Formal Conjectures, 그 밖의 어떤 외부
채널에도 제출하지 않았다. 외부 제출에는 사람의 승인이 필요하다.
