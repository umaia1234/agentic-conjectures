[English](README.md) | **한국어**

# 에르되시 문제 #307 검토

이 디렉터리는 유한 소수 집합 `P,Q`에 대한 다음 질문의 증명 검토와 정확한
계산을 담고 있습니다.

\[
\left(\sum_{p\in P}\frac1p\right)
\left(\sum_{q\in Q}\frac1q\right)=1
\]

문제는 여전히 미해결이며, 여기의 어떤 내용도 해답이나 새로움의 증명으로
제시하지 않습니다.

## 주요 결과

- 강제 항등식 `A(P)=M(Q)`, `A(Q)=M(P)`와 서로소성(disjointness)을 기약분수로부터
  다시 증명합니다.
- `U=P union Q`의 모든 홀수 `r`에 대해, 반대쪽 소수곱으로 제곱근을 명시하여
  더 강한 국소 조건 `(M(U)/r | r)=1`을 유도합니다.
- 이 기호들을 곱하면 모든 부호를 포함해 다음이 확인됩니다.
  - `2 notin U`이면 `3 mod 4`인 소수의 개수 `u`는 `0 또는 1 mod 4`입니다.
  - `2 in U`이면 `v+binom(u,2)`는 짝수입니다. 여기서 `v`는 `3 또는 5 mod 8`인
    홀수 소수의 개수입니다.
- `r=2`의 합동식은 따로 분리해 다루며, 분모가 2인 Legendre 기호는 쓰지
  않습니다.
- 분할에 의존하는 mod-8 조건과 합집합만으로 정해지는 mod-8 조건을
  증명합니다. 3이 없으면 이 조건들은 더 강한 mod-24 조건으로 올라갑니다.
- 정확한 열거로 59개 소수의 합집합을 배제합니다. 역수 질량이 충분한 집합은
  49,961개이고, 값싼 mod-8 및 종합 상호법칙 필터를 통과하는 것은 6,149개이며,
  모든 국소 Legendre 조건을 만족하는 것은 없습니다. 따라서
  `|P union Q|>=60`이며, 이는 현재 데이터베이스의 서술과 일치합니다.
- 느린 정확한 열거로 처음 66개 소수 위에 놓인 가능한 합집합 644,666개를
  검사합니다. 별도로 구성한 캐시 기호 열거는 이를 처음 68개 소수로 넓혀,
  역수 조건을 만족하는 합집합 9,926,250개를 검사하며 국소 조건을 통과하는
  것은 없습니다. 따라서 새로움을 주장하지 않고 `max(P union Q)>=347`을
  얻습니다.
- **2026-10-24 갱신.** 중간 만남(meet-in-the-middle) 탐색으로 유계 지지 배제를
  처음 90개 소수까지 넓힙니다. 463 이하 소수에 포함되는 어떤 합집합도 역수
  질량, 크기, 국소 Legendre 조건을 함께 통과하지 못하므로
  `max(P union Q)>=467`입니다. 따로 작성한 두 번째 구현이 경계 계산의 개수를
  재현하고, 그 전수 탐색 모드는 76개 소수까지 모든 후보 합집합을 직접
  검사합니다.
- 같은 갱신에서 두 번째 구현으로 59개 소수 배제를 다시 실행하고(이제 CI에서
  실행), 강제 항등식, 국소 제곱/Legendre 조건, mod-8/mod-24 및 홀짝 조건,
  그리고 `|P union Q|>=59`를 Lean 4로 형식화합니다
  (`AgenticConjectures/Erdos307.lean`, `native_decide` 없이 커널 검증).

전체 논증은 `PROOF.md`에 있습니다.

## 90개 소수까지의 유계 지지 (2026-10-24)

**결과.** `F_90`을 처음 90개 소수 `2,...,463`이라 합시다. 다음을 모두 만족하는
`U ⊆ F_90`은 없습니다.

1. `sum_{r in U} 1/r >= 2`,
2. `|U| >= 60`,
3. `U`의 모든 홀수 `r`에 대해 `prod_{s in U, s != r} (s|r) = 1`.

모든 해 `(P,Q)`는 이런 `U=P union Q`를 줍니다. 조건 1과 조건 3은 Lean
정리(`two_lt_sum_inv_union`, `prod_jacobiSym_eq_one`)이고, 조건 2는 정확한
59개 소수 배제입니다. 따라서 모든 해는 463 다음 소수인 467 이상의 소수를
포함합니다. 이는 이전의 계산적 하한 `max(P union Q)>=347`을 대체합니다.

**방법.** `support_mitm.cpp`(C++17, `std::thread`)는 제거 집합 `R=F_90-U`를
정수 산술로 열거합니다. 조건 3은 GF(2) 위에서 선형이므로, 탐색은 먼저 가장
작은 홀수 소수 33개(*키*)에서 이 조건을 맞추고, 제거 가능한 소수의 두 절반
표를 키 조회로 결합한 뒤, 키가 맞는 모든 집합에 전체 조건을 검사합니다.
환원, 예산 산술, 그리고 각 제거 집합이 정확히 한 번 생성되는 이유는
`PROOF.md` 6절 "Meet-in-the-middle extension to 90 primes"에 적혀 있습니다.

| `K` | 최대 소수 | 키 크기 | 키가 맞는 제거 집합 | 생존 | 실행 시간 |
|---:|---:|---:|---:|---:|---:|
| 80 | 409 | 30 | 16,626 | 0 | 2.9 s (1 스레드) |
| 84 | 433 | 30 | 1,054,762 | 0 | 33.6 s (1 스레드) |
| 86 | 443 | 31 | 4,454,518 | 0 | 119.7 s (1 스레드) |
| 88 | 457 | 32 | 18,447,093 | 0 | 171.4 s (3 스레드) |
| 90 | 463 | 33 | 75,000,754 | 0 | 752.7 s (3 스레드) |

어떤 실행에서도 모호한 예산 경우가 보고되지 않았으므로 키가 맞는 집합의
개수는 정확합니다. `K=88`과 `K=90` 실행은 부하가 큰(load average 40–70) 공유
18코어 Apple 기기에서 이루어졌고, `K=90` 실행은 CPU 시간 1,542 s와 메모리
3.4 GB를 썼습니다. `K=80`–`86` 행은 같은 기기에서 더 낮은 부하로 다시 실행한
단일 스레드 결과입니다.

**교차 검증.** `cross_check_support.py`는 따로 작성한 구현(numba)입니다.
이차잉여 표, 행 비트집합, 정확한 `Fraction` 예산, 정렬된 표, 반대 방향의
절반 분할, 다른 무게 경계를 사용합니다.

- `brute` 모드는 키 없이 모든 제거 집합을 열거합니다. 이전 스크립트의 정확한
  총수 644,666(`K=66`)과 9,926,250(`K=68`)을 재현하고, `K=76`의 후보 합집합
  128,295,786,172개 전체를 529 s(3 스레드)에 검사합니다. 생존자가 없으므로
  이것만으로도 독립적으로 `max(P union Q)>=389`를 줍니다.
- 66부터 76까지의 모든 짝수 `K`와 `{12,16,20,24,30}`의 모든 키 크기에서
  `brute`와 `support_mitm.cpp`의 키가 맞는 집합 개수가 정확히 일치합니다
  (30회 비교).
- `mitm` 모드는 `K=84`와 `K=90`의 키가 맞는 집합 개수와 `|R|`별 분포를
  재현하고, 생존자를 찾지 못합니다(`K=90`: 부하 아래 3 스레드로 1,578 s,
  6.9 GB).
- `fiftynine` 모드는 역수 조건을 만족하는 59개 소수 합집합 49,961개를 다시
  열거하고(교체 개수별 개수가 `enumerate_59.py`와 같음), 어느 것도 국소 조건을
  통과하지 않음을 확인합니다.

모든 개수와 시간은 `bounded_support_90_result.json`에 기록되어 있습니다.

**주장하지 않는 것.** 이것은 유한한 컴퓨터 배제이며 비존재 증명이 아닙니다.
`|U|>=60`은 정확한 59개 소수 열거에 의존합니다. 두 탐색 구현은 수학적 환원과
중간 만남 설계를 공유합니다. 다른 알고리즘인 전수 탐색 모드는 76개 소수까지만
닿습니다. 같은 방법으로 `|P union Q|>=61`을 얻는 것은 불가능합니다. 역수 질량
조건만으로는 60개 소수 합집합의 최대 소수가 유계가 되지 않으므로, 그 경우에는
유한한 후보 목록이 없습니다. 두 하한 모두 새로움을 주장하지 않습니다.

## 재현

정확한 무작위/장난감 검토를 실행합니다.

```bash
python3 problems/erdos-307/test_identities.py
```

이 스크립트는 무작위 소수 상호법칙 항등식 2,000개, 쌍마다 서로소인 합성수
Jacobi 항등식 1,000개(절반은 2를 포함), 정확한 강제 동치 2,000개, 그리고
일반화된 장난감 해 세 개를 결정론적으로 검사합니다. 가장 큰 장난감 해는
진짜 합성수 분모 `1805=5*19^2`를 포함합니다.

\[
\left(1+\frac1{1805}\right)
\left(\frac12+\frac13+\frac17+\frac1{43}\right)=1.
\]

유한 배제를 실행합니다.

```bash
python3 problems/erdos-307/enumerate_59.py
python3 problems/erdos-307/enumerate_bounded_union.py
python3 problems/erdos-307/enumerate_bounded_support_fast.py \
  --prime-count 68
```

이 스크립트들은 Python 표준 라이브러리와 정확한 정수/Fraction 산술만
사용합니다. 기대 요약값은 `enumeration_59_result.json`,
`bounded_union_result.json`, `bounded_support_68_result.json`에 정리되어
있습니다. 66개 소수에서는 느린 곱 기반 구현과 캐시 비트집합 구현이 모든
열에서 같은 개수를 줍니다. 67개 소수의 캐시 결과도 느린 구현으로
재현했고, 결정론적으로 고른 68개 소수 부분집합 5,000개를 두 국소 기호
공식으로 검사했습니다.

90개 소수 배제와 그 교차 검증을 실행합니다(`problems/erdos-307`에서 실행하며,
`brute`와 `mitm` 모드에는 numpy와 numba가 필요합니다).

```bash
mkdir -p build && g++ -O3 -std=c++17 -pthread support_mitm.cpp -o build/support_mitm
build/support_mitm 80 --threads 2               # 수 초; CI에서도 실행
build/support_mitm 90 --key 33 --threads 3      # 부하 아래 약 13분, 3.4 GB
python3 cross_check_support.py fiftynine        # 0.7 s, 표준 라이브러리만 사용; CI
python3 cross_check_support.py brute --K 76 --keys 12,16,20,24,30 --threads 3  # 529 s
python3 cross_check_support.py mitm --K 90 --key 33 --threads 3     # 약 26분, 6.9 GB
```

각 명령은 JSON 객체 하나를 출력하고, 생존자가 없을 때에만 상태 0으로
종료합니다.

제안된 소수 쌍을 검사하려면 예를 들어 다음을 실행합니다.

```bash
python3 problems/erdos-307/exact_checker.py \
  --P 2,5,11 --Q 3,7,13
```

보고서에는 정확한 역수합, 강제 항등식, 모든 교차 합동식과 국소 Legendre
기호, 상호법칙 개수, 홀짝성, mod-8, 조건부 mod-24, 그리고 알려진 합집합
제곱 항등식이 포함됩니다.

## FormalConjectures 상류

정확한 Lean 명제와 변경 불가능한 출처 메타데이터는 로컬
[상류 스냅숏](upstream/README.md)에 보존되어 있습니다. 주 선언은 여전히
`sorry`에 기댄 미해결 명제이며, 여기의 더 강한 유한 배제도 이를 해결하지
않습니다.

## Lean 형식화

`AgenticConjectures/Erdos307.lean`은 상류 명제의 모든 증인(witness)에 대해
초등적 필요조건을 증명합니다. 여기서 `M S = ∏ p ∈ S, p`이고
`A S = ∑ p ∈ S, ∏ q ∈ S.erase p, q`이므로 `∑ p ∈ S, 1/p = A S / M S`입니다.

| 선언 | 내용 |
|---|---|
| `statement` | 상류 `erdos_307`의 우변을 그대로 옮긴 것 |
| `IsSolution P Q` | 그 존재 명제의 본문 |
| `forcing`, `isSolution_of_forcing` | `IsSolution P Q ↔` (소수 조건과 `A P = M Q ∧ A Q = M P`) |
| `statement_iff_forcing` | `statement ↔ ∃ P Q`, `A P = M Q ∧ A Q = M P`인 소수 집합 |
| `disjoint_of_isSolution` | `Disjoint P Q` |
| `union_identity` | `A (P ∪ Q) = M P ^ 2 + M Q ^ 2` |
| `two_lt_sum_inv_union` | `2 < ∑ r ∈ P ∪ Q, 1/r` |
| `isSquare_prod_erase` | `r ∈ P ∪ Q`이면 `∏ ((P ∪ Q).erase r)`는 `ZMod r`에서 0이 아닌 제곱수 |
| `prod_jacobiSym_eq_one` | `∏ s ∈ (P ∪ Q).erase r, J(s \| r) = 1` |
| `even_card_nonresidues` | `J(s \| r) = -1`인 `s ∈ (P ∪ Q).erase r`의 개수는 짝수(탐색의 가지치기 규칙) |
| `sum_cast_eq_M`, `sum_cast_eq_of_two_mem` | 소수들의 제곱이 1인 임의의 법에서의 (8a)–(8d) |
| `mod_eight`, `mod_eight_of_two_mem` | 법 8에서의 (8a)–(8d) |
| `mod_twentyFour`, `mod_twentyFour_of_two_mem` | `3 ∉ P ∪ Q`일 때의 mod-24 조건 |
| `odd_card_of_two_not_mem`, `even_card_of_two_mem` | 홀짝 제약 |
| `card_union_ge_59` | `59 ≤ #(P ∪ Q)` |

`2 ∈ Q`인 경우는 `IsSolution.symm`으로 얻습니다. `59` 하한은 임의의 58개
소수를 처음 58개 소수와 비교하고, 후자에 대한 `∑ 1/p < 2`를 자연수 부등식으로
바꾸어 `decide +kernel`로 계산합니다. `native_decide`는 쓰지 않습니다.
`#print axioms`에는 `propext`, `Classical.choice`, `Quot.sound`만 나타납니다.

**명제 충실성.** `statement`와 `IsSolution`은 상류 명제를 그대로
옮깁니다. 증인은 `Finset ℕ`이고, 원소에 대한 가정은 `Nat.Prime`이며, 등식
`1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)`은 `ℚ`에서 성립합니다. 다른
정의나 경계 관례는 개입하지 않으며, 모든 정리는 이 등식의 결과입니다.
`card_union_ge_59`는 상류 `erdos_307.barrier`의 왼쪽 연언입니다. 상류는
`Q.Nonempty`도 가정하지만 이는 등식에서 이미 따라 나오며, 오른쪽 연언(`∏ P`의
하한)은 여기서 형식화하지 않습니다. `erdos_307`의 `answer(sorry)`는 건드리지
않습니다. 계산적 하한 `|P union Q|>=60`과 `max(P union Q)>=467`은
형식화하지 않았습니다.

## AlphaProof Nexus 벤치마크 출처

Google DeepMind의 AlphaProof Nexus `science-submission` 스냅숏(커밋
[`0647711a71183c1ea492ad60860776617ce1ea88`](https://github.com/google-deepmind/alphaproof-nexus-results/tree/0647711a71183c1ea492ad60860776617ce1ea88))은
변경 불가능한
[시도 문제 목록](https://github.com/google-deepmind/alphaproof-nexus-results/blob/0647711a71183c1ea492ad60860776617ce1ea88/erdos_problems_attempted.txt)에
`erdos_307`과 `erdos_307.variants.coprime_one_notMem`을 모두 올려 두었습니다.
그 스냅숏에서 `APNOutputs/ErdosProblems`와 `NaturalLanguageProofs/ErdosProblems`
어느 쪽에도 #307의 결과는 없습니다. 따라서 이것은 시도의 출처일 뿐 증명이나
반례가 아닙니다. 특히 여기서 검사한 쌍마다 서로소인 합성수 장난감 해 세 개는
모두 `1`을 포함하므로 `1 notin P union Q`를 요구하는 변형을 해결하지 않습니다.

## 문헌 검토

확인한 일차 및 준일차 출처는 다음과 같습니다.

- Erdős와 Graham의 1980년 단행본은 인쇄본 38쪽 아래에서 이 질문을 제시하고
  Barbeau에게 돌립니다:
  <https://www.math.ucsd.edu/~ronspubs/80_11_number_theory.pdf>
- 현재 문제 페이지는 이를 미해결로 올리고 `|P union Q|>=60`을 적고 있습니다:
  <https://www.erdosproblems.com/307>
- I. O. Bado, *Structural Constraints for an Erdős Unit-Fraction Problem over
  Primes*, 저자 업로드 프리프린트, 2026년 5월, DOI
  `10.13140/RG.2.2.32245.54245`:
  <https://www.researchgate.net/publication/404719794_STRUCTURAL_CONSTRAINTS_FOR_AN_ERDOS_UNIT-FRACTION_PROBLEM_OVER_PRIMES>
  이 문헌에는 이미 강제 정리, 교차곱/국소 영합 합동식, 홀짝 제약, 정확한 한쪽
  판정, 합집합 판별식/피타고라스 항등식이 들어 있습니다. 프리프린트이며
  페이지에는 인용이 보고되어 있지 않습니다.
- 2019년 MathOverflow 토론은 단행본의 위치와 역수합에서 바로 나오는 하한
  `|U|>=59`를 기록합니다:
  <https://mathoverflow.net/questions/320838/product-of-sum-of-reciprocals-of-prime-numbers>

이 문제를 “Legendre symbol”, “quadratic reciprocity”, “mod 8”과 함께 정확한
구문으로 검색했을 때, 2026-08-11 기준으로 관련된 일차 출처를 더 찾지
못했습니다. 이는 제한된 증거일 뿐이며, 상호법칙, mod-8, mod-24, 열거
정식화는 더 넓은 전문가 문헌 검토 없이 새롭다고 불러서는 안 됩니다.
