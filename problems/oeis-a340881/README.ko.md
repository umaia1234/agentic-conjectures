[English](README.md) | **한국어**

# OEIS A340881

[OEIS A340881](https://oeis.org/A340881)의 두 모듈러 주기성 추측을
모든 법 \(m\ge2\)에 대해 해결합니다. 수열은

\[
A(n)=\sum_{k=0}^{n-1}2^{k(k+1)/2}
       \prod_{j=k+1}^{n-1}(2^j-1),\qquad n\ge1
\]

로 정의합니다.

## 결과

- 홀수 \(m>1\)과 \(L=\operatorname{ord}_m(2)\)에 대해
  \(A(n+2L)\equiv A(n)\pmod m\)가 모든 \(n\ge1\)에서 성립합니다.
  즉 홀수 합성수까지 처음부터 시작하는 명시적 주기를 얻습니다.
- 소수 \(p\)에 대한 최소주기는 \(2(p-1)\)의 약수입니다. \(p=2\)에서는
  \(A(n)\equiv1\pmod2\)입니다.
- \(m=2^eu\), \(u\) 홀수로 쓰면 모든 \(m\ge2\)에서 궁극 주기성을
  얻습니다. \(u>1\)일 때 \(2\operatorname{ord}_u(2)\)가
  \(n\ge\max(1,e)\)에서 한 주기이고, \(u=1\)일 때 주기 2가
  \(n\ge e\)에서 성립합니다.

## 문서와 인증서

- [상세 증명](PROOF.ko.md)
- [검증·재현 기록](VERIFICATION.ko.md)
- [실행 가능한 인증서](a340881_certificate.py)

저장소 루트에서 다음과 같이 재검산할 수 있습니다.

    python3 -m py_compile problems/oeis-a340881/a340881_certificate.py
    python3 problems/oeis-a340881/a340881_certificate.py

## Lean 형식 증명

[`AgenticConjectures/OeisA340881.lean`](../../AgenticConjectures/OeisA340881.lean)은
`sorry`, 추가 공리, `native_decide` 없이 다음을 증명합니다.

```text
statement1_holds : statement1     -- 추측 1, 최소주기 조건 포함
statement2_holds : statement2     -- 추측 2
oeis_340881_conjecture_0 :        -- 상류 명제 그대로
  ∀ p, p.Prime → ∀ n ≥ 1, a (n + 2 * (p - 1)) % p = a n % p
period_odd :
  Odd m → 0 < ord m ∧ ∀ n ≥ 1, a (n + 2 * ord m) ≡ a n [MOD m]
modEq_two_pow_mul_odd :
  Odd u → max 1 e ≤ n → a (n + 2 * ord u) ≡ a n [MOD 2 ^ e * u]
eventually_periodic :
  0 < m → ∃ N T, 0 < T ∧ ∀ n ≥ N, a (n + T) % m = a n % m
```

여기서 `ord m`은 `orderOf (2 : ZMod m)`의 줄임입니다. 증명은
[상세 증명](PROOF.ko.md)을 따릅니다. 보조정리 1.1은 `A_add_two_mul`,
보조정리 1.2는 `dvd_of_minimal`, 보조정리 1.4는 `A_succ`, 보조정리 1.5는
`A_succ_two_pow`와 `modEq_two_pow`, 정리 1.6은 `modEq_two_pow_mul_odd`입니다.
§1.4의 두 단계는 더 짧게 처리했습니다. 홀수 \(p\)에서는 \(2^{p-1}=1\)을
보조정리 1.1에 바로 넣어 \(2(p-1)\) 자체가 주기임을 얻으므로, 보조정리 1.2만으로
최소주기를 제한하고 \(\operatorname{ord}_p(2)\mid p-1\)은 쓰지 않습니다.
\(p=2\)에서는 \(A(n)\equiv1\pmod2\) 대신 \(e=1\)인 보조정리 1.5에서 주기 2를
얻습니다.

    lake build AgenticConjectures.OeisA340881
    python3 scripts/check_axioms.py

## 명제 충실성

- OEIS 추측 1은 소수 \(p\)를 법으로 수열이 “purely periodic with minimum
  period dividing 2*(p - 1)”이라고 말합니다. `statement1`은 순수 주기성을
  오프셋 \(n=1\)부터의 주기성으로 읽고, 양의 주기가 존재하며 더 작은 양의
  주기가 없는 모든 양의 주기가 \(2(p-1)\)을 나눈다고 진술합니다.
- OEIS 추측 2는 합성수 \(n\)을 법으로 한 궁극 주기성입니다. `statement2`는
  그 제한을 그대로 두고, `eventually_periodic`은 모든 \(m\ge1\)에 대해 이를
  증명합니다.
- `a`는 상류 정의를 항 하나하나 그대로 옮긴 것입니다.
  `Nat.choose (k + 1) 2`는 \(k(k+1)/2\)이고, \(2^j\ge1\)이므로 자연수 뺄셈
  `2 ^ j - 1`은 정확합니다. 처음 열 항은 OEIS 데이터
  \(1,3,17,183,3769,\ldots\)와 일치합니다. `a 0 = 0`은 오프셋 앞에 있으며
  어떤 명제에도 제약되지 않습니다.
- `orderOf (2 : ZMod m)`은 홀수 \(m\)을 법으로 한 2의 곱셈적 위수이며,
  `orderOf_two_pos`가 이것이 양수임을 보입니다.
- \(e\ge1\)인 \(m=2^e\)에 대해 상세 증명은 \(n\ge e\)부터 주기 2를 말합니다.
  \(\operatorname{ord}_1(2)=1\)이고 \(\max(1,e)=e\)이므로 \(u=1\)인
  `modEq_two_pow_mul_odd`가 같은 내용을 줍니다.

## 연구 상태

2026-08-11 당시 OEIS 원문은 두 명제를 “Conjecture”로 표시하고 있었습니다.
정확한 식·초기항·핵심 주기식으로 공개 웹, arXiv, GitHub를 대조했으나 같은
공개 증명을 찾지 못했다는 것이 당시의 감사 기록입니다. 이는 음성 검색 결과일
뿐이며, 이 증명은 아직 동료 심사나 OEIS 편집자의 확인을 거치지 않았습니다.

## 상류 Lean 형식화

FormalConjectures의 [원문 스냅샷과 출처 기록](upstream/README.md)을
[`340881_294a5574.lean`](upstream/340881_294a5574.lean)에 보존했다. 소수
법의 주기를 적은 정리는 `by sorry`인 **추측 statement**이지 형식 증명이 아니다.
이 폴더의 모든 법에 대한 더 강한 결과는 해당 Lean 스냅샷에 형식화되어 있지 않다.
이 저장소의 자체 모듈([위](#lean-형식-증명) 참고)은 상류 명제를
`oeis_340881_conjecture_0`이라는 이름으로 그대로 증명한다. 스냅샷 파일 자체는
바꾸지 않았다.
