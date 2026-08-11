# OEIS A136433

[OEIS A136433](https://oeis.org/A136433)의 주기계수 비자율 점화식에서
9-lag 상수계수 선형 점화식을 도출합니다. 수열은 \(a_1=11\)과

\[
a_{n+2}=((n\bmod3)+1)a_{n+1}+((n\bmod2)+1)
\qquad(n\ge0)
\]

로 정의됩니다.

## 결과

모든 \(n\ge10\)에 대해

\[
a_n=6a_{n-3}+a_{n-6}-6a_{n-9}
\]

가 성립합니다. 핵심은 세 단계 전이가
\(a_{t+3}=6a_t+B_t\)이고 상수항 \(B_t\)가 주기 6을 갖는다는
사실입니다. 한 주기의 값은 \((13,9,7,17,6,8)\)입니다.

## 문서와 인증서

- [상세 증명](PROOF.md)
- [검증·재현 기록](VERIFICATION.md)
- [실행 가능한 인증서](a136433_certificate.py)

저장소 루트에서 다음과 같이 재검산할 수 있습니다.

    python3 -m py_compile problems/oeis-a136433/a136433_certificate.py
    python3 problems/oeis-a136433/a136433_certificate.py

## 연구 상태

2026-08-11 당시 OEIS 원문은 이 식을 “Conjecture”로 표시하고 있었습니다.
같은 상수계수 점화식 자체는 2013년부터 OEIS의 “LinearRecurrence” 계산
코드에 나타나므로, 여기서 보존하는 기여는 식의 발견이 아니라 원래 비자율
점화식으로부터 모든 \(n\ge10\)에 대해 성립함을 보이는 전칭 증명입니다.
공개 검색에서 같은 증명을 찾지 못했다는 기록은 신규성의 확정이 아니며,
아직 동료 심사나 OEIS 편집자의 확인을 거치지 않았습니다.

## Lean 형식 증명

[`AgenticConjectures/OeisA136433.lean`](../../AgenticConjectures/OeisA136433.lean)이
이 전칭 명제를 mathlib 기반 Lean 4로 `sorry` 없이 증명합니다:

```
a136433_order9 : ∀ n, 10 ≤ n → (a n : ℤ) = 6 * a (n-3) + a (n-6) - 6 * a (n-9)
```

이 항목은 upstream Lean 스냅샷이 없으므로 수열 정의 자체의 충실성
주의사항(오프셋, 점화 인덱스 기준, `a 0` 미사용)은 모듈 docstring에
기록했습니다. CI가 `lake build`, no-sorry 게이트, 공리 감사를 재검증합니다.
