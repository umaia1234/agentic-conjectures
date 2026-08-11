# OEIS A397621

[OEIS A397621](https://oeis.org/A397621)의 Pascal mod 2 행
선형복잡도 추측을 증명합니다. [A001317](https://oeis.org/A001317)은
Pascal 삼각형의 \(n\)번째 행을 mod 2로 줄여 이진수로 읽은 수이고,
A397621은 그 MSB-first 이진 단어의 GF(2) 선형복잡도입니다.

## 결과

모든 \(n\ge1\)에 대해

\[
\operatorname{A397621}(\operatorname{A001317}(n))
=2^{\lfloor\log_2n\rfloor+1}-n
=\operatorname{A080079}(n).
\]

하한은 Pascal 행의 두 블록 사이에 생기는 연속 0 구간으로 얻고, 상한은
연결다항식 \(C(x)=(1+x)^d\)를 명시적으로 구성해 얻습니다.

## 문서와 인증서

- [상세 증명](PROOF.md)
- [검증·재현 기록](VERIFICATION.md)
- [canonical 인증서](a397621_certificate.py)
- [초기 v1 인증서](legacy/a397621_certificate.py)

후속 감사를 반영한 루트의 인증서가 canonical입니다. 초기 인증서는
재현성과 변경 이력 보존을 위해 그대로 둡니다.

    python3 -m py_compile problems/oeis-a397621/a397621_certificate.py
    python3 problems/oeis-a397621/a397621_certificate.py

## 연구 상태

2026-08-11 당시 A397621의 Formula 절은 이 등식을 “Conjecture”로
표시하고 있었습니다. 공개 검색에서 같은 증명을 찾지 못했다는 당시 기록은
신규성의 확정이 아닙니다. 인접한 이항수열 선형복잡도 문헌은 Pascal
삼각형의 무한 대각선 수열을 다루며, 여기의 고정된 유한 행 문제와는
구별됩니다. 이 증명은 아직 동료 심사나 OEIS 편집자의 확인을 거치지
않았습니다.
