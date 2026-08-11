[English](VERIFICATION.md) | **한국어**

# OEIS A136433 검증·재현 기록

이 문서는 [상세 증명](PROOF.ko.md)의 세 단계 affine 전이와 9-lag
점화식을 유한 계산으로 독립 재검산한 기록입니다. 유한 검사는 전칭 증명을
대신하지 않습니다.

## 감사 이력

- 최종 통합 감사 실행 시각: 2026-08-11T23:09:20+09:00
- 당시 Python 구문 검사: 통과
- 당시 독립 수학 감사: 별도 에이전트 감사 통과
- 문제별 문서 통합 중 2026-08-12에 인증서를 다시 실행: 통과

## 재현

저장소 루트에서 실행합니다.

    python3 -m py_compile problems/oeis-a136433/a136433_certificate.py
    python3 problems/oeis-a136433/a136433_certificate.py

기록된 출력은 다음과 같습니다.

    A136433 certificate: PASS
      three-step constants by t mod 6: [13, 9, 7, 17, 6, 8]
      conjectured order-9 recurrence checked through n=10000

## 인증서가 확인하는 것

- OEIS 공식 초기항과 원래 주기계수 점화식으로 생성한 값을 대조합니다.
- \(t\bmod6\)의 여섯 경우에서 세 단계 전이의 선형계수가 모두 6이고,
  상수항이 정확히 \((13,9,7,17,6,8)\)인지 확인합니다.
- \(1\le t<1000\)에서 세 단계 전이가 6만큼 이동해도 같은지 검사합니다.
- 모든 \(10\le n\le10000\)에서
  \(a_n=6a_{n-3}+a_{n-6}-6a_{n-9}\)를 검사합니다.

## 무결성

2026-08-11 최종 검증 기록과 현재 파일에서 같은 인증서 SHA-256을
확인했습니다.

    a08ec9bb967b6bc231eb7e4d5c8e9004b3eb1312e42b7d97b2669378fb54dfac  a136433_certificate.py

문제별 분리 전 네 문제 통합 요약 문서에 기록되어 있던 SHA-256은
다음과 같습니다. 이 값은 삭제된 통합 원본의 역사적 provenance만
식별하며, 현재 재현 대상은 위 인증서와 이 디렉터리의 증명입니다.

    166b0cd51374e5e2f247f086c2d9b6e448dd879342131f86300ba8c2eb640da1
