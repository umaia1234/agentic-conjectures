[English](VERIFICATION.md) | **한국어**

# OEIS A397621 검증·재현 기록

이 문서는 [상세 증명](PROOF.ko.md)의 연결다항식 방향, 하한의 0 구간,
명시적 상한 및 경계 사례를 서로 다른 알고리즘으로 재검산한 기록입니다.
유한 검사는 전칭 증명을 대신하지 않습니다.

## canonical과 legacy

[canonical 인증서](a397621_certificate.py)는 후속 감사를 반영합니다.
[초기 v1 인증서](legacy/a397621_certificate.py)는 초기 보고서 당시의
계산을 재현하기 위해 그대로 보존합니다. canonical 버전은 초기 검사를
모두 유지하면서 \(n=1,\ldots,512\)에서 증명에 사용한
\((1+x)^d\) 연결다항식의 합성곱 조건과 0 구간도 명시적으로 검사합니다.

## 감사 이력

- 최종 통합 감사 실행 시각: 2026-08-11T23:09:20+09:00
- 당시 Python 구문 검사: 통과
- 당시 독립 수학 감사: 연결다항식 방향, 하한 및 \(n=1\) 경계 통과
- 문제별 문서 통합 중 2026-08-12에 canonical과 legacy를 다시 실행:
  모두 통과

## 재현

저장소 루트에서 실행합니다.

    python3 -m py_compile \
      problems/oeis-a397621/a397621_certificate.py \
      problems/oeis-a397621/legacy/a397621_certificate.py
    python3 problems/oeis-a397621/a397621_certificate.py
    python3 problems/oeis-a397621/legacy/a397621_certificate.py

canonical 출력은 다음과 같습니다.

    A397621 certificate: PASS
      Berlekamp--Massey: n=1..512 plus 12 boundary values
      independent GF(2) system solver: n=1..80

legacy 출력은 다음과 같습니다.

    A397621 certificate checks passed

## 인증서가 확인하는 것

- 독립 Berlekamp--Massey 구현으로 \(n=1,\ldots,512\)와
  1000, 1023, 1024, 1025, 2047, 2048, 4095, 4096, 8191, 8192,
  9999, 10000의 큰 경계값을 검사합니다.
- 별도 GF(2) 가우스 소거 구현으로 모든 가능한 점화식 길이의 일관성을
  \(n=1,\ldots,80\)에서 검사합니다.
- canonical 인증서는 Pascal 다항식의 위치 \(r+1,\ldots,q-1\)이 0,
  위치 \(q\)가 1인지와
  \([x^i](1+x)^d(1+x)^n=0\) (\(d\le i\le n\))도 확인합니다.

## 무결성

    93bfbc68f744f25703683aba69e25d46ce02fa13bcef51183ba579faa70c3c2f  a397621_certificate.py
    5ced56c1afd2f6b5158059c69c17d64adefee0791fa7bd48945a622be00970ed  legacy/a397621_certificate.py

첫 값은 2026-08-11 최종 검증 기록과 현재 파일에서 일치합니다. 두 번째는
문제별 통합 시 현재 legacy 파일에 대해 새로 기록한 값입니다.

문제별 분리 전 네 문제 통합 요약 문서의 역사적 SHA-256은 다음과
같습니다.

    166b0cd51374e5e2f247f086c2d9b6e448dd879342131f86300ba8c2eb640da1
