[English](VERIFICATION.md) | **한국어**

# OEIS A397245 검증·재현 기록

이 문서는 [상세 증명](PROOF.ko.md)의 정수 삼각 점화식, GF(3) 대수
점화식, 3진법 계수 분류 및 미분항등식을 독립 경로로 재검산한 기록입니다.
유한 검사는 전칭 증명을 대신하지 않습니다.

## canonical과 legacy

[canonical 인증서](a397245_certificate.py)는 후속 감사를 반영합니다.
[초기 v1 인증서](legacy/a397245_certificate.py)는 초기 보고서 당시의
계산을 재현하기 위해 그대로 보존합니다. 두 스크립트 모두 SymPy가
필요합니다.

## 감사 이력

- 최종 통합 감사 실행 시각: 2026-08-11T23:09:20+09:00
- 당시 Python 구문 검사: 통과
- 당시 독립 수학 감사: 정수성, GF(3) 환원, 유일성, 대수·미분
  항등식 통과
- 문제별 문서 통합 중 2026-08-12에 canonical과 legacy를 다시 실행:
  모두 통과

## 재현

저장소 루트에서 실행합니다.

    python3 -m py_compile \
      problems/oeis-a397245/a397245_certificate.py \
      problems/oeis-a397245/legacy/a397245_certificate.py
    python3 problems/oeis-a397245/a397245_certificate.py
    python3 problems/oeis-a397245/legacy/a397245_certificate.py

canonical 출력은 다음과 같습니다.

    A397245 certificate: PASS
      exact integer recurrence: n=0..140
      independent GF(3) algebraic recurrence: n=0..2000
      symbolic differential identity: verified over GF(3)

legacy 출력은 다음과 같습니다.

    A397245 certificate checks passed

## 인증서가 확인하는 것

- 정수 삼각 점화식으로 \(a_0,\ldots,a_{140}\)을 정확한 큰 정수로
  계산하고, 처음 아홉 항 및 mod 3 분류와 대조합니다.
- 독립적으로 \(B=1+xB^2+x^3B^3\)의 계수 점화식을
  \(n=0,\ldots,2000\)까지 계산해 3진법 분류와 대조합니다.
- \(B'=B^2/(1+xB)\)와
  \(D=x+x(B-1)B'/B\)에서 \(xD'=B-1\)이 나오는지를 GF(3)
  Gröbner 환원으로 확인합니다.

초기 보고서에는 이와 별도로 당시 OEIS 공식 b-file의 \(0,\ldots,400\)
전 항을 대조해 일치했다는 기록도 있습니다. 현재 보존된 두 인증서는
네트워크에서 b-file을 내려받지 않으므로, 이 항목은 2026-08-11 당시의
역사적 외부 대조 기록이며 위 명령만으로 다시 수행되는 검사는 아닙니다.

## 무결성

    be2b3a0f3f2f2d167f502210f0180b5cdbda48b830a925909c476c0683812d3a  a397245_certificate.py
    4c946fd309c1638129d04096fcd78f52c356fb605a055fa5547aa1a9f7a4185e  legacy/a397245_certificate.py

첫 값은 2026-08-11 최종 검증 기록과 현재 파일에서 일치합니다. 두 번째는
문제별 통합 시 현재 legacy 파일에 대해 새로 기록한 값입니다.

문제별 분리 전 네 문제 통합 요약 문서의 역사적 SHA-256은 다음과
같습니다.

    166b0cd51374e5e2f247f086c2d9b6e448dd879342131f86300ba8c2eb640da1
