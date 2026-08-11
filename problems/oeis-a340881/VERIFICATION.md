# OEIS A340881 검증·재현 기록

이 문서는 [상세 증명](PROOF.md)에 쓰인 정의, 1차 점화식, 홀수 법의
순수 주기 및 일반 법의 궁극 주기를 유한 계산으로 독립 재검산한 기록입니다.
유한 검사는 전칭 증명을 대신하지 않습니다.

## 감사 이력

- 최종 통합 감사 실행 시각: 2026-08-11T23:09:20+09:00
- 당시 Python 구문 검사: 통과
- 당시 독립 수학 감사: 별도 에이전트 감사 통과
- 문제별 문서 통합 중 2026-08-12에 인증서를 다시 실행: 통과

## 재현

저장소 루트에서 실행합니다.

    python3 -m py_compile problems/oeis-a340881/a340881_certificate.py
    python3 problems/oeis-a340881/a340881_certificate.py

기록된 출력은 다음과 같습니다.

    A340881 certificate: PASS
      odd-modulus pure-period checks: 35255
      prime advertised-period checks: 12648
      general eventual-period/sign checks: 62106

## 인증서가 확인하는 것

- 공식 초기항과 점화식으로 계산한 값을 대조하고, \(n=1,\ldots,12\)에서는
  정의의 이중 곱·합을 직접 계산해 점화식과 비교합니다.
- \(3\le m<300\)인 홀수 법에서
  \(2\operatorname{ord}_m(2)\) 주기와 지수 이동 항등식을 검사합니다.
- \(p<252\)인 소수에서 광고된 주기 \(2(p-1)\)를 검사합니다.
- \(2\le m\le300\)에서 \(m=2^eu\) 분해에 따른 궁극 주기를 검사하고,
  \(2^e\) 성분에서는 \(A(n+1)\equiv-A(n)\pmod{2^e}\)도 따로 검사합니다.

## 무결성

2026-08-11 최종 검증 기록에 남은 인증서 SHA-256은 다음과 같습니다.

    18d5347ff49eb2eb5b0c974334ac0a4879dbf84d90ee9cf38b0d3dd4b16589e6  a340881_certificate.py

문제별 통합 뒤에는 코드 docstring의 증명 문서 이름만 삭제된
`RESULTS.md`에서 현재의 `PROOF.md`로 고쳤습니다. 실행 코드는 바뀌지
않았으며, 이 경로 정리 뒤 현재 SHA-256은 다음과 같습니다.

    17d7095390071e1e79d686aded5656c5135f7b558ca0a49b14e87253204ccffd  a340881_certificate.py

문제별 분리 전 네 문제 통합 요약 문서에 기록되어 있던 SHA-256은
다음과 같습니다. 이 값은 삭제된 통합 원본의 역사적 provenance만
식별하며, 현재 재현 대상은 위 인증서와 이 디렉터리의 증명입니다.

    166b0cd51374e5e2f247f086c2d9b6e448dd879342131f86300ba8c2eb640da1
