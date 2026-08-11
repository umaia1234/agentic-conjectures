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

- [상세 증명](PROOF.md)
- [검증·재현 기록](VERIFICATION.md)
- [실행 가능한 인증서](a340881_certificate.py)

저장소 루트에서 다음과 같이 재검산할 수 있습니다.

    python3 -m py_compile problems/oeis-a340881/a340881_certificate.py
    python3 problems/oeis-a340881/a340881_certificate.py

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
