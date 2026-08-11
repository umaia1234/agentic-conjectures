[English](README.md) | **한국어**

# OEIS A397245

[OEIS A397245](https://oeis.org/A397245)의 두 mod 3 필요충분 추측을
증명합니다. \(A(x)=\sum_{n\ge0}a_nx^n\), \(a_0=a_1=1\)은

\[
A(x)=\exp\!\left(
x+\sum_{n\ge2}\frac{(4n^2-1)a_n}{4n^2}x^n
\right)
\]

으로 정의됩니다.

## 결과

모든 \(n\ge0\)에 대해 다음 완전한 분류가 성립합니다.

- \(a_n\equiv1\pmod3\)일 필요충분조건은
  \(n+2=3^j\) 또는 \(n+2=2\cdot3^j\)인 것입니다.
- \(a_n\equiv2\pmod3\)일 필요충분조건은
  \(n+2=3^i+3^j\), \(0\le i<j\), 인 것입니다.
- 그 밖의 경우에는 \(a_n\equiv0\pmod3\)입니다.

증명은 먼저 \(a_n/n\in\mathbb Z\)를 삼각 점화식으로 확립한 뒤,
\(\mathbb F_3[[x]]\)에서

\[
A(x)\equiv\frac{T+T^2-x}{x^2},\qquad
T=\sum_{j\ge0}x^{3^j}
\]

를 증명하고 3진법으로 계수를 읽습니다.

## 문서와 인증서

- [상세 증명](PROOF.ko.md)
- [검증·재현 기록](VERIFICATION.ko.md)
- [canonical 인증서](a397245_certificate.py)
- [초기 v1 인증서](legacy/a397245_certificate.py)

후속 감사를 반영한 루트의 인증서가 canonical입니다. 이 인증서는
[SymPy](https://www.sympy.org/)를 사용하며, 초기 인증서는 재현성과
변경 이력 보존을 위해 그대로 둡니다.

    python3 -m py_compile problems/oeis-a397245/a397245_certificate.py
    python3 problems/oeis-a397245/a397245_certificate.py

## 연구 상태

2026-08-11 당시 OEIS Comments 절은 두 필요충분 명제를 모두
“Conjecture”로 표시하고 있었습니다. 정확한 문구·초기항·핵심 닫힌형으로
공개 웹과 arXiv를 검색해 같은 증명을 찾지 못했다는 당시 기록은 신규성의
확정이 아닙니다. 이 증명은 아직 동료 심사나 OEIS 편집자의 확인을 거치지
않았습니다.
