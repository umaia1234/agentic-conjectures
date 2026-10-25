[English](README.md) | **한국어**

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

- [상세 증명](PROOF.ko.md)
- [검증·재현 기록](VERIFICATION.ko.md)
- [canonical 인증서](a397621_certificate.py)
- [초기 v1 인증서](legacy/a397621_certificate.py)

후속 감사를 반영한 루트의 인증서가 canonical입니다. 초기 인증서는
재현성과 변경 이력 보존을 위해 그대로 둡니다.

    python3 -m py_compile problems/oeis-a397621/a397621_certificate.py
    python3 problems/oeis-a397621/a397621_certificate.py

## Lean 형식 증명

[`AgenticConjectures/OeisA397621.lean`](../../AgenticConjectures/OeisA397621.lean)은
`sorry`, 추가 공리, `native_decide` 없이 다음을 증명합니다.

```text
a_A001317_eq_A080079 : statement
  -- ∀ n ≥ 1, a (A001317 n) = A080079 n, 여기서 A080079 n = 2 * 2 ^ Nat.log 2 n - n
linearComplexity_pascal :
  1 ≤ n → linearComplexity (fun i => (n.choose i : ZMod 2)) (n + 1) = A080079 n
a_two : a 2 = 1
```

증명은 [상세 증명](PROOF.ko.md)을 따릅니다. `binWord_A001317`은 §3.3으로,
A001317(n)의 MSB-first 이진 단어가 \(\mathbf F_2\) 위 \((1+x)^n\)의
계수열임을 보입니다. `not_hasRecurrence`는 §3.4.1–3.4.2의 연속 0 구간
하한이고, `hasRecurrence`는 §3.4.3의 \((1+x)^d\) 상한입니다. Frobenius
항등식 \((1+x)^{2^h}=1+x^{2^h}\)은 mathlib의 `add_pow_char_pow`에서
얻습니다.

    lake build AgenticConjectures.OeisA397621
    python3 scripts/check_axioms.py

## 명제 충실성

- `a`는 OEIS 이름을 따릅니다. 즉 \(n\)의 이진 전개를 최상위 비트부터 읽은
  단어의 GF(2) 선형복잡도이며, Berlekamp–Massey가 계산하는 값입니다.
  `HasRecurrence s N L`은 \(L\le i<N\)에서
  \(s_i+c_1s_{i-1}+\cdots+c_Ls_{i-L}=0\)을 요구하고 \(c_L\)에는 조건을 두지
  않으며, `linearComplexity`는 그런 \(L\)의 최솟값입니다. 이는 §3.1의
  점화식 길이이자 인증서의 전수 풀이기가 찾는 길이입니다.
- OEIS 항목의 한 주석은 \(a(n)\)을 최소 연결다항식의 차수라고 설명합니다.
  이를 문자 그대로 읽으면 \(n=2\)에서 달라집니다. 단어 `10`은 길이 1의
  점화식(\(c_1=0\))을 만족하지만, 차수 2 미만의 연결다항식으로는 생성되지
  않습니다. 데이터는 \(a(2)=1\)이며, `a_two`가 우리 정의가 1을 준다는 것을
  확인합니다. 추측에 나오는 단어에서는 두 해석이 일치합니다. 길이 하한이
  차수 \(d\) 미만의 모든 다항식을 배제하고, 증인 \((1+x)^d\)의 차수가
  정확히 \(d\)이기 때문입니다. 이 마지막 설명은 형식화하지 않았습니다.
- `A001317 n`은 \(\sum_{k=0}^{n}(\binom nk \bmod 2)\,2^k\), 즉 Pascal
  삼각형의 \(n\)번째 행을 mod 2로 줄여 이진수로 읽은 값입니다.
  `A080079 n`은 OEIS Formula 절의 닫힌 꼴
  \(2\cdot2^{\lfloor\log_2n\rfloor}-n\)이며, 자리올림 수열에 관한 이름
  자체를 형식화한 것은 아닙니다. 명제는 A080079의 오프셋인 \(n=1\)부터
  시작합니다.
- 이 항목에는 상류 FormalConjectures 스냅샷이 없습니다.

## 연구 상태

2026-08-11 당시 A397621의 Formula 절은 이 등식을 “Conjecture”로
표시하고 있었습니다. 공개 검색에서 같은 증명을 찾지 못했다는 당시 기록은
신규성의 확정이 아닙니다. 인접한 이항수열 선형복잡도 문헌은 Pascal
삼각형의 무한 대각선 수열을 다루며, 여기의 고정된 유한 행 문제와는
구별됩니다. 이 증명은 아직 동료 심사나 OEIS 편집자의 확인을 거치지
않았습니다.
