# OEIS A060841

## 판정

\[
R_n:=\frac1{\det M_n}
=\prod_{k=1}^n\frac{k^2}{\varphi(k)}
=\frac{(n!)^2}{\prod_{k=1}^n\varphi(k)}.
\]

OEIS에 함께 적혀 있던 두 추측의 판정은 다음과 같다.

1. **정수성 추측은 참이다.** 정확히
   \[
   R_n\in\mathbb Z\iff n\in\{1,2,\ldots,34,36,38\}.
   \]
2. **모든 기약분모가 2의 거듭제곱이라는 추측은 거짓이다.** 홀수 소수가
   분모에 처음 나타나는 인덱스는 \(n=1807\)이고
   \[
   \operatorname{den}(R_{1807})=2^{2342}\cdot3.
   \]

모든 \(n\ge91\)을 닫는 2-adic 경계, \(n\le90\)의 유한 인증, 최소 홀수
분모의 독립적인 두 계산은 [PROOF.md](PROOF.md)에 정리되어 있다. 두 번째
결과는 관련 [OEIS A260897](https://oeis.org/A260897)의 “모든 항이 2의
거듭제곱”이라는 주장도 반증한다.

## 원문 상태와 결과의 범위

- 2026-08-11에 확인한 [OEIS A060841](https://oeis.org/A060841) revision
  #37에서는 두 명제가 2015-08-02자 `Conjecture`로 남아 있었다.
- 당시 [공식 b-file](https://oeis.org/A060841/b060841.txt)은 분자의
  \(n=1,\ldots,400\) 값을 제공했다. 이 항 개수를 추측의 범위나 여기의
  전수검색 상한으로 해석하지 않는다.
- 정수성 분류는 \(n\ge91\)에 대한 증명과 \(n\le90\)의 정확 인증을
  결합한 전역 결과다. 최소 홀수 분모는 \(n\le1807\)을 정확히 검사한다.
- 같은 공개 반례·증명을 당시 공개 웹, arXiv, 수학 Q&A, SeqFan,
  GitHub에서 찾지 못했으나 이는 음성 검색 결과일 뿐이다. 아직 동료평가나
  OEIS 제출을 거치지 않았으므로 신규성을 단정하지 않는다.

## 재현

[`a060841_certificate.py`](a060841_certificate.py)는 Python 표준
라이브러리만 사용하고 다음 두
독립 경로를 모두 실행한다.

- `fractions.Fraction`으로 \(R_n\)을 직접 누적·약분;
- 각 소수 \(q\)에 대해 \(v_q(R_n)\)을 정수로 누적.

두 경로 모두 최초 홀수 분모를 \((n,q)=(1807,3)\)으로 판정한다. 저장소
루트에서 실행한다.

```bash
python3 problems/oeis-a060841/a060841_certificate.py
```

2026-08-11 재검산 당시 파일의 SHA-256은 다음과 같았다.

```text
82364fbe79c32c30009ce3193aefc0a1be6e824682cf236e7de80f75ac507464  problems/oeis-a060841/a060841_certificate.py
```

당시 `python3 -m py_compile`을 통과했고 실행 시간은 약 0.46초였다.

## 상류 Lean 형식화

FormalConjectures의 [원문 스냅샷과 출처 기록](upstream/README.md)을
[`60841_4cba886e.lean`](upstream/60841_4cba886e.lean)에 보존했다. 그 파일의
`by sorry` 정리는 두 OEIS 추측을 함께 적은 **statement**이지 형식 증명이 아니다.
여기서는 정수성 분류를 증명하는 한편 분모 명제는 `n=1807`로 반증한다.
