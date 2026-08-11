# OEIS A190363

## 판정

OEIS에 제안된 다음 21항 상수계수 점화식은 **거짓**이다.

\[
a(n)=2n+\left\lfloor\frac{n\sqrt5}{2}\right\rfloor+\left\lfloor\frac n4\right\rfloor,
\qquad
a(n+21)=a(n+17)+a(n+4)-a(n).
\]

첫 실패 기준 인덱스는 \(n=140\), 즉 첫 실패 출력항은 \(a(161)\)이다.
실제로

\[
a(157)+a(144)-a(140)=541\ne542=a(161).
\]

더 나아가 Pell 방정식으로 무한히 많은 실패 인덱스가 생성되므로, 이
점화식은 어느 인덱스 이후에도 항구적으로 성립하지 않는다. 자세한 최소성
인증과 무한 반례족은 [PROOF.md](PROOF.md)에 있다.

## 원문 상태와 결과의 범위

- 2026-08-11에 확인한 [OEIS A190363](https://oeis.org/A190363) revision
  #14에서는 이 점화식이 2025-01-28자 `Conjecture`로 표시되어 있었다.
- 당시 [공식 b-file](https://oeis.org/A190363/b190363.txt)은
  \(n=1,\ldots,10000\)을 제공했다. b-file의 네 관련 값은 여기의 반례와
  일치하지만, b-file 길이를 원 주장의 유효 범위로 해석하지 않는다.
- 이 결과와 같은 공개 반례·증명을 당시 공개 웹, arXiv, 수학 Q&A,
  SeqFan, GitHub에서 찾지 못했으나 이는 음성 검색 결과일 뿐이다. 아직
  동료평가나 OEIS 제출을 거치지 않았으므로 신규성을 단정하지 않는다.

## 재현

[`a190363_certificate.py`](a190363_certificate.py)는 Python 표준
라이브러리만 사용하며 부동소수점
근사 없이 `math.isqrt`와 정수 제곱 비교로 다음을 검사한다.

- \(1\le n\le139\)에서 결함이 모두 0이고 \(D(140)=1\)임;
- 최소성에 쓰인 shift-17 margin과 네 항의 제곱 인증;
- Pell 불변량과 처음 여덟 개의 Pell 생성 반례.

저장소 루트에서 실행한다.

```bash
python3 problems/oeis-a190363/a190363_certificate.py
```

2026-08-11 재검산 당시 파일의 SHA-256은 다음과 같았다.

```text
0cd6f96307f4c0ceb007ec14ff813ba6443c4163328ded3a2df384d55038979e  problems/oeis-a190363/a190363_certificate.py
```

당시 `python3 -m py_compile`을 통과했고 실행 시간은 약 0.00초였다.

## 상류 Lean 형식화

FormalConjectures의 [원문 스냅샷과 출처 기록](upstream/README.md)을
[`190363_e4edee15.lean`](upstream/190363_e4edee15.lean)에 보존했다. 그
`by sorry` 정리는 제안된 점화식을 적은 **추측 statement**이지 형식 증명이 아니다.
이 폴더는 첫 실패와 무한 반례족으로 그 statement를 반증한다.

## 이 저장소의 Lean 형식 반증

upstream 정의를 그대로 복사한
[`AgenticConjectures/OeisA190363.lean`](../../AgenticConjectures/OeisA190363.lean)에서
정확히 그 statement의 부정

```
oeis_190363_conjecture_0_false : ¬ A190363_LR.IsSolution (fun n => (a (n + 1) : ℤ))
```

을 `sorry` 없이 증명했다. 해 인덱스 139(= OEIS 기준 인덱스 140)에서의 첫
실패 `542 ≠ -471 + 484 + 528 = 541`을 네 개의 정확한 정수 제곱 샌드위치로
평가한다. CI가 `lake build`, no-sorry 게이트, 공리 감사(표준 3공리만)를
재검증한다.
