[English](README.md) | **한국어**

# OEIS A056777 / Choudhury–Wei Conjecture 1.1

## 부분정리

원 추측은 합성수 \(n\ge4\)가

\[
\varphi(n+12)=\varphi(n)+12,
\qquad
\sigma(n+12)=\sigma(n)+12
\]

을 동시에 만족하면

\[
n=p(p+8),
\qquad p,p+2,p+6,p+8\text{ all prime}
\]

인지 묻는다. 이 폴더에서는 다음을 증명한다.

> 위 두 식을 만족하는 합성수 \(n\ge4\)에 대해 \(n+12\)는 소수
> 거듭제곱일 수 없다.

자세한 불변량과 모든 소수별 경우 분류는 [PROOF.md](PROOF.ko.md)에 있다.
이 결과는 논문이 이미 배제한 “\(n\)이 소수 거듭제곱”인 경우의 반대쪽
끝을 배제하지만 원 추측 전체를 해결하지 않는다. 남은 해는 양쪽 모두
소수 거듭제곱이 아니며, 논문의 semiprime 정리 밖에서는 적어도 한쪽에
서로 다른 소인수가 세 개 이상 있거나 중복 소인수가 있다.

## 원문 상태와 검증 범위

- 2026-07-22의 [Choudhury–Wei 논문 v3, Conjecture
  1.1](https://arxiv.org/abs/2606.10331v3)은 이 문제를 명시적으로 open으로
  두었다. 논문의 Theorem 2.2는 \(n,n+12\)가 모두 서로 다른 두 소수의
  곱인 경우를 판정하고, Theorem 3.1은 \(n\) 자체가 소수 거듭제곱인
  경우를 배제한다.
- 저자들은 공개한 [OpenMP
  코드](https://github.com/bvrtoverfitprimes/integersequencetesting/blob/main/search_omp.cpp)로
  정확히 \(2\le n<10^{12}\)을 검사해 얻은 166개 해가 모두 예상한
  형태라고 보고했다. 이는 출처가 보고한 계산이며 이 작업에서 그 범위를
  독립 재실행했다는 뜻이 아니다.
- 이 폴더에는 계산 인증서가 없다. 결과는 유한 탐색에 의존하지 않고
  [PROOF.md](PROOF.ko.md)의 초등 정수론 논증으로 모든 소수 거듭제곱
  \(n+12\)을 배제한다.
- 같은 공개 부분정리를 2026-08-11 당시 공개 웹, arXiv, 수학 Q&A,
  SeqFan, GitHub에서 찾지 못했으나 이는 음성 검색 결과일 뿐이다.
  동료평가 전에는 신규성을 단정하지 않는다.

## 상류 Lean 형식화

감사에 사용한 FormalConjectures 원문과 고정 출처는
[upstream 기록](upstream/README.md) 및 [`56777.lean`](upstream/56777.lean)에
보존했다. 중심 추측은 `by sorry`로 닫힌 **statement**이지 형식 증명이 아니며,
이 폴더의 `n+12` 소수거듭제곱 배제 정리는 그 Lean 파일에 형식화되어 있지 않다.
