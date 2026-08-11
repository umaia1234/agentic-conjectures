[English](README.md) | **한국어**

# OEIS A063880

## 부분정리

원 문제는

\[
\sigma(n)=2\sigma^*(n)
\]

인 수의 유일한 primitive 항이 \(108\)이고 모든 항이
\(108\pmod{216}\)인지 묻는다. 여기서

\[
C(n):=\prod_{e_p\ge2}p^{e_p}
\]

를 \(n\)의 powerful core라 하면, 이 폴더에서는 다음을 증명한다.

> \(\omega(C(n))\le2\)인 모든 해에서 \(C(n)=108\)이다. 따라서 이
> 부분족의 해는 정확히
> \[
> n=108s,\qquad s\text{ squarefree},\qquad\gcd(s,108)=1
> \]
> 이며, 이 부분족의 유일한 primitive 해는 \(108\)이고 모든 해가
> \(108\pmod{216}\)이다.

상세 증명은 [PROOF.md](PROOF.ko.md)에 있다. 이 정리는 가상적인 추가
primitive 해의 powerful core가 서로 다른 소수를 적어도 세 개 가져야
함을 보일 뿐, 그 경우를 배제하지는 않는다. 따라서 원 추측 전체의
해결이 아니다.

## 원문 상태와 검증 범위

- 2026-08-11에 확인한 [OEIS A063880](https://oeis.org/A063880)
  revision #39는 primitive 항을 \(n<10^{18}\)까지 조사해 \(108\)만
  찾았다고 보고했다. 이는 출처가 보고한 계산이며 이 작업에서 그 범위를
  독립 재실행했다는 뜻이 아니다.
- 같은 날 FormalConjectures main commit
  `9118d083ffca1536f521f9a7d103201f537ea670`의
  [`63880.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/OEIS/63880.lean)은
  유일한 primitive 항과 합동류라는 두 전역 명제를 모두
  `category research open`으로 표시했다.
- 이 폴더에는 계산 인증서가 없다. 결과는 유한 탐색이 아니라
  [PROOF.md](PROOF.ko.md)의 곱셈적 국소비율 논증으로
  \(\omega(C(n))\le2\)인 모든 수를 완전히 분류한다.
- 같은 공개 부분정리를 당시 공개 웹, arXiv, 수학 Q&A, SeqFan,
  GitHub에서 찾지 못했으나 이는 음성 검색 결과일 뿐이다. 동료평가 전에는
  신규성을 단정하지 않는다.

## 상류 Lean 형식화

감사에 사용한 FormalConjectures 원문과 고정 출처는
[upstream 기록](upstream/README.md) 및 [`63880.lean`](upstream/63880.lean)에
보존했다. 전역 합동·유일성 추측은 `by sorry`로 적힌 **statement**이지 형식
증명이 아니다. 이 폴더는 powerful core의 소인수가 두 개 이하인 부분족만 증명한다.
