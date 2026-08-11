# OEIS A067720

## 부분정리

원 문제는

\[
\varphi(k^2+1)=k\varphi(k+1)
\]

을 만족하면서 \(k+1\)이 합성수인 해가 \(k=8\)뿐인지 묻는다. 이
폴더에서는 \(k+1\)이 소수 거듭제곱인 다음 부분족을 판정한다.

> \(k+1=p^a\), \(p\)가 소수이고 \(a\ge2\)라 하자. \(p=2\)이면 해가
> 없다. \(p\)가 홀수이고
> \[
> V:=v_2(p^a-1)+v_2(p-1)\le5
> \]
> 이면 유일한 해는 \((p,a,k)=(3,2,8)\)이다.

증명은 [PROOF.md](PROOF.md)에 있다. 이 결과는 일반 합성수 \(k+1\)을
다루지 않으며, 홀수 \(p\)에서 \(V\ge6\)인 소수 거듭제곱 경우도 남긴다.
따라서 원 추측 전체의 해결이 아니다.

## 원문 상태와 검증 범위

- 2026-08-11에 확인한 [OEIS A067720](https://oeis.org/A067720)
  revision #18은 “\(8\)만 추가값인가?”라고 묻고 있었고,
  [b-file](https://oeis.org/A067720/b067720.txt)은 첫 10000항을 제공했다.
  b-file의 길이는 추측이나 이 증명의 범위가 아니다.
- 같은 날 FormalConjectures main commit
  `9118d083ffca1536f521f9a7d103201f537ea670`의
  [`67720.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/OEIS/67720.lean)도
  이 명제를 `category research open`으로 표시했다.
- 이 폴더에는 계산 인증서가 없다. 결론은 유한 탐색 결과가 아니라
  [PROOF.md](PROOF.md)의 초등적 부등식과 소인수 구조 논증이 정확히
  명시한 부분족에만 적용된다.
- 같은 공개 부분정리를 당시 공개 웹, arXiv, 수학 Q&A, SeqFan,
  GitHub에서 찾지 못했으나 이는 음성 검색 결과일 뿐이다. 동료평가 전에는
  신규성을 단정하지 않는다.

## 상류 Lean 형식화

감사에 사용한 FormalConjectures 원문과 고정 출처는
[upstream 기록](upstream/README.md) 및 [`67720.lean`](upstream/67720.lean)에
보존했다. `k=8` 외에는 `k+1`이 소수라는 전역 명제는 `by sorry`인 **추측
statement**이지 형식 증명이 아니며, 이 폴더는 명시한 소수거듭제곱 부분족만 다룬다.
