[English](README.md) | **한국어**

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

증명은 [PROOF.ko.md](PROOF.ko.md)에 있다. 이 결과는 일반 합성수 \(k+1\)을
다루지 않으며, 홀수 \(p\)에서 \(V\ge6\)인 소수 거듭제곱 경우도 남긴다.
따라서 원 추측 전체의 해결이 아니다.

## 2의 거듭제곱 경우에 대한 Lean 형식 증명

[`AgenticConjectures/OeisA067720.lean`](../../AgenticConjectures/OeisA067720.lean)은
upstream의 수열 소속 조건을 정확히 복사하고 `sorry`, 추가 공리,
`native_decide` 없이 다음을 증명한다.

```text
power_two_add_one_not_solution {k a : ℕ} (ha : 2 ≤ a)
    (hk : k + 1 = 2 ^ a) : ¬ A k
```

증명은 \(k=2t+1\), \(k^2+1=2N\)이며 \(N\)이 홀수임을 보인다. 이어서
\(\varphi(2N)=\varphi(N)\le N\)과 다음 엄격한 부등식을 사용한다.

\[
N < k\,2^{a-1}=k\varphi(2^a).
\]

이는 A067720을 정의하는 등식과 모순이다. [PROOF.ko.md](PROOF.ko.md)의
홀수 소수 \(V\le5\) 부분은 여전히 비형식적 증명이며 Lean 정리로 등록하지
않았다.

### 명제 충실성

- `A k`는 upstream 명제
  `Nat.totient (k ^ 2 + 1) = k * Nat.totient (k + 1)`을 정확히 옮겼다.
  수열 인덱스나 뺄셈 규약의 변환은 없다.
- 가정 `2 ≤ a`와 `k + 1 = 2 ^ a`는 정확히 \(p=2\), \(a\ge2\)인
  부분족이며, \(a=1\)인 소수 경계 경우를 제외한다.
- 이 정리는 홀수 소수 거듭제곱, 임의의 합성수 \(k+1\), 또는 \(k=8\) 외의
  모든 수열 원소에서 \(k+1\)이 소수라는 upstream 전역 명제를 다루지 않는다.

## 원문 상태와 검증 범위

- 2026-08-11에 확인한 [OEIS A067720](https://oeis.org/A067720)
  revision #18은 “\(8\)만 추가값인가?”라고 묻고 있었고,
  [b-file](https://oeis.org/A067720/b067720.txt)은 첫 10000항을 제공했다.
  b-file의 길이는 추측이나 이 증명의 범위가 아니다.
- 같은 날 FormalConjectures main commit
  `9118d083ffca1536f521f9a7d103201f537ea670`의
  [`67720.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/OEIS/67720.lean)도
  이 명제를 `category research open`으로 표시했다.
- 이 폴더에는 유한 탐색 인증서가 없다. 2의 거듭제곱 배제는 Lean 커널로
  검증하며, [PROOF.ko.md](PROOF.ko.md)의 초등적 부등식과 소인수 구조
  논증은 정확히 명시한 더 큰 부분족에만 적용된다.
- 같은 공개 부분정리를 당시 공개 웹, arXiv, 수학 Q&A, SeqFan,
  GitHub에서 찾지 못했으나 이는 음성 검색 결과일 뿐이다. 동료평가 전에는
  신규성을 단정하지 않는다.

## 상류 Lean 형식화

감사에 사용한 FormalConjectures 원문과 고정 출처는
[upstream 기록](upstream/README.md) 및 [`67720.lean`](upstream/67720.lean)에
보존했다. `k=8` 외에는 `k+1`이 소수라는 전역 명제는 `by sorry`인 **추측
statement**이지 형식 증명이 아니며, 이 폴더는 명시한 소수거듭제곱 부분족만 다룬다.

## 재현 방법

저장소 루트에서 다음을 실행한다.

```bash
lake env lean AgenticConjectures/OeisA067720.lean
python3 scripts/check_imports.py
python3 scripts/check_sorry.py
lake build
python3 scripts/check_axioms.py
python3 scripts/verify_all.py --ci
python3 scripts/gen_readme.py --check
python3 scripts/gen_upstream_docs.py --check
python3 scripts/check_docs.py
```

개발 머신에서 모듈 직접 elaboration은 4.45초가 걸렸다. 2026-08-12에 웜
캐시로 실행한 저장소 전체 8개 게이트는 총 84.87초가 걸렸다. import 도달성
0.02초, 금지 구문 검사 0.03초, `lake build` 6.60초, 공리 감사 3.42초,
CI 가능 인증서 42개 검사 74.59초, 대시보드 신선도 검사 0.09초, upstream
문서 신선도 검사 0.02초, 문서 감사 0.10초였다. 인증서 검사에는 `/tmp`에
이미 빌드되어 있고 `PATH`에 추가한 `drat-trim`을 사용했으며, 바이너리는
커밋하지 않았다.
