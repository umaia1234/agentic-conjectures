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

## 소수 거듭제곱 부분족에 대한 Lean 형식 증명

[`AgenticConjectures/OeisA067720.lean`](../../AgenticConjectures/OeisA067720.lean)은
upstream의 수열 소속 조건을 정확히 복사하고 `sorry`, 추가 공리,
`native_decide` 없이 부분정리의 두 방향을 모두 증명한다.

```text
power_two_add_one_not_solution {k a : ℕ} (ha : 2 ≤ a)
    (hk : k + 1 = 2 ^ a) : ¬ A k

odd_prime_power_small_two_valuation_iff {p a k : ℕ}
    (hp : p.Prime) (hodd : Odd p) (ha : 2 ≤ a) (hk : k + 1 = p ^ a)
    (hV : padicValNat 2 (p ^ a - 1) + padicValNat 2 (p - 1) ≤ 5) :
    A k ↔ p = 3 ∧ a = 2 ∧ k = 8
```

2의 거듭제곱 증명은 \(k=2t+1\), \(k^2+1=2N\)이며 \(N\)이 홀수임을 보인 뒤
\(\varphi(2N)=\varphi(N)\le N\)과 \(N < k\,2^{a-1}\)을 쓴다. 홀수 소수 증명은
[PROOF.ko.md](PROOF.ko.md)를 따른다. \(M=k^2+1\)은 소인수가 모두
\(1\pmod 4\)인 홀수 제곱자유 합성수이고, \(V\le5\)이면 \(M\)은 서로 다른 두
소수의 곱이며, 그 이차식의 정수근은 \((p,a,k)=(3,2,8)\)에서만 존재한다.
직접 계산으로 \(\varphi(65)=48=8\varphi(9)\)이다.

### 명제 충실성

- `A k`는 upstream 명제
  `Nat.totient (k ^ 2 + 1) = k * Nat.totient (k + 1)`을 정확히 옮겼다.
  수열 인덱스나 뺄셈 규약의 변환은 없다.
- 가정 `2 ≤ a`와 `k + 1 = 2 ^ a`는 정확히 \(p=2\), \(a\ge2\)인
  부분족이며, \(a=1\)인 소수 경계 경우를 제외한다.
- 홀수 \(p\)에서 `padicValNat 2`는 2진 부가 \(v_2\)이고, `p ^ a - 1`은
  \(k\)와 같은 양의 정수이다. 상한 `≤ 5`는 [PROOF.ko.md](PROOF.ko.md)의
  \(V\le5\) 가정이다.
- 두 정리 모두 \(V\ge6\)인 홀수 소수 거듭제곱, 임의의 합성수 \(k+1\), 또는
  \(k=8\) 외의 모든 수열 원소에서 \(k+1\)이 소수라는 upstream 전역 명제를
  다루지 않는다.

## 원문 상태와 검증 범위

- 2026-08-11에 확인한 [OEIS A067720](https://oeis.org/A067720)
  revision #18은 “\(8\)만 추가값인가?”라고 묻고 있었고,
  [b-file](https://oeis.org/A067720/b067720.txt)은 첫 10000항을 제공했다.
  b-file의 길이는 추측이나 이 증명의 범위가 아니다.
- 같은 날 FormalConjectures main commit
  `9118d083ffca1536f521f9a7d103201f537ea670`의
  [`67720.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9118d083ffca1536f521f9a7d103201f537ea670/FormalConjectures/OEIS/67720.lean)도
  이 명제를 `category research open`으로 표시했다.
- 이 폴더에는 유한 탐색 인증서가 없다. 2의 거듭제곱 배제와 홀수 소수
  \(V\le5\) 유일성 명제는 모두 Lean 커널로 검증하며, 논증은
  [PROOF.ko.md](PROOF.ko.md)에 적은 것이다. \(V\ge6\)인 경우와 소수
  거듭제곱이 아닌 합성수 \(k+1\)은 미해결로 남긴다.
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

2026-11-25에 `lake env lean`으로 이 모듈을 직접 elaboration하는 데 약 16초가
걸렸다. 이어서 웜 캐시로 저장소 게이트를 통과하는 데 약 190초가 걸렸다.
import 도달성 검사와 금지 구문 검사는 각각 1초 미만, olean이 최신인 상태에서
`lake build`는 3초(모듈 자체 빌드는 18초), 공리 감사는 5초, CI 가능 인증서
44개 검사는 181초, 대시보드·upstream 문서·문서 감사는 각각 1초 미만이었다.
인증서 검사에는 `/tmp`에 빌드해서 `PATH`에 올린 `drat-trim`을 사용했으며,
바이너리는 커밋하지 않았다.
