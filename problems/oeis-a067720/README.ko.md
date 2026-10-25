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

증명은 [PROOF.ko.md](PROOF.ko.md)에 있다. 이제 두 부분 모두 Lean 커널로
검증되며(아래 Lean 절 참고), 두 가지 확장도 함께 증명했다. 홀수 경우는
\(V\le6\)에서도 성립하고, \(k^2+1\)이 두 소수의 곱이면 모든 \(V\)에 대해
성립한다. 이 결과들은 일반 합성수 \(k+1\)을 다루지 않는다. 또한
\(V\ge7\)이면서 \(k^2+1\)의 소인수가 세 개 이상인 홀수 소수 거듭제곱
경우도 남긴다. 따라서 원 추측 전체의 해결이 아니다.

## Lean 형식화

[`AgenticConjectures/OeisA067720.lean`](../../AgenticConjectures/OeisA067720.lean)(네임스페이스
`AgenticConjectures.OeisA067720`)은 upstream의 수열 소속 조건을 정확히
복사한다. 그리고 `sorry`, 추가 공리, `native_decide` 없이 다음을 증명한다.

| 선언 | 내용 |
|---|---|
| `A` | upstream 술어 `OeisA67720.A`를 그대로 옮긴 것: `Nat.totient (k ^ 2 + 1) = k * Nat.totient (k + 1)` |
| `power_two_add_one_not_solution` | \(p=2\): \(a\ge2\)이고 \(k+1=2^a\)인 원소는 없다 |
| `a_eight` | `A 8`, 즉 \(\varphi(65)=48=8\varphi(9)\)를 커널 `decide`로 확인한다 |
| `odd_prime_power_solution_of_two_prime_factors` | 모든 \(V\): \(p\)가 홀수 소수이고 \(a\ge2\)이며 \(k+1=p^a\)일 때, `A k`가 성립하고 \(k^2+1=qr\)(\(q,r\)는 소수)이면 \((p,a,k)=(3,2,8)\) |
| `odd_prime_power_solution_iff_of_two_adic_le_six` | **주정리**: \(p\)가 홀수 소수이고 \(a\ge2\), \(V\le6\), \(k+1=p^a\)이면 `A k ↔ p = 3 ∧ a = 2 ∧ k = 8` |
| `odd_prime_power_solution_iff_of_two_adic_le_five` | [PROOF.ko.md](PROOF.ko.md)의 홀수 소수 정리(\(V\le5\))를 \(V\le6\) 정리의 따름정리로 얻은 것 |

### 2의 거듭제곱 경우

```text
power_two_add_one_not_solution {k a : ℕ} (ha : 2 ≤ a)
    (hk : k + 1 = 2 ^ a) : ¬ A k
```

증명은 \(k=2t+1\), \(k^2+1=2N\)이며 \(N\)이 홀수임을 보인다. 이어서
\(\varphi(2N)=\varphi(N)\le N\)과 다음 엄격한 부등식을 사용한다.

\[
N < k\,2^{a-1}=k\varphi(2^a).
\]

이는 A067720을 정의하는 등식과 모순이다.

### 홀수 소수 거듭제곱

```text
odd_prime_power_solution_iff_of_two_adic_le_six {p a k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 2 ≤ a) (hk : k + 1 = p ^ a)
    (hV : padicValNat 2 (p ^ a - 1) + padicValNat 2 (p - 1) ≤ 6) :
    A k ↔ p = 3 ∧ a = 2 ∧ k = 8

odd_prime_power_solution_of_two_prime_factors {p a k q r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 2 ≤ a) (hk : k + 1 = p ^ a) (hA : A k) (hq : q.Prime)
    (hr : r.Prime) (hM : k ^ 2 + 1 = q * r) : p = 3 ∧ a = 2 ∧ k = 8
```

`odd_prime_power_solution_iff_of_two_adic_le_five`는 첫 명제에서 `≤ 6`을
`≤ 5`로 바꾼 것과 같은 꼴이다.

Lean 증명은 [PROOF.ko.md](PROOF.ko.md)를 따른다. \(M=k^2+1\)로 두면
등식은 \(\varphi(M)=k\,p^{a-1}(p-1)\)이 된다. \(M\)의 어떤 소인수도
\(k\), \(p\), \(p-1\)을 나누지 않으므로 \(M\)은 squarefree이다(식 (2)).
\(M\)의 모든 소인수는 \(4\)로 나눈 나머지가 \(1\)이고(식 (3)),
\(v_2(\varphi(M))=V\)이다(식 (5)). Lean 증명은 두 군데에서 PROOF.ko.md의
서술 방식과 다르다.

- 부등식 (4)로 \(\omega(M)\)을 세는 대신, 가장 작은 소인수
  (`Nat.minFac`)를 차례로 떼어 낸다: \(M=qm\), \(m=rs\), \(s=tu\).
  squarefree이므로 각 분해의 두 인수는 서로소이고, 따라서 \(\varphi\)가
  곱으로 나뉘며 소인수 하나마다 인수 \(4\)가 생긴다. \(M\)은 소수가
  아니다. \(s=1\)이면 \(M\)의 소인수는 정확히 두 개이다. \(u\ne1\)이면
  \(2^8\mid\varphi(M)\)이다.
- 두 소인수 경우에 PROOF.ko.md는 \(f(x)=x(S-x)\)가 \([0,S/2]\)에서
  증가함을 이용한다. Lean 증명은 그 대신 동치인 정수 부등식
  \((x-q)(r-x)\ge0\)과 \((q-x-1)(r-x-1)\ge0\)을 쓴다. 그리고
  PROOF.ko.md의 추정 (8)–(12)로 이를 계산한다. \(a\ge3\)이면 \(x=p\)에서,
  \(a=2\)이고 \(p>3\)이면 \(x=p+1\)에서 계산한다.

두 소인수 경우에는 \(V\)에 대한 상계를 전혀 쓰지 않는다. 그래서
`odd_prime_power_solution_of_two_prime_factors`는 모든 \(V\)에 대해
성립한다.

**\(V\le5\)에서 \(V\le6\)으로.** 이 단계는 PROOF.ko.md에 없다. \(V=6\)이고
\(M=qrt\)의 소인수가 정확히 세 개라고 하자. 나머지 경우는 이미 모두
배제되었다. \(v_2(\varphi(M))=\sum v_2(q_i-1)=6\)이고 각 항은 \(2\)
이상이다. 따라서 모든 \(q_i\equiv5\pmod 8\)이고
\(M\equiv5^3\equiv5\pmod 8\)이다. 한편 \(p-1\mid p^a-1=k\)이므로
\(v_2(p-1)\le v_2(k)\)이다. 따라서 \(6=V\le2v_2(k)\)이고, \(8\mid k\)이므로
\(M=k^2+1\equiv1\pmod 8\)이 되어 모순이다. Lean 증명도 같은 방식으로
경우를 나눈다. \(q,r,t\) 중 하나라도 \(8\)로 나눈 나머지가 \(1\)이면
\(2^7\mid\varphi(M)\)이 되어 \(V\le6\)에 모순이다. 그렇지 않으면 위와
같이 \(8\)에 대한 나머지가 충돌한다.

같은 아이디어로는 \(V=7\)에 이르지 못한다. 이 경우 2진 valuation이
\(2,2,3\)인 세 소인수는 \(M\equiv1\pmod 8\)을 주며, 이는 \(8\mid k\)와
모순되지 않는다.

참고로, 표준적인 lifting-the-exponent 보조정리에 따른 \(V\)의 값은
다음과 같다. 이는 Lean 형식화의 일부가 아니다. \(p\equiv3\pmod 4\)이고
\(a\)가 홀수이면 \(V=2\)이다. \(p\equiv3\pmod 4\)이고 \(a\)가 짝수이면
\(V=1+v_2(p+1)+v_2(a)\)이다. \(p\equiv1\pmod 4\)이면
\(V=2v_2(p-1)+v_2(a)\)이다.

### 명제 충실성

- `A k`는 upstream 명제
  `Nat.totient (k ^ 2 + 1) = k * Nat.totient (k + 1)`을 정확히 옮겼다.
  수열 인덱스나 뺄셈 규약의 변환은 없다.
- 가정 `2 ≤ a`와 `k + 1 = 2 ^ a`는 정확히 \(p=2\), \(a\ge2\)인
  부분족이며, \(a=1\)인 소수 경계 경우를 제외한다.
- 홀수 소수 정리들에서 `p.Prime`과 `p ≠ 2`는 \(p\)가 홀수 소수라는
  뜻이다. `2 ≤ a`와 `k + 1 = p ^ a`는 \(a\ge2\)인 \(k=p^a-1\)을 정하며,
  여기서도 \(a=1\)인 소수 경우를 제외한다.
- \(V\)는 `padicValNat 2 (p ^ a - 1) + padicValNat 2 (p - 1)`로 썼다.
  \(p\ge3\)이므로 두 자연수 뺄셈 모두 잘림이 없고 두 인수 모두 0이
  아니다. 따라서 이 인수들에서 `padicValNat 2`는 보통의 2진 valuation
  \(v_2\)이다.
- "유일한 해는 \((3,2,8)\)이다"는 이 가정 아래의 동치
  `A k ↔ p = 3 ∧ a = 2 ∧ k = 8`로 표현했다. \((3,2,8)\) 자체도 가정을
  만족하며(\(V=v_2(8)+v_2(2)=4\)), `a_eight`가 \(\varphi(65)=8\varphi(9)\)를
  확인한다.
- `odd_prime_power_solution_of_two_prime_factors`의 가정
  `k ^ 2 + 1 = q * r`은 \(q=r\)도 허용한다. 증명은 squarefree 성질로 이
  경우를 배제한다.
- 임의의 합성수 \(k+1\)이나, \(V\ge7\)이면서 \(k^2+1\)의 소인수가 세 개
  이상인 홀수 소수 거듭제곱은 다루지 않는다. \(k=8\) 외의 모든 수열
  원소에서 \(k+1\)이 소수라는 upstream 전역 명제도 다루지 않는다.

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
  \(V\le6\) 분류는 Lean 커널로 검증한다. 후자는 [PROOF.ko.md](PROOF.ko.md)의
  \(V\le5\) 정리를 포함하며, 그 \(V=6\) 단계는 위에서 설명했고
  PROOF.ko.md에는 없다.
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

2026-10-24에 웜 mathlib 캐시로 개발 머신에서 측정한 시간은 다음과 같다.

- 모듈 직접 elaboration: 11.2초
- 변경 후 `lake build AgenticConjectures.OeisA067720`: 벽시계 14.5초, 그중
  모듈 자체는 10초
- 이어서 실행한 전체 `lake build`: 10.5초
- 등록된 정리 84개 전체에 대한 공리 감사: 8.1초
- import 도달성, 금지 구문 검사,
  `verify_all.py --ci --only oeis-a067720`: 각각 0.1초 미만. 이 문제에는
  인증서 검사가 없다.

문서 게이트는 각각 0.2초 미만이 걸렸다.
