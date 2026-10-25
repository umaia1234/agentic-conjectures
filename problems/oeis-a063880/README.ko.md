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

> \(\omega(C(n))\le3\)인 모든 해에서 \(C(n)=108\)이다. 따라서 이
> 부분족의 해는 정확히
> \[
> n=108s,\qquad s\text{ squarefree},\qquad\gcd(s,108)=1
> \]
> 이며, 이 부분족의 유일한 primitive 해는 \(108\)이고 모든 해가
> \(108\pmod{216}\)이다.

\(\omega(C(n))\le2\)인 경우는 [PROOF.md](PROOF.ko.md)에서 증명하고,
소수가 세 개인 경우는 [THREE_PRIMES.md](THREE_PRIMES.ko.md)에서 더한다
([세 소수로 이루어진 core](#세-소수로-이루어진-core) 참조). 두 결과 모두
[`AgenticConjectures/OeisA063880.lean`](../../AgenticConjectures/OeisA063880.lean)에서
**Lean 4로 커널 검사**되었다([아래](#lean-4-형식화) 참조). 이 정리는
가상적인 추가 primitive 해의 powerful core가 서로 다른 소수를 적어도
네 개 가져야 함을 보일 뿐, 그 경우를 배제하지는 않는다. 따라서 원
추측 전체의 해결이 아니다.

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
- \(\omega(C(n))\le3\)인 모든 해의 분류는 탐색이 아니라 증명이다.
  [PROOF.md](PROOF.ko.md)의 곱셈적 국소비율 논증과
  [THREE_PRIMES.md](THREE_PRIMES.ko.md)의 세 소수 논증을 쓰며, 그 안에
  남는 유한 개의 경우는 Lean 안에서 검사한다. 기계 검증 산출물은 아래의
  Lean 모듈이다(CI가 no-`sorry` 게이트와 공리 감사를 거쳐 다시
  빌드한다). [THREE_PRIMES.md](THREE_PRIMES.ko.md) 8절의 두 Python
  탐색은 세 소수 경우의 일부를 독립적으로 교차 검증할 뿐 인증서가
  아니다.
- 같은 공개 부분정리를 당시 공개 웹, arXiv, 수학 Q&A, SeqFan,
  GitHub에서 찾지 못했으나 이는 음성 검색 결과일 뿐이다. 동료평가 전에는
  신규성을 단정하지 않는다.

## Lean 4 형식화

부분정리는 mathlib만을 사용해 `sorry` 없이
[`AgenticConjectures/OeisA063880.lean`](../../AgenticConjectures/OeisA063880.lean)
(네임스페이스 `AgenticConjectures.OeisA063880`)에 형식화되어 있다:

| 선언 | 내용 |
|---|---|
| `unitaryDivisors`, `usigma`, `A` | 상류 정의 `OeisA63880.unitaryDivisors / usigma / A`를 글자 그대로 옮긴 것: `A n := 0 < n ∧ σ 1 n = 2 * usigma n` |
| `IsPrimitive`, `IsPrimitiveTerm`, `Powerful` | 상류 보조 정의 `Set.IsPrimitive`, `OeisA63880.IsPrimitiveTerm`, `Nat.Powerful`(= `Nat.Full 2`)을 복사·전개한 것 |
| `statement_mod_216`, `statement_unique_primitive` | 상류의 두 미해결 추측 `mod_216_of_a`, `unique_primitive_108` (`Prop`이며 **증명되지 않음**) |
| `usigma_mul`, `usigma_prime_pow`, `usigma_eq_sigma_of_squarefree` | \(\sigma^*\)의 곱셈성, \(e\ge1\)에서 \(\sigma^*(p^e)=1+p^e\), squarefree 수에서 \(\sigma^*=\sigma\) |
| `a_mul_iff` | PROOF.md의 환원 (4): \(m\)과 서로소인 squarefree \(s\)에 대해 `A (m * s) ↔ A m` |
| `sigma_prime_pow_lt`, `not_a_prime_pow`, `sigma_mul_sigma_lt_of_odd` | 국소비율 부등식: 소수 거듭제곱 하나는 해가 아니고, 서로 다른 홀수 소수 \(p,q\)의 \(p^aq^b\)도 해가 아님 |
| `eq_of_two_pow_mul_prime_pow` | 두 소수 디오판토스 분류: \(q\) 홀수, \(a,b\ge2\)에서 \(\sigma(2^a)\sigma(q^b)=2(1+2^a)(1+q^b)\)이면 \(q=3,a=2,b=3\) |
| `eq_108_of_powerful` | 소인수가 두 개 이하인 powerful 해는 \(108\) |
| `exists_eq_108_mul_of_card_le_two` | **주정리**: `A n`이고 \(p^2\mid n\)인 소수 \(p\)가 두 개 이하이면 `n = 108 * s` (`s`는 squarefree, \(108\)과 서로소), 즉 \(C(n)=108\) |
| `mod_216_of_card_le_two`, `eq_108_of_isPrimitiveTerm_of_card_le_two` | 따름정리: \(n\equiv108\pmod{216}\), 그리고 이 부분족의 유일한 primitive 항은 \(108\) |
| `a_108_mul`, `primeFactors_filter_sq_dvd_108_mul` | 역으로 \(108\)과 서로소인 squarefree \(s\)에 대해 \(108s\)는 항이며 이 부분족에 속한다(\(p^2\mid108s\)인 소수 \(p\)는 정확히 \(2,3\)) — 따라서 분류는 동치이다 |
| `powerful_of_isPrimitiveTerm`, `a_of_primitive_mul_squarefree` | 상류의 두 `textbook` 보조정리(상류에서는 sorry): primitive 항은 powerful이고, primitive × 서로소 squarefree는 항 |
| `a_108`, `isPrimitiveTerm_108` | 확인용 정리: 상류 test 정리 중 두 개 |

명제 충실성. `A`, `unitaryDivisors`, `usigma`는 상류 스냅샷을 글자
그대로 옮겼다(`σ 1`은 `ArithmeticFunction.sigma 1`; 모든 등식은 `ℕ`에서
덧셈형이므로 절단 뺄셈 문제가 없다). `Set.IsPrimitive`와 `Nat.Powerful`은
mathlib에 없어 고정 커밋의 상류 보조 파일
(`FormalConjecturesForMathlib/NumberTheory/Primitive.lean`,
`…/Data/Nat/Full.lean`)에서 복사했고, `Nat.Full 2`는
`∀ p ∈ n.primeFactors, p ^ 2 ∣ n`으로 전개했다. 가정
\(\omega(C(n))\le2\)는 `(n.primeFactors.filter fun p => p ^ 2 ∣ n).card ≤ 2`로
부호화했다 — \(p^2\mid n\)인 소수 \(p\)가 바로 powerful core의
소인수이다 — 그리고 결론 \(C(n)=108\)은
`∃ s, Squarefree s ∧ Nat.Coprime 108 s ∧ n = 108 * s`로 부호화했으며,
이는 동치이다(그런 \(s\)에 대해 \(C(108s)=108\)이고, 역으로 \(C(n)=108\)이면
\(n/108\)은 squarefree이며 \(108\)과 서로소이다).

Lean 증명은 PROOF.md를 따른다: \(\sigma\)와 \(\sigma^*\)의 곱셈성으로
`A`를 powerful core로 환원하고, 국소비율 부등식으로 소수 하나와 홀수
소수 둘의 경우를 배제하며, \(q\mid3\) 논증과
\((2^{a+1}-7)(3^{b}-3)=24\)(PROOF.md의 식 (9)에 3을 곱한 것)로
\(2^aq^b\)를 처리한다. 서술상의 차이 두 가지: 해의 복원은 core \(C(n)\)을
명시적으로 정의하는 대신 `a_mul_iff`로 지수 1인 소수를 하나씩 떼어내는
\(n\)에 대한 강한 귀납법으로 하고, powerful 경우는 \(n\)의 소인수
개수(\(0,1,2\))로 나눈다.

재현(저장소 루트에서; `lake build`와 `check_axioms.py`는 mathlib
캐시 `lake exe cache get`이 필요):

```bash
lake build AgenticConjectures.OeisA063880   # 이 모듈만, mathlib 캐시 후 약 20초
lake build                                  # 전체 라이브러리 (check_axioms.py에 필요)
python3 scripts/check_sorry.py
python3 scripts/check_axioms.py             # propext / Classical.choice / Quot.sound만
```

## 세 소수로 이루어진 core

**결과.** 서로 다른 소수 \(p,q,r\)와 \(a,b,c\ge2\)에 대해 powerful 수
\(n=p^aq^br^c\)는 \(\sigma(n)=2\sigma^*(n)\)을 만족하지 않는다. 두 소수
정리와 합치면 \(\omega(C(n))\le3\)인 모든 해에서 \(C(n)=108\)이다.
따라서 이 더 큰 부분족에서도 모든 항이 \(108\pmod{216}\)이고 \(108\)이
유일한 primitive 항이다. 이 결과는 같은 상류 술어에 대해 Lean으로 커널
검사를 거쳤고, 비형식 증명은 [THREE_PRIMES.md](THREE_PRIMES.ko.md)에 있다.

**방법.** 소수를 \(p<q<r\)로 정렬한다.

- 인수 \(2\)가 없을 때: 부등식 \(\sigma(p^e)/(1+p^e)<p/(p-1)\)에 의해
  \(r\le13\)인 \(\{3,5,r\}\)만 남고, 이는 유한 상자 세 개로 배제한다.
- \(\{2,3,r\}\): 비율 부등식으로 \(a=2\), \(b\in\{2,3\}\)을 뺀 모든
  경우가 해결된다. 남은 경우에 방정식은 불가능한
  \(\sigma(r^c)=1+r^c\)가 되거나, \(r\mid9\)를 강제하는
  \(91\sigma(r^c)=100(1+r^c)\)가 된다.
- \(2<5\le q<r\): \(K=2^{a+1}-1\)로 두면 방정식은 정수 항등식
  \(W_qW_r=K(K+3)t_qt_r\)가 된다. 2진 값매김 항등식이 \(b\)와 \(c\)를
  묶어 준다(예를 들어 \(c\)가 짝수이면 \(b\equiv7\pmod{16}\)이다).
  이어서 보조 정수 \(\Omega,H,G\)에서 얻는 크기 부등식이 유한 개의
  경우를 빼고 모든 지수 조합을 배제한다. 남는 것은 상자 다섯 개와,
  16개의 쌍 \((a,q)\)에 대해 허용되는 근이 없는 \(r\)의 이차방정식이다.
- 두 소수 정리의 squarefree 부분 귀납법을 상한 \(3\)으로 다시 적용하면
  powerful 경우의 결과가 모든 \(n\)으로 확장된다.

**재현.** 탐색은 이 폴더에서, 나머지 명령은 저장소 루트에서 실행한다.
시간은 개발 기기에서 측정했다.

```bash
lake build AgenticConjectures.OeisA063880   # mathlib 캐시 후 약 20초, 증명 전체를 검사
lake build && python3 scripts/check_axioms.py   # propext / Classical.choice / Quot.sound만
cd problems/oeis-a063880
python3 three_prime_search.py --amax 22       # 4.0초 (CI)
python3 three_prime_search_int.py --amax 22   # 8.3초 (CI)
python3 three_prime_search.py --amax 28       # 5분 06초 (기기 부하 상태)
python3 three_prime_search_int.py --amax 28   # 16분 08초 (기기 부하 상태)
```

두 탐색은 \(2\le a\le\) `AMAX`(모든 \(q,b,r,c\))에서 경우
\(2<5\le q<r\)를 서로 독립적으로, 정확한 산술로 교차 검증한다. 둘 다
해를 찾지 못했으며, 어느 쪽도 증명의 일부가 아니다.

| 선언 | 내용 |
|---|---|
| `not_a_three_prime_pow` | 서로 다른 소수 \(p,q,r\)와 \(a,b,c\ge2\)에 대해 `¬ A (p ^ a * q ^ b * r ^ c)` |
| `three_prime_sorted`, `caseB`, `case23`, `caseA` | 정렬 후의 경우 나누기: 인수 \(2\) 없음, \(\{2,3,r\}\), \(2<5\le q<r\) |
| `two_adic_rel`, `caseA_two_adic` | 2진 항등식과 그로부터 나오는 \((b,c)\)에 대한 제약 |
| `caseA_c7`, `caseA_c46`, `caseA_c2`, `caseA_c5b`, `caseA_c3a`, `caseA_c3b` | \(c\)에 따른 경우 나누기의 크기 부등식 |
| `caseA_c3b_finite`, `box_*`(상자 여덟 개) | 유한 검사 |
| `eq_108_of_powerful_of_card_le_three` | 소인수가 세 개 이하인 powerful 해는 \(108\)이다 |
| `exists_eq_108_mul_of_card_le` | powerful 해가 \(108\)뿐인 임의의 상한 \(k\)에 대한 squarefree 부분 귀납법 |
| `exists_eq_108_mul_of_card_le_three` | **주정리**: `A n`이고 \(p^2\mid n\)인 소수 \(p\)가 세 개 이하이면 `n = 108 * s`이고 `s`는 squarefree이며 \(108\)과 서로소 |
| `mod_216_of_card_le_three`, `eq_108_of_isPrimitiveTerm_of_card_le_three` | 따름정리: \(n\equiv108\pmod{216}\)이고, 이 부분족의 유일한 primitive 항은 \(108\) |

증명 단계와 Lean 보조정리의 전체 대응표는
[THREE_PRIMES.md](THREE_PRIMES.ko.md) 9절에 있다.

명제의 충실성. `not_a_three_prime_pow`는 상류 술어 `A` 자체(위와 같이
글자 그대로 옮긴 것)에 대해 진술되며, 가정은 `p.Prime`, `q.Prime`,
`r.Prime`, 쌍마다 `≠`, 그리고 `2 ≤ a`, `2 ≤ b`, `2 ≤ c`이다. 가정
\(\omega(C(n))\le3\)은 두 소수의 경우와 똑같이
`(n.primeFactors.filter fun p => p ^ 2 ∣ n).card ≤ 3`으로 나타내고, 결론
\(C(n)=108\)도 같은 `∃ s, Squarefree s ∧ Nat.Coprime 108 s ∧ n = 108 * s`로
나타낸다. 경우 \(2<5\le q<r\)는 증명 안에서 `ℕ`의 값을 `ℤ`로 옮긴 뒤
`ℤ` 위에서 논증한다. 새 `ℕ` 명제에 나오는 뺄셈은 `1 ≤ p`일 때의
`p - 1`뿐이므로 정확한 뺄셈이다. 위의 두 소수 정리들은 바뀌지 않았다.

**주장하지 않는 것.** 서로 다른 소수를 네 개 이상 가진 core는 다루지
않으므로 OEIS의 두 추측은 여전히 미해결이다. \(10^{18}\)까지의 OEIS
탐색은 다시 실행하지 않았다. 새로움은 주장하지 않는다.

## 상류 Lean 형식화

감사에 사용한 FormalConjectures 원문과 고정 출처는
[upstream 기록](upstream/README.md) 및 [`63880.lean`](upstream/63880.lean)에
보존했다. 전역 합동·유일성 추측은 `by sorry`로 적힌 **statement**이지 형식
증명이 아니다. 이 폴더는 powerful core의 소인수가 세 개 이하인 부분족만
증명하며, 그 증명은 (독립 빌드가 불가능한) 스냅샷을 import하는 대신 상류
정의를 글자 그대로 다시 적은 위의 이 저장소 모듈에 들어 있다.
