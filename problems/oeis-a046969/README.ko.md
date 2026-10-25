[English](README.md) | **한국어**

# OEIS A046969 — 추측 I

## 판정

[OEIS A046969](https://oeis.org/A046969)의 추측 I은 다음과 같은 더 강한
형태로 **증명**되었다.

\[
a(p)=12\,(2p-1)
\]

이 식은 $2p-1$도 소수인 모든 소수 $p>3$에 대해 성립하므로
$a(p)/12=2p-1$은 소수이다. 여기서 $a(n)$은 $B_{2n}/(2n(2n-1))$의
분모이고, $B_k$는 Bernoulli 수이다.

증명은 Lean 4로 형식화되어 있으며
([`AgenticConjectures/OeisA046969.lean`](../../AgenticConjectures/OeisA046969.lean)),
`sorry`, 추가 공리, `native_decide` 없이 검사된다.

## 원문 명제와 선행 결과 조사

[OEIS A046969](https://oeis.org/A046969)(revision #70, 2026-10-24 확인)는
$\log\Gamma(z)$에 대한 Stirling 급수 계수의 분모를 나열한다. 항목의
Maple·PARI 프로그램은 offset 1로
$a(n)=\operatorname{denominator}\bigl(B_{2n}/(2n(2n-1))\bigr)$을 계산한다.
Lorenzo Sauras Altuzarra는 2020년 10월 13일에 다음을 추가했다.

> “Conjecture I: if n > 2, then a(A005382(n))/12 is prime.”

여기서 [A005382](https://oeis.org/A005382)는 $2p-1$도 소수인 소수 $p$의
목록 $2, 3, 7, 19, 31, 37, \ldots$이다. 같은 주석은 추측 II도 제시하는데,
항목에는 현재 Adamczewski가 $n=236791$에서 이를 반증했다고 기록되어
있고(arXiv:2608.11941), 상류 Formal Conjectures 파일도 이를 해결됨으로
표시한다. 추측 II는 이 문서의 범위 밖이다.

항목에는 추측 I의 증명이 기록되어 있지 않으며,
[스냅샷 commit](upstream/README.md)에서 상류 명제는 여전히
`research open`으로 태그되어 있다. OEIS Open 연구(arXiv:2608.11941)와
공개된 시도 점수도 추측 II만 다룬다. 아래 논증은 von Staudt–Clausen 정리,
Adams 정리, Kummer 합동식, Voronoi 합동식이라는 고전적 결과를 직접
적용한 것이다. 새로움은 주장하지 않는다. 이 증명은 검토되지 않았고
OEIS나 다른 외부 기관에 보고되지 않았다. 외부 제출에는 사람의 승인이
필요하다.

## 증명

$p>3$과 $q=2p-1$이 소수라고 하자. 그러면 4는 소수가 아니므로
$p\ge5$이고, $q\ge9$이다.

**1단계 ($B_{2p}$의 분모).** $3\mid q$이면 $q=3$이어야 하므로 불가능하고,
$3\nmid p$이다. 따라서 $p\equiv1\pmod 3$이고 $3\mid 2p+1$이다.
$(r-1)\mid 2p$인 소수 $r$은 $r-1\in\{1,2,p,2p\}$를 만족한다. 그런데
$r=p+1$은 2보다 큰 짝수이고, $r=2p+1$은 3보다 큰 3의 배수이다. 따라서
von Staudt–Clausen 정리에 의해 $B_{2p}+\tfrac12+\tfrac13=z\in\mathbb Z$,
즉

\[
B_{2p}=\frac{N}{6},\qquad N=6z-5,\qquad \gcd(N,6)=1
\]

이다.

**2단계 (귀착).** $a(p)=\operatorname{den}\bigl(N/(12pq)\bigr)$이다.
$p\mid N$이고 $q\nmid N$이면 $N=pM$으로 쓸 때 $B_{2p}/(2pq)=M/(12q)$이고
$M$은 2, 3, $q$와 서로소이므로 $a(p)=12q$이다. 따라서 $p\mid N$과
$q\nmid N$만 보이면 된다.

**3단계 ($\ell^2$을 법으로 한 거듭제곱 합).** $\ell\ge5$를 소수, $m$을
짝수라 하고 $S_m(\ell)=\sum_{k<\ell}k^m$이라 하자.
$\binom{m+1}{i}/(m+1)=\binom{m}{i}/(m+1-i)$를 쓰면 Faulhaber 공식에서

\[
S_m(\ell)=\ell B_m+\sum_{i<m} B_i\binom{m}{i}\frac{\ell^{\,j}}{j},
\qquad j=m+1-i\ge2
\]

를 얻는다. $j=2$이면 계수 $B_{m-1}$은 $0$이거나 $B_1=-\tfrac12$이므로 그
항의 $\ell$진 값매김은 2 이상이다. $j\ge3$이면 von Staudt–Clausen에 의해
$v_\ell(B_i)\ge-1$이고, $\ell^{v_\ell(j)}\le j<5^{\,j-2}\le\ell^{\,j-2}$에서
$v_\ell(j)\le j-3$이므로 그 항의 값매김도 $-1+j-(j-3)=2$ 이상이다.
따라서 $\mathbb Z_{(\ell)}$에서 $S_m(\ell)\equiv\ell B_m\pmod{\ell^2}$이다.

**4단계 (2배 사상).** $\ell=2h+1$이라 하자. $\{0,\ldots,\ell-1\}$을 짝수
$2k$ ($k\le h$)와 홀수 $2j+1$ ($j<h$)로 나눈다. 2배 사상은 $k=h+1+j$를
$2k=\ell+(2j+1)$로 보내므로

\[
(2^m-1)\,S_m(\ell)=\sum_{j<h}\bigl((\ell+2j+1)^m-(2j+1)^m\bigr)
\equiv \ell\, m\sum_{j<h}(2j+1)^{m-1}\pmod{\ell^2}
\]

이다. 이것은 승수 2에 대한 Voronoi 합동식을 거듭제곱 합의 형태로 쓴
것이다.

**5단계 (Adams 쪽: $p\mid N$).** $\ell=p$, $m=2p$로 두자. 4단계의 우변은
$p\cdot2p$의 배수이므로 $p^2\mid(2^{2p}-1)\,S_{2p}(p)$이다. Fermat
정리에 의해 $2^{2p}-1\equiv3\not\equiv0\pmod p$이므로 $p^2\mid S_{2p}(p)$이다.
그러면 3단계에서 $v_p(pB_{2p})\ge2$, 즉 $v_p(N)=v_p(B_{2p})\ge1$을 얻는다.

**6단계 (Kummer 쪽: $q\nmid N$).** $\ell=q$, $m=q+1=2p$, $h=p-1$로 두자.
$q\mid N$이면 $v_q(qB_{2p})\ge2$이므로 3단계에 의해 $q^2\mid S_{2p}(q)$이다.
그러면 4단계에서 $q\mid(q+1)\sum_{j<p-1}(2j+1)^q$를 얻는다. Fermat 정리에
의해 이 합은 $q$를 법으로 $\sum_{j<p-1}(2j+1)=(p-1)^2$과 합동이다.
그런데 $0<p-1<q$이므로 $q\nmid(p-1)^2$이고, 이는 모순이다.

5단계와 6단계는 증명에 필요한 범위에서 Adams 정리($p\mid m$이고
$(p-1)\nmid m$이면 $p\mid\operatorname{num}B_m$)와 Kummer 합동식
$B_{2p}/(2p)\equiv B_2/2=\tfrac1{12}\pmod q$의 특수한 경우이다. 실제로 위
계산은 $3B_{q+1}\equiv\tfrac14$, 즉 $B_{q+1}\equiv\tfrac1{12}\pmod q$를 준다.

## Lean 형식화

모든 선언은 이름공간 `AgenticConjectures.OeisA046969`에 있다.

| 선언 | 내용 |
|---|---|
| `a` | 상류 정의를 항 단위로 그대로 복사한 것 |
| `statement` | `∀ p, p.Prime → (2 * p - 1).Prime → 3 < p → (a p / 12).Prime` |
| `conjecture1_holds` | `statement` (추측 I) |
| `conjecture1` | 같은 명제를 상류와 똑같은 시그니처로 쓴 것 |
| `a_eq` | `2 * p - 1`도 소수인 소수 `p > 3`에 대해 `a p = 12 * (2 * p - 1)` (2단계) |
| `vonStaudt_primes_eq` | $B_{2p}$에 대한 von Staudt–Clausen 소수 집합은 $\{2,3\}$ (1단계) |
| `bernoulli_two_mul_eq` | 어떤 정수 $z$에 대해 $B_{2p}=(6z-5)/6$ (1단계) |
| `padicNorm_bernoulli_le` | 모든 홀수 소수 $\ell$에 대해 $\lvert B_n\rvert_\ell\le\ell$ |
| `padicNorm_sum_pow_sub_le` | 소수 $\ell\ge5$와 짝수 $m$에 대해 $\lvert S_m(\ell)-\ell B_m\rvert_\ell\le\ell^{-2}$ (3단계) |
| `voronoi_two` | 4단계를 $\mathbb Z$에서 $(2h+1)^2$에 대한 나누어떨어짐으로 쓴 것 |
| `sq_dvd_sum_pow_two_mul` | 소수 $p\ge5$에 대해 $p^2\mid S_{2p}(p)$ |
| `not_sq_dvd_sum_pow_succ` | 소수 $q=2h+1$, $h\ge1$에 대해 $q^2\nmid S_{q+1}(q)$ |
| `prime_dvd_num` | $B_{2p}=N/6$일 때 $p\mid N$ (5단계) |
| `not_dvd_num` | $B_{2p}=N/6$일 때 $q\nmid N$ (6단계) |

`conjecture1_holds`, `conjecture1`, `a_eq`, `padicNorm_sum_pow_sub_le`,
`voronoi_two`는 공리 감사를 위해 [`status.yaml`](status.yaml)에 등록되어
있다. 증명에는 mathlib의 `Bernoulli.vonStaudt_clausen`,
`sum_range_pow`(Faulhaber), `sq_dvd_add_pow_sub_sub`와 `padicNorm` API를
사용한다.

## 명제 충실성

- **정의.** `a`는 [상류 스냅샷](upstream/README.md)에서 항 단위로 그대로
  복사했다. `a 0 = 0`이고, `n ≠ 0`이면 `m = 2 * n`과 `k = m * (m - 1)`을
  `ℕ`에서 계산하여 `a n = (bernoulli m / (k : ℚ)).den`이다. 이는
  $n\ge1$에서 OEIS 공식과 같고, PARI 프로그램도 $n<1$이면 0을 반환한다.
  mathlib의 `bernoulli`는 $B_1=-\tfrac12$ 규약을 쓰지만, 여기에는 짝수
  첨자 $2n\ge2$만 나타나므로 모든 규약이 일치한다. 점검 스크립트는 이
  정의가 OEIS DATA 줄의 35개 항을 재현함을 확인한다.
- **첨자 기준.** $A005382(1)=2$, $A005382(2)=3$이고 A005382는
  증가수열이므로 $\{A005382(n): n>2\}$는 정확히 $2p-1$도 소수인 소수
  $p>3$의 집합이다. `statement`는 상류 docstring과 마찬가지로 정확히 이
  집합 위에서 양화한다.
- **자연수 뺄셈.** `2 * p - 1`에서는 $p\ge2$이고 `m - 1`에서는
  $m=2p\ge2$이므로 어느 뺄셈도 잘리지 않는다.
- **자연수 나눗셈.** `a p / 12`는 `ℕ`에서 버림 나눗셈이지만, `a_eq`가
  `a p = 12 * (2 * p - 1)`임을 보이므로 나눗셈은 정확하다.
- **경계값.** `p`가 소수이므로 `a`의 `n = 0` 분기는 쓰이지 않는다. 가정은
  상류 정리와 정확히 같다. `statement`는 그 전칭 폐포이고,
  `conjecture1`은 그 시그니처를 그대로 반복한다.

## 기계 검증과 재현

저장소 루트에서 다음을 실행한다.

```bash
lake build AgenticConjectures.OeisA046969
python3 problems/oeis-a046969/a046969_certificate.py --limit 400
```

2026-10-24에 mathlib이 미리 빌드된, 부하가 큰 공유 머신에서
`lake build`는 모듈을 8.6초(벽시계 시간 13초)에 컴파일했다. 스크립트는
약 1초 걸렸다.

[`a046969_certificate.py`](a046969_certificate.py)는 Python 표준
라이브러리와 정확한 유리수 연산만 사용한다. 이것은 증명의 일부가 아니라
점검용이다. 점화식 $\sum_{k\le n}\binom{n+1}{k}B_k=0$으로
$B_0,\ldots,B_{800}$을 계산하고 다음을 검사한다.

- $a(1),\ldots,a(35)$를 OEIS DATA 줄과 비교한다.
- $2p-1$도 소수인 17개의 소수 $3<p\le400$ 모두에 대해
  $\operatorname{den}B_{2p}=6$, $p\mid N$, $q\nmid N$, $a(p)=12(2p-1)$이고
  $a(p)/12$가 소수임을 확인한다.

저장소 CI도 모듈을 다시 빌드하고, 등록된 정리의 공리를 감사하며,
스크립트를 다시 실행한다.

## 주장하지 않는 것

- 같은 항목의 추측 II는 다루지 않는다.
- 새로움은 주장하지 않는다. 사용한 재료는 고전적이며 결과는 검토되지
  않았다.
- OEIS나 상류에는 아무것도 보고하지 않았다.
