[English](README.md) | **한국어**

# OEIS A398189 — 일반화 Schenker 합의 2진 부치(2-adic valuation)

[OEIS A398187](https://oeis.org/A398187)(Peter Luschny, 2026-07-23)은
**일반화 Schenker 합**의 삼각형이다:

\[
T(n,k) \;=\; \sum_{j=0}^{n-k} \frac{(n-k)!}{j!}\, n^j , \qquad 0 \le k \le n,
\]

열 \(k=0\)은 고전적인 Schenker 합
[A063170](https://oeis.org/A063170)이다.
[OEIS A398189](https://oeis.org/A398189)(Peter Luschny, 2026-07-27)는 그
2진 부치 \(v_2(T(n,k))\)의 삼각형이며, 항목의 주석은 다음과 같이 말한다
(2026-08-12 조회):

> We conjecture that:
> &nbsp;&nbsp;T(n, k) =
> &nbsp;&nbsp;&nbsp;&nbsp;= v2((n - k)!), if n is even;
> &nbsp;&nbsp;&nbsp;&nbsp;= 1, if n is odd and k = 0;
> &nbsp;&nbsp;&nbsp;&nbsp;= 0, if n is odd and k is odd;
> &nbsp;&nbsp;&nbsp;&nbsp;= v2(k + 2), if n is odd, k is even, and not k == 14 mod 16.
>
> All other cases arise when n is odd, k is even, and k == 14 mod 16. No
> simple formula is known.

## 결과

**추측된 네 경우 전부를 모든 \(0 \le k \le n\)에 대해 증명했다.** 추가로,
제외된 부류(\(n\) 홀수, \(k \equiv 14 \pmod{16}\))에서는 부치가 항상
\(\ge 4\)임을 증명했다 — 그 영역에 mod 16 패턴이 존재할 수 없는 이유다.

증명([PROOF.md](PROOF.md), 영어)은 행 다항식 \(T(n,k) = S_n(n-k)\)의
점화식 \(S_n(m+1) = (m+1) S_n(m) + n^{m+1}\)만 사용한다:

- **\(n\) 짝수:** 초거리(ultrametric) 귀납 — Legendre 공식으로
  \(v_2((m+1)!) \le m\)이므로 \(n^{m+1}\) 항의 부치가 항상 엄격히 더
  크고, 따라서 정확히 \(v_2 = v_2((n-k)!)\).
- **\(n\) 홀수:** 주장되는 부치가 모두 \(\le 3\)이고, mod 16에서 수열
  \(m \mapsto S_n(m)\)은 주기 16으로 주기적이다(홀수 잉여류는
  \(a^4 \equiv 1 \bmod 16\)을 만족하고, 각 계수 \(16!/j!\)(\(j<16\))는
  16으로 나누어진다). 모든 것이 홀수 잉여쌍 \((n \bmod 16, m \bmod 16)\)
  64개에 대한 유한 표 검사로 환원된다.

## 기계 검증

Lean 4(mathlib), `sorry` 없음:
[`AgenticConjectures/OeisA398189.lean`](../../AgenticConjectures/OeisA398189.lean)

| 정리 | 내용 |
|---|---|
| `valuation_even` | \(n\) 짝수 → \(v_2(T(n,k)) = v_2((n-k)!)\) (모든 \(k\)) |
| `valuation_odd_k0` | \(n\) 홀수 → \(v_2(T(n,0)) = 1\) |
| `valuation_odd_odd` | \(n\), \(k\) 홀수 → \(v_2(T(n,k)) = 0\) |
| `valuation_odd_even` | \(n\) 홀수, \(k\) 짝수, \(k \le n\), \(k \not\equiv 14 \,(16)\) → \(v_2(T(n,k)) = v_2(k+2)\) |
| `sixteen_dvd_excluded` | \(n\) 홀수, \(k \le n\), \(k \equiv 14 \,(16)\) → \(16 \mid T(n,k)\) |
| `T_eq_oeis_form` | Lean의 `T`가 OEIS 원문 합 \(\sum_j (n-k)!/j! \cdot n^j\)과 같음 |

유한 검사는 `decide`로 커널 검증한다(`native_decide`는 저장소 전체에서
금지). CI는 push마다 `lake build`, no-`sorry` 게이트, 공리 감사를 다시
실행한다.

실행 가능한 인증서
[`a398189_certificate.py`](a398189_certificate.py)는 (1) \(T\)의 두 독립
구현 상호 대조, (2) OEIS에 공개된 DATA 91항 재현, (3) \(n \le 220\)
(24,531쌍)에서 네 경우 + 제외 부류 하한, (4) mod 16 환원을 독립적으로
재검사한다. 저장소 루트에서:

    python3 problems/oeis-a398189/a398189_certificate.py

실행 시간: 1초 미만. 이는 유한 사례의 교차 검증일 뿐 증명이 아니며, 증명은
Lean 모듈이다.

## 연구 현황과 선행 연구

- \(k = 0\) 열은 고전적 결과다: Schenker 합 A063170의 2진 부치에 관한
  McGarvey의 추측(2007)은 T. Amdeberhan, D. Callan, V. Moll,
  *Valuations and combinatorics of truncated exponential sums*,
  [Integers 13 (2013), #A21](https://math.colgate.edu/~integers/n21/n21.Abstract.html)이
  증명했다(이후 P. Miska의 Schenker 합 \(p\)진 부치 연구도 있다).
- A398189가 추측한 \(k\)-일관 명제(2026-07)에 대해서는 2026-08-12 기준
  OEIS 항목에 증명 기록이 없고, 웹 검색으로도 찾지 못했다. 여기 보존된
  기여는 일관된 증명과 그 기계 검증 형태이며, 방법(2진 초거리 평가 +
  mod 16 주기성)은 표준적이다.
- 이는 검토되지 않은 기계 보조 작업이다: OEIS 편집자나 동료 검토의 확인을
  받지 않았고 **새로움을 주장하지 않는다**. 상류(OEIS 등)에는 아무것도
  제출하지 않았다(이 저장소 규칙상 외부 제출은 사람의 승인이 필요하다).
