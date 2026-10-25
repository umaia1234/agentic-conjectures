[English](README.md) | **한국어**

# OEIS A110566 — 모든 홀수가 나타나지는 않는다

## 판정

이 추측은 **반박**되었다. [OEIS A110566](https://oeis.org/A110566)은 다음과
같이 정의된다.

\[
a(n)=\frac{\operatorname{lcm}(1,2,\ldots,n)}{\operatorname{den}(H_n)},\qquad
H_n=\sum_{j=1}^{n}\frac1j\qquad(n\ge1).
\]

모든 \(n\)에 대해 3진 부치(3-adic valuation)는 다음을 만족한다.

\[
v_3\bigl(a(n)\bigr)\le 3 .
\]

따라서 \(81=3^4\)은 어떤 항으로도 나타나지 않으며, 81의 홀수 배수도 마찬가지다.
이 상계는 최선이다. 실제로 \(a(66)=27\)이다. 이 결과는 upstream 명제를 항
하나하나 그대로 옮긴 Lean 4 명제에 대해 형식화되었다. Lean 증명에는 `sorry`,
추가 공리, `native_decide`를 쓰지 않았다.

## 원래 명제

OEIS 항목(2023년 5월 17일 개정판 #39, 2026-10-24 확인)은 이 수열을
“lcm{1,2,...,n}/denominator of harmonic number H(n)”로 정의하며 오프셋은
1이다. 항목에는 다음 주석이 있다.

> “It is conjectured that every odd number occurs in this sequence (see
> A112822 for the first occurrence of each of them). - Jianing Song, Nov 28
> 2022”

[`upstream/`](upstream/README.md)의 Formal Conjectures 스냅샷(커밋
`c094b979118b89adb77cf5f8d923ac9dd2e51b1d`의
`FormalConjectures/OEIS/110566.lean`)은 `open Nat Finset Rat` 아래에서 이를
다음과 같이 서술한다.

```lean
def a (n : ℕ) : ℕ :=
  (Icc 1 n).lcm id / (harmonic n).den

theorem conjecture :
  ∀ m : ℕ, Odd m → ∃ n > 0, a n = m := by
  sorry
```

## 증명

\(v=v_3\), \(L_n=\operatorname{lcm}(1,\ldots,n)\),
\(k(n)=\lfloor\log_3 n\rfloor\)로 쓴다.

1. **\(H_n\)에서 \(a(n)\)으로.** \(H_n\)의 분모는 \(L_n\)을 나누므로
   \(L_n=a(n)\operatorname{den}(H_n)\)이다. 또한 \(v(L_n)=k(n)\)이고
   \(v(H_n)=v(\operatorname{num})-v(\operatorname{den})\ge-v(\operatorname{den}(H_n))\)이다.
   따라서
   \[
   v\bigl(a(n)\bigr)=k(n)-v\bigl(\operatorname{den}(H_n)\bigr)\le k(n)+v(H_n)=:f(n).
   \]
2. **3진 한 단계.** \(m=\lfloor n/3\rfloor\)로 두고 3의 배수 항을 따로 모으면
   다음을 얻는다.
   \[
   H_n=\frac{H_m}{3}+R_n,\qquad R_n=\sum_{j\le n,\;3\nmid j}\frac1j,\qquad v(R_n)\ge0 .
   \]
   \(n\ge3\)이고 \(v(H_m)\le0\)이라 하자. 그러면
   \(v(H_m/3)=v(H_m)-1<0\le v(R_n)\)이므로 \(v(H_n)=v(H_m)-1\)이다. 또
   \(k(n)=k(m)+1\)이므로 \(f(n)=f(m)\)이다.
3. **3진 트리 위의 귀납법.** \(n\)에 대한 강한 귀납법을 쓴다.
   \(m\notin\{2,7,22\}\)이면 2단계를 적용한다. 그렇지 않으면 \(n\)은 아홉 수
   \(6,7,8,21,22,23,66,67,68\) 중 하나이며, 이들과 뿌리 \(n=1,2\)는 직접
   확인한다.

   | \(n\) | \(H_n\) (기약분수) | \(v(H_n)\) | \(k(n)\) | \(f(n)\) |
   |---|---|---|---|---|
   | 2 | \(3/2\) | 1 | 0 | 1 |
   | 6 | \(49/20\) | 0 | 1 | 1 |
   | 7 | \(363/140\) | 1 | 1 | 2 |
   | 8 | \(761/280\) | 0 | 1 | 1 |
   | 21 | \(18858053/5173168\) | 0 | 2 | 2 |
   | 22 | \(19093197/5173168\) | 1 | 2 | 3 |
   | 23 | \(444316699/118982864\) | 0 | 2 | 2 |
   | 66 | \(209060999005535159677640233/43787662374178602500420800\) | 0 | 3 | 3 |
   | 67 | \(14050874595745034300902316411/2933773379069966367528193600\) | 0 | 3 | 3 |
   | 68 | \(14094018321907827923954201611/2933773379069966367528193600\) | 0 | 3 | 3 |

   이 귀납법에서 두 사실이 나온다. 첫째, \(v(H_n)>0\)인 것은 정확히
   \(n\in\{2,7,22\}\)일 때다. 이는 \(p=3\)에 대한 Eswarathasan–Levine의 알려진
   결과다. 둘째, 모든 \(n\)에 대해 \(f(n)\le3\)이다.
4. **결론.** 1단계에 의해 \(v(a(n))\le f(n)\le3\)이다. 따라서 모든 \(n\)에
   대해 \(81\nmid a(n)\)이다. 81은 홀수이므로 추측은 거짓이다.

## Lean 형식화

[`AgenticConjectures/OeisA110566.lean`](../../AgenticConjectures/OeisA110566.lean)
(이름공간 `AgenticConjectures.OeisA110566`):

| 선언 | 내용 |
|---|---|
| `a` | upstream 정의 그대로: `(Icc 1 n).lcm id / (harmonic n).den` |
| `statement` | upstream 추측 그대로: `∀ m : ℕ, Odd m → ∃ n > 0, a n = m` |
| `not_statement` | `¬ statement` (증인 \(m=81\)) |
| `not_eightyone_dvd_a` | \(\forall n,\ 81\nmid a(n)\) |
| `padicValNat_a_le` | \(\forall n,\ v_3(a(n))\le3\) |
| `padicValRat_harmonic_add_log_le` | \(\forall n,\ v_3(H_n)+\lfloor\log_3 n\rfloor\le3\) |
| `padicValRat_harmonic_pos_iff` | \(v_3(H_n)>0\iff n\in\{2,7,22\}\) |
| `padicValRat_harmonic_step` | \(n\ge3,\ v_3(H_{\lfloor n/3\rfloor})\le0\Rightarrow v_3(H_n)=v_3(H_{\lfloor n/3\rfloor})-1\) |
| `den_dvd_lcm` | \(\operatorname{den}(H_n)\mid\operatorname{lcm}(1,\ldots,n)\) |
| `a_6`, `a_66` | \(a(6)=3\) (upstream 검사 `a_6`)과 \(a(66)=27\) (상계가 실제로 달성됨) |

증명에 관한 참고:

- \(R_n:=H_n-H_{\lfloor n/3\rfloor}/3\)에 대해 \(v(R_n)\ge0\)을 \(n\)에 대한
  귀납법으로 증명한다. \(n\)에서 \(n+1\)로 갈 때 \(R\)은 그대로이거나
  (\(3\mid n+1\)일 때) \(3\nmid n+1\)인 \(1/(n+1)\)이 더해진다. 따라서 finset을
  나눌 필요가 없다.
- \(v_3(\operatorname{lcm}(1,\ldots,n))=\lfloor\log_3 n\rfloor\)은 mathlib의
  `Nat.factorization_lcmUpto`를 쓴다. `Nat.lcmUpto n`은 정의상
  `(Icc 1 n).lcm id`와 같다.
- 열 개의 조화수 값은 `norm_num`으로 계산한다. 두 확인용 값은 upstream 정의에
  대해 커널 `decide +kernel`로 검증한다.
- `#print axioms not_statement`는 `propext`, `Classical.choice`,
  `Quot.sound`만 보고한다.

## 명제의 충실성

- **정의.** `a`와 `statement`는 같은 `open Nat Finset Rat` 아래에서 그대로
  옮겼다. `module`/`public import`/`@[expose]` 골격은 `import Mathlib`으로
  바꾸었고, 메타데이터 속성 `@[category …]`와 `@[AMS …]`는 뺐다. Formal
  Conjectures에는 다른 `harmonic` 정의가 없으므로 `harmonic`은 mathlib의
  \(H_n=\sum_{i<n}1/(i+1)\)이다.
- **첨자 기준.** OEIS의 오프셋은 1이고 upstream은 `n > 0`에 대해 양화한다. 이
  파일도 같은 양화를 쓴다. Lean에서 `a 0 = 1`(빈 집합의 lcm은 1, \(H_0=0\)의
  분모는 1)이지만 명제에는 쓰이지 않는다. 상계 `padicValNat_a_le`는
  \(n=0\)에서도 성립한다.
- **자연수 나눗셈.** `a`의 `/`는 ℕ의 내림 나눗셈이다. `den_dvd_lcm`이
  \(\operatorname{den}(H_n)\mid L_n\)을 증명하므로 이 나눗셈은 정확하며, `a n`은
  OEIS가 쓰는 정확한 몫(A003418/A002805)과 같다.
- **분모.** `Rat.den`은 기약분수의 분모이므로 OEIS의 “denominator of
  harmonic number H(n)”(A002805)과 일치한다.
- **뺄셈 없음.** 명제에는 뺄셈이 없다. 증인은 \(m=81\)이며
  \(81=2\cdot40+1\)이므로 `Odd`이다.
- **버전.** upstream은 Lean/mathlib `v4.33.1`(mathlib 리비전
  `0df444a360eaa60ab8c11dca51a86af692955474`)을 고정하고, 이 저장소는
  `v4.30.0`을 쓴다. 2026-10-24에 그 리비전의 `harmonic` 정의가 우리 것과
  같음을 확인했다. `Finset.lcm`, `Finset.Icc`, `Rat.den`은 유한집합의
  최소공배수, 정수 구간, 기약분수의 분모라는 기본 개념이며 그 의미는 버전에
  따라 달라지지 않는다.

## 재현

저장소 루트에서 다음을 실행한다.

```bash
lake build AgenticConjectures.OeisA110566
python3 problems/oeis-a110566/a110566_certificate.py
python3 problems/oeis-a110566/a110566_certificate.py --limit 300000   # 선택 사항, 느림
```

2026-10-24 측정값(Apple M5 Max, 공유 장비):

- Lean 모듈은 캐시된 mathlib 빌드 위에서 8.1초 만에 빌드되었다.
- 기본값으로 실행한 인증서 스크립트는 약 4초 걸렸다.
- `--limit 100000`은 42초 걸렸다.
- `--limit 300000`은 403초(약 7분) 걸렸다.

[`a110566_certificate.py`](a110566_certificate.py)는 Python 표준 라이브러리만
쓴다. 이 스크립트는 수치 교차 검증이며 증명의 일부가 아니다. 확인하는 내용은
다음과 같다.

- Lean 증명에 하드코딩한 열 개의 기약분수와 그 3진 부치;
- OEIS DATA의 90개 항 \(a(1..90)\);
- \(n\le3000\)에서 정의 \(L_n/\operatorname{den}(H_n)\)과 Vrabec의 독립적인
  공식 \(\gcd(L_n, L_nH_n)\)의 일치;
- `--limit`(기본값 30000)까지의 \(n\)에 대해:
  - \(v_3(L_n)=\lfloor\log_3 n\rfloor\);
  - \(v_3(a(n))\le3\);
  - \(\{n : v_3(H_n)>0\}=\{2,7,22\}\);
  - 한 단계 점화식.

개발 중에 별도의 탐색용 gmpy2 실행으로 \(n\le300000\)에서
\(\max v_3(a(n))=3\)임을 확인했다. 그 실행은 [공식 b-file](https://oeis.org/A110566/b110566.txt)의
10000개 항과도 모두 일치했다.

## 주장하지 않는 것

- 어떤 홀수가 실제로 나타나는지에 대해서는 아무것도 주장하지 않는다. 예를 들어
  35, 47, 51, 69, 73의 첫 등장 위치는 [A112822](https://oeis.org/A112822)에
  여전히 미상(`?`)으로 적혀 있다.
- \(p\ge5\)인 소수에 대해 \(v_p(a(n))\le c_p\) 꼴의 상계는 주장하지 않는다.
  집합 \(\{n: v_p(H_n)>0\}\)이 유한하다고 알려진 경우에는 같은 방법이 통할 수
  있지만, 여기서는 시도하지 않았다.
- 인증서 스크립트는 Lean 증명을 대신하지 않는다.

## 선행 연구와 제출 현황

OEIS 항목(개정판 #39, 2026-10-24 확인)에는 여전히 이 추측이 실려 있고 반례는
기록되어 있지 않다. [A112822](https://oeis.org/A112822)(\(2n-1\)의 첫 등장
위치, 개정판 #18)는 \(2n-1=77\)까지의 값을 싣고 있다. 81은 결코 나타나지
않으므로, 이 정리에 따르면 A112822에는 \(2n-1=81\)에 해당하는 항이 없다.

핵심 재료인 \(\{n : v_3(H_n)>0\}=\{2,7,22\}\)는 알려진 결과를 재현한 것이다:
A. Eswarathasan and E. Levine, “p-integral harmonic sums”, *Discrete
Mathematics* 91 (1991), 249–257. 이 결과에서 \(v_3(a(n))\le3\)으로 가는 짧은
논증은 2026-10-24 수집 분류 과정에서 찾았다. 선행 연구는 OEIS(A110566,
A112822, A112810)에서만 확인했으며, 이 반박에 대해 더 넓은 문헌 조사는 하지
않았다. 새로움은 주장하지 않는다. 이 결과는 검토를 거치지 않았고, 외부 제출에는
사람의 승인이 필요하므로 OEIS에 보고하지 않았다.
