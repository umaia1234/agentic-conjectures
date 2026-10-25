[English](README.md) | **한국어**

# 크리스털 성분의 유일성 (arXiv:1601.03081)

## 추측

M. Abrate, S. Barbero, U. Cerruti, N. Murru의 논문 *The Biharmonic mean*
([arXiv:1601.03081](https://arxiv.org/abs/1601.03081), v1, 2016년 1월 12일)은 다음 값을 정의합니다.

B(a, b) = ((a + b)² + (ab + 1)²) / (2(a + 1)(b + 1)).

논문의 정의 5는 홀수 n이 a, b > 1이고 B(a, b) ∈ ℕ인 곱 n = ab로 쓰일 때 n을 **크리스털**(crystal)이라고
부릅니다. 가장 작은 크리스털은 35 = 5 · 7이며, 이때 B(5, 7) = 1440 / 96 = 15입니다.

저자들은 결론 절에서 n = cd이면서 B(c, d) ∈ ℕ인 다른 쌍 c, d > 1은 없다, 즉 "the components of the
crystals are unique"라고 추측하고, 증명이나 반례가 쉽게 나오지는 않을 것 같다고 덧붙입니다. Formal
Conjectures는 커밋 `c094b97`에서 이 추측을 `research open` 태그를 붙여 `crystals_components_unique`로
적어 두었습니다.

```lean
def IsCrystalWithComponents (n a b : ℕ) : Prop :=
  Odd n ∧ 1 < a ∧ 1 < b ∧ n = a * b ∧ 2 * (a + 1) * (b + 1) ∣ (a + b)^2 + (a * b + 1)^2

theorem crystals_components_unique (n a b c d : ℕ)
    (hab : IsCrystalWithComponents n a b) (hcd : IsCrystalWithComponents n c d) :
    ({a, b} : Finset ℕ) = {c, d} := by
  sorry
```

upstream 파일 원본은 [upstream/](upstream/README.md)에 보관했습니다.

## 결과

**상태: partial.** 추측은 증명되지 않았습니다. 확립한 내용은 다음과 같습니다.

1. **Lean: 동치 조건** (논문의 명제 1. 앞의 두 조건은 아직 열려 있는 Formal Conjectures PR #7051에도
   있습니다). 홀수 a, b > 1에 대해 n = ab가 크리스털일 필요충분조건은 (a + 1)(b + 1) ∣ (a + b)²이고,
   이는 (a + 1)(b + 1) ∣ (n + 1)²과 동치이며, u = (a + 1)/2, v = (b + 1)/2로 두면 u ∣ (v − 1)²이고
   v ∣ (u − 1)²인 것과도 동치입니다.
2. **Lean: 분류** (논문의 정리 4와 5). n = ab가 크리스털일 필요충분조건은 어떤 정수 k에 대해
   (a + 1)/2와 (b + 1)/2가 순서와 관계없이 수열 u₀ = 0, u₁ = 1, u_{m+2} = (k − 2)u_{m+1} − u_m + 2의
   연속한 두 항이고 둘 다 2 이상인 것입니다. k로는 3 이상의 정수인 k = (a + b)² / ((a + 1)(b + 1))을
   잡을 수 있습니다. 닫힌 형태로 쓰면 {a + 1, b + 1} = {2kp², 2(p + r)²}이고, 여기서 p, r ≥ 1은
   (p + r)² = kpr + 1을 만족하는 뤼카(Lucas) 수열의 연속한 두 항입니다.
3. **Lean: 환원.** 모든 크리스털은 (a + b)² = k(n + 1 + a + b)를 만족하므로 n과 k가 {a, b}를 결정합니다.
   따라서 추측은 *같은 n의 크리스털 분해는 모두 같은 k를 갖는다*는 명제와 동치입니다.
4. **Lean: 세 가지 경우.** n과 k가 같은 두 크리스털은 일치합니다. k = 3은 35 = 5 · 7에서만 나타납니다.
   j = 1 족 {2k − 1, 2(k − 1)² − 1}의 서로 다른 두 크리스털은 n을 공유하지 않습니다.
5. **컴퓨터 보조 증명(계산한 사실 하나를 가정한 Lean 증명).** k = 4 족 {2t² − 1, 2(t + 1)² − 1}과
   j = 1 족이 공유하는 n은 n = 119 = 7 · 17뿐이며, 이는 두 족에 동시에 속하는 하나의 크리스털입니다.
   Lean은 랭크(rank)가 2인 타원곡선의 정수점 목록으로부터 이를 증명합니다(`eq_of_crystalK_eq_four_of_j1`).
   그 목록은 Sage/PARI로 계산한 것이며 정리에 명시적인 가정(`EllipticCurveIntegralPoints`)으로 들어갑니다.
6. **계산.** 서로 독립적인 두 프로그램이 n ≤ 2¹²⁷ − 1인 크리스털 3,493,319,443,273개에서 충돌을 찾지
   못했습니다. 그중 하나는 j ≥ 2인 크리스털에 대한 검사를 n ≤ 10⁴⁰까지 확장합니다.

모든 크리스털은 불변량 k와, 그 k의 사슬에서의 위치 j에 따라 정확히 네 부류 중 하나에 속합니다. k 사슬의
j번째 크리스털은 위 수열의 쌍 (u_{j+1}, u_{j+2})입니다.

| 부류 | 정의 | 성분 {a, b} | n ≤ 2¹²⁷ − 1인 크리스털 수 |
| --- | --- | --- | ---: |
| F3 | k = 3 | {5, 7} | 1 |
| F4 | k = 4 | {2t² − 1, 2(t + 1)² − 1}, t ≥ 2 | 2,553,802,832 |
| F1 | k ≥ 5, j = 1 | {2k − 1, 2(k − 1)² − 1} | 3,490,731,829,162 |
| S | k ≥ 5, j ≥ 2 | 점화식으로 생성 | 33,811,278 (j ≤ 43) |

n을 공유하지 않는다고 알려진 부류 쌍은 다음과 같습니다.

| 쌍 | 상태 |
| --- | --- |
| k가 같은 임의의 두 크리스털 | Lean, `eq_of_crystalK_eq` |
| F3과 임의의 크리스털 | Lean, `eq_of_crystalK_eq_three` |
| F1과 F1 | Lean, `eq_of_j1` |
| F4와 F1 | Lean, `eq_of_crystalK_eq_four_of_j1`. [`ec_k4_j1.py`](ec_k4_j1.py)(Sage/PARI)가 계산한 타원곡선의 정수점 목록을 가정함 |
| S와, k가 다른 F1, F4 또는 S | **미해결**. n ≤ 2¹²⁷ − 1에서 충돌 없음(두 프로그램), n ≤ 10⁴⁰에서 충돌 없음(한 프로그램) |

남은 미해결 부분은 마지막 행, 즉 부류 S의 크리스털이 k가 다른 크리스털과 n을 공유하는 경우입니다.

## 증명 아이디어

1. **나눗셈 조건.** D = (a + 1)(b + 1), s = a + b로 두면 ab + 1 = D − s입니다. a가 홀수이면
   s² + (ab + 1)² = 2(s² + D · ((a − 1)/2)(b − 1))이므로, 2D가 이 값을 나누는 것은 D ∣ s²과 동치입니다.
   또 (ab + 1)² = s² + D(D − 2s)이므로 D ∣ s²은 D ∣ (n + 1)²과 동치입니다.
2. **(u, v) 형태.** a + 1 = 2u, b + 1 = 2v로 두면 D = 4uv, s = 2(u + v − 1)이므로 조건은
   uv ∣ (u + v − 1)²이 되고, 이는 u ∣ (v − 1)²과 v ∣ (u − 1)²으로 나뉩니다. k = (u + v − 1)²/(uv)로 두면
   (u + v − 1)² − 2uv = (u − 1)² + (v − 1)² − 1 > 0이므로 k ≥ 3입니다.
3. **비에타 하강.** y를 고정하면 (x + y − 1)² = kxy의 두 근 x, x′은 x + x′ = (k − 2)y + 2,
   xx′ = (y − 1)²을 만족합니다. 큰 좌표를 그 짝으로 바꾸어 가면 쌍 (1, k)까지 내려가고, 거꾸로 올라가면
   점화식이 나옵니다. 이것으로 논문의 정리 4와 5가 증명됩니다(논문은 정리 4를 참고문헌 [1]에서
   가져옵니다).
4. **닫힌 형태.** L을 L₀ = 0, L₁ = 1, L_{i+2} = (k − 2)L_{i+1} − L_i인 뤼카 수열이라 하면
   u_{2i} = kL_i², u_{2i+1} = (L_i + L_{i+1})²이고, 연속한 항은 L_{i+1}² − (k − 2)L_iL_{i+1} + L_i² = 1을
   만족합니다. (p, r) = (L_i, L_{i+1})에 대해 이 식은 (p + r)² = kpr + 1입니다.
5. **환원.** a + b = 2(u + v − 1)이고 D = n + 1 + (a + b)이므로 (a + b)² = k(n + 1 + a + b)입니다. n과 k를
   고정하면 이 이차방정식의 양의 근은 하나뿐이므로, a + b와 ab = n이 {a, b}를 결정합니다.
6. **경우.** k = 3이면 사슬이 1, 3, 4, 3, 1, …이므로 크리스털은 5 · 7뿐입니다. j = 1 족에서
   n = (2k − 1)(2(k − 1)² − 1)은 k에 대해 순증가합니다. k = 4 족과 j = 1 족의 n이 같다는 것은
   X = t(t + 1)에 대해 (2X − 1)² = 4K³ − 10K² + 6K + 1이라는 뜻이고, x = 4K, y = 4(2X − 1)로 두면 이는
   타원곡선 y² = x³ − 10x² + 24x + 16이 됩니다. 그 정수점에서 K ∈ {0, 1, 4, 21, 300}이 나오고, 그중
   X가 t ≥ 2인 t(t + 1) 꼴인 것은 K = 4뿐입니다.

[DETAILS.ko.md](DETAILS.ko.md)에 모든 단계, 타원곡선 논증, 알고리즘과 그 완전성 논증, 그리고 남은 경우가
어려운 이유에 대한 설명이 있습니다.

## Lean 형식 증명

[`AgenticConjectures/CrystalComponentsUnique.lean`](../../AgenticConjectures/CrystalComponentsUnique.lean)은
미해결 명제를 `statement`로 기록하고 아래 결과를 증명합니다. `sorry`, 추가 공리, `native_decide`를 쓰지
않으며, `#print axioms`는 `propext`, `Classical.choice`, `Quot.sound`만 출력합니다. 계산으로 얻은 유일한
사실인 타원곡선의 정수점 목록은 `def` `EllipticCurveIntegralPoints`로 정의되어
`eq_of_crystalK_eq_four_of_j1`의 가정으로만 쓰이며, 공리가 아닙니다.

| 선언 | 내용 |
| --- | --- |
| `IsCrystalWithComponents`, `isCrystalWithComponents_35_5_7` | upstream 정의와 테스트 사례를 항 단위로 그대로 옮긴 것. |
| `statement` | upstream 정리를 전칭 양화한 명제(증명하지 않음). |
| `dvd_biharmonic_iff`, `dvd_sq_add_iff_dvd_mul_add_one_sq` | 2(a + 1)(b + 1) ∣ (a + b)² + (ab + 1)² ⟺ (a + 1)(b + 1) ∣ (a + b)² (a 홀수) ⟺ (a + 1)(b + 1) ∣ (ab + 1)². |
| `isCrystal_iff_dvd_sq_add`, `isCrystal_iff_dvd_succ_sq` | 명제 1을 `IsCrystalWithComponents`의 특성화로 쓴 것. |
| `isCrystal_iff_uv_dvd`, `isCrystal_iff_uv` | (u, v) 형태: uv ∣ (u + v − 1)², 그리고 u ∣ (v − 1)² ∧ v ∣ (u − 1)². |
| `crystalK`, `IsCrystalWithComponents.sq_add_eq_mul`, `.three_le_crystalK` | k = (a + b)² / ((a + 1)(b + 1)); (a + b)² = k(n + 1 + a + b); k ≥ 3. |
| `eq_of_crystalK_eq` | n과 k가 같은 두 크리스털 분해는 일치함. |
| `statement_iff_crystalK_eq` | 추측 ⟺ 같은 n의 두 크리스털 분해는 항상 같은 k를 가짐. |
| `IsCrystalWithComponents.eq_five_seven_of_crystalK_eq_three`, `.eq_five_seven_of_eq_35`, `eq_of_crystalK_eq_three` | k = 3은 {5, 7}에서만 나타나고, n = 35를 공유하는 다른 크리스털은 없음. |
| `seqU`, `seqU_invariant`, `sq_eq_mul_iff_seqU` | 논문의 수열 u(w)와 정리 4: (x + y − 1)² = wxy의 양의 해는 연속한 두 항의 쌍(두 순서 모두)임. |
| `IsCrystalWithComponents.exists_seqU`, `isCrystal_iff_seqU` | 정리 5: 점화식에 의한 크리스털의 분류. |
| `lucas`, `lucas_cassini`, `lucas_nonneg_lt`, `seqU_lucas` | 뤼카 수열과 u_{2i} = wL_i², u_{2i+1} = (L_i + L_{i+1})². |
| `isCrystal_iff_kpr`, `crystalK_eq_of_kpr` | 닫힌 형태 {a + 1, b + 1} = {2kp², 2(p + r)²}, (p + r)² = kpr + 1과, 이때 k = `crystalK a b`. |
| `isCrystal_iff_pronic` | 크리스털 ⟺ 어떤 k, q에 대해 n + 1 = kq(q + 1)이고 a + b = k(q + 1). |
| `IsCrystalWithComponents.crystalK_eq_four_iff` | k = 4 ⟺ {(a + 1)/2, (b + 1)/2} = {t², (t + 1)²}, t ≥ 2. |
| `IsCrystalWithComponents.j1`, `eq_of_j1` | a + 1 = 2k이면 b + 1 = 2(k − 1)²이고, n이 같은 두 크리스털은 일치함. |
| `EllipticCurveIntegralPoints` | 증명하지 않음(Sage/PARI의 출력): y² = x³ − 10x² + 24x + 16의 모든 정수점은 x ∈ {0, 3, 4, 6, 10, 16, 19, 84, 1200}을 만족함. |
| `eq_of_crystalK_eq_four_of_j1` | `EllipticCurveIntegralPoints`를 가정하면, n이 같은 k = 4인 크리스털과 j = 1인 크리스털은 일치함. |

## 명제 충실성

- **정의.** `IsCrystalWithComponents`는 Formal Conjectures의 정의를 항 단위로 그대로 옮긴 것입니다.
  B(a, b) ∈ ℕ을 분자가 (0이 아닌) 분모로 나누어떨어진다는 조건으로 표현하며, "n = ab인 홀수 n"은 정의 5와
  정확히 같습니다.
- **명제.** `statement`는 upstream 정리의 인자 n, a, b, c, d와 두 가정을 전칭 양화한 것이며, 결론
  `({a, b} : Finset ℕ) = {c, d}`는 바꾸지 않았습니다. 이 결론은 두 성분 비순서쌍이 같다는 뜻이고, 논문의
  "different from the couple a, b"에 해당합니다.
- **자연수 나눗셈.** `crystalK a b`는 내림하는 `ℕ` 나눗셈으로 정의되어 있습니다. 크리스털에서는 이
  나눗셈이 정확하므로(`IsCrystalWithComponents.sq_add_eq`) 논문의 Q(a, b)와 같으며, `crystalK`를 쓰는
  정리는 모두 크리스털을 가정합니다.
- **뺄셈.** 수열 `seqU`와 `lucas`는 ℤ에서 정의되므로 점화식에 잘린 뺄셈이 없습니다. `ℕ` 뺄셈은
  `IsCrystalWithComponents.j1`의 `crystalK a b - 1` 하나뿐인데, 여기서 k ≥ 3입니다.
- **순서와 첨자 범위.** 논문은 정리 4를 n ≥ 1에 대해 (x, y) = (u_n, u_{n−1})로 쓰고, 정리 5에서는 a를
  뒤쪽 항으로 둡니다. 방정식은 대칭이고 (u₁, u₀) = (1, 0)은 양의 쌍이 아니므로, Lean 버전은 두 순서를
  모두 허용하고 두 항이 양수(정리 4) 또는 2 이상(정리 5)이기를 요구합니다.
- **도구 버전.** 이 저장소는 Lean과 mathlib `v4.30.0`으로 빌드하고, `c094b97`의 Formal Conjectures는
  `v4.33.1`을 고정합니다. 정의는 `ℕ` 위의 `Odd`, `∣`, `*`, `^`만, 명제는 `Finset` 삽입만 쓰며, 이들의
  의미는 두 버전에서 같습니다. 이 파일을 `v4.33.1`에서 컴파일해 보지는 않았습니다.
- **수정 사항**(모듈 docstring에도 적어 두었습니다): `public import FormalConjecturesUtil` 대신
  `import Mathlib`을 쓰고, `module` 키워드, `@[expose] public section`, `@[category …]`/`@[AMS …]` 속성을
  뺐으며, 이름공간 `Arxiv.«1601.03081»`을 `AgenticConjectures.CrystalComponentsUnique`로 바꿨습니다.

## 계산

`direct_check.py`를 제외한 계산은 완전성을 Lean 분류에 의존합니다.

- [`crystal_search.c`](crystal_search.c) (구현 A): 128비트 정수를 쓰는 C 프로그램입니다. k ≥ 5마다 뤼카 쌍
  (p, r)을 따라가며 S의 크리스털을 두 방향 모두 나열해 정렬한 다음, 모든 S 원소와 모든 F4 원소에 대해
  F1과 F4의 닫힌 형태를 정확히 역산합니다. 모든 곱은 2¹²⁸ − 1에서 포화되며, 이 값은 허용되는 모든 상한
  X ≤ 2¹²⁷ − 1보다 큽니다.
- [`crystal_exact.py`](crystal_exact.py) (구현 B): 정확한 정수와 표준 라이브러리만 쓰는 Python
  프로그램입니다. 뤼카 쌍 대신 (u, v) 점화식을 따라가고, 부동소수점 추정 대신 정수 거듭제곱근을 씁니다.
  A와 공유하는 코드가 없습니다.
- [`direct_check.py`](direct_check.py): 모든 u ≥ 2와 (u − 1)²의 약수 v ≥ u를 나열해 원래 정의를 검사하고,
  찾은 크리스털을 분류합니다. 분류를 쓰지 않으므로 10¹⁴까지는 분류 자체도 검사합니다.
- [`ec_k4_j1.py`](ec_k4_j1.py): F4와 F1에 대한 타원곡선 계산입니다.

모든 프로그램은 부류별 크기, 가장 큰 j, 전체 개수, S 원소의 체크섬(합을 2⁶⁴로 나눈 나머지), 충돌 개수를
출력합니다. 측정은 Apple M5 Max(다른 작업과 공유)에서 했고, 전체 출력은 [logs/](logs/crystal_search.log)에
있습니다.

| 상한 X | 프로그램 | n ≤ X인 크리스털 | S 원소(가장 큰 j) | 충돌 | 시간 |
| --- | --- | ---: | ---: | ---: | ---: |
| 10¹² | A, B, `direct_check.py` | 7,266 | 264 (12) | 0 | 0.1초, 0.02초, 2.4초 |
| 10¹⁴ | A, B, `direct_check.py` | 32,094 | 622 (14) | 0 | 0.1초 미만, 0.02초, 32초 |
| 10³⁴ | A(스레드 4개), B | 135,949,335,491 | 4,847,868 (38) | 0 | 2.4초, 18초 |
| 2¹²⁷ − 1 | A(스레드 4개), B | 3,493,319,443,273 | 33,811,278 (43) | 0 | 26초(CPU 89초, 1.1 GB), 168초(1.9 GB) |
| 10⁴⁰ | B | 13,579,235,391,289 | 76,240,507 (45) | 0 | 353초(4.3 GB) |

- 모든 상한에서 프로그램들의 부류별 개수와 S 체크섬이 모두 일치합니다.
- A는 모든 F4 원소를 F1과 비교합니다. B는 `--f4-limit`로 준 상한까지만 비교합니다(X = 10³⁴에서는 10²⁴,
  더 큰 상한에서는 10³⁰). 어차피 이 쌍은 타원곡선 계산이 모든 n에 대해 다룹니다. 2¹²⁷ − 1을 넘는 범위는
  B만 돌렸으므로, 10⁴⁰ 실행의 S 결과는 구현 하나에만 의존합니다.
- `ec_k4_j1.py`는 약 2초 걸립니다. PARI `ellrank`로 랭크가 2임을 보이고, 찾은 두 점이 모델-베유 군을
  생성함을 보이며(표준 높이(canonical height)의 하계에서 얻은 지수 상계 5.96, 그리고 100 이하의 모든 소수에서 PARI
  `ellsaturation`), Sage로 정수점을 나열합니다. 또 K ≤ 10⁶의 직접 탐색과 결과를 비교합니다.

## 선행 연구와 상태

2026-10-25(UTC)에 확인했습니다.

- **논문.** arXiv에는 v1만 있습니다. OpenAlex(W4293570946)에는 이 논문을 인용한 연구가 없고, biharmonic
  mean에 대한 arXiv 검색에서도 후속 연구가 나오지 않습니다.
- **Formal Conjectures.** `crystals_components_unique`는 `c094b97`과 `main` `37f0808`에서 `research open`
  입니다. 아직 열려 있는
  [google-deepmind/formal-conjectures#7051](https://github.com/google-deepmind/formal-conjectures/pull/7051)
  (마지막 갱신 2026-10-10)은 명제 1을 형식화하는데, 여기에는 이 저장소의 `dvd_biharmonic_iff`,
  `dvd_sq_add_iff_dvd_mul_add_one_sq`, `isCrystal_iff_dvd_sq_add`, `isCrystal_iff_dvd_succ_sq`가 증명하는
  동치가 포함되며, 논문 3절의 점화식 특성화는 TODO로 남아 있습니다. 그 밖에 진전을 주장하는 이슈나 풀
  리퀘스트는 없습니다.
- **기타.** 이 명제는 FC100 미해결 부분집합에 들어 있습니다. GitHub 코드 검색에서는 벤치마크 저장소와
  추적 저장소에 있는 사본만 나오고 증명이나 반례는 나오지 않습니다. Zenodo에는 해당 기록이 없습니다.
  OEIS에는 크리스털 수열이 없으며, 논문이 언급하는 A210494(biharmonic numbers)가 관련 수열입니다.
- **논문에 이미 있는 것.** 명제 1과 분류(정리 4와 5. 정리 4는 Abrate, Barbero, Cerruti, Murru,
  *Polynomial sequences on quadratic curves*, Integers, 2015에서 가져온 것입니다)는 논문에 있습니다. 이에
  대한 Lean 증명은 알려진 결과의 형식화입니다. k로의 환원, 경우별 결과, 계산은 위 출처들에서 찾지
  못했습니다.

결과를 찾지 못했다고 해서 새로움이 입증되는 것은 아니며, 새로움을 주장하지 않습니다. 이 작업은 사람이
검토하지 않았습니다. AI 모델이 만들었고, Lean 커널, PARI/Sage, 위의 교차 검증으로만 확인했습니다. Formal
Conjectures나 다른 곳에 제출하지 않았으며, 외부 제출에는 사람의 승인이 필요합니다.

## 재현

저장소 루트에서:

```bash
lake build AgenticConjectures.CrystalComponentsUnique
python3 scripts/check_axioms.py
```

mathlib이 빌드되어 있으면 모듈 컴파일에 약 7초 걸립니다.

이 디렉터리에서(C 프로그램에는 C 컴파일러가, `ec_k4_j1.py`에는 Sage 또는 pip 패키지 passagemath-schemes,
passagemath-pari, passagemath-symbolics가 필요합니다):

```bash
python3 direct_check.py 1e12
python3 direct_check.py 1e14
python3 crystal_exact.py 1e34 --f4-limit 1e24
python3 crystal_exact.py 2^127-1 --f4-limit 1e30
python3 crystal_exact.py 1e40 --f4-limit 1e30
cc -O2 -o /tmp/crystal_search crystal_search.c -lm -lpthread && /tmp/crystal_search 1e34 2
/tmp/crystal_search max 4
sage -python ec_k4_j1.py
```

CI는 상한 10¹²과 10³⁴을 다시 실행해 [`logs/summary_1e12.txt`](logs/summary_1e12.txt),
[`logs/summary_1e34.txt`](logs/summary_1e34.txt)와 비교합니다.
