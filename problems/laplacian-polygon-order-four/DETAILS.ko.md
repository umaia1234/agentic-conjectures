[English](DETAILS.md) | **한국어**

# 4차 다각형 질문: 상세

이 파일은 [README.ko.md](README.ko.md) 뒤에 있는 전체 논증을 담습니다. 질문 1을 유한 개 면
위의 두 다항식 부등식으로 줄이는 Lean 환원, 그 부등식들의 정확한 인증서, 면 궤도 통계, 수치
교차 확인, 다른 연구와의 관계를 다룹니다. Lean 이름은 이름공간
`AgenticConjectures.LaplacianPolygonOrderFour`를 가리킵니다(모듈
[`AgenticConjectures/LaplacianPolygonOrderFour.lean`](../../AgenticConjectures/LaplacianPolygonOrderFour.lean)과
그 폴더).

## 1. 설정

4차 표준화 라플라시안은 행 합이 0이고 $i \ne j$에서 $-1/4 \le \tilde\ell_{ij} \le 0$인 실
$4 \times 4$ 행렬 $\tilde L$입니다(`IsStdLaplacian`). $\Lambda_4$는 이런 행렬 전체의 복소
고윳값 전체의 집합입니다(`Λ₄`, `IsEig`, `isEig_iff_det`).

**척도를 뺀 가중치.** 열두 개의 호 $i \ne j$에 대해 $b_{ij} = -4\tilde\ell_{ij} \in [0,1]$로
두고, $D$를 나가는 차수의 대각 행렬이라 할 때 $L = \operatorname{lap} b = D - B$로 둡니다.
그러면 $L = 4\tilde L$이고, `mem_Λ₄_iff`는 $z \in \Lambda_4$일 필요충분조건이 어떤
$b \in [0,1]^{12}$(`InBox`)에 대해 $4z$가 $\operatorname{lap} b$의 고윳값인 것임을 말합니다.
$S_4$의 반평면 형태(`S4_eq`, 2절)를 쓰면 질문 1은 다음과 같습니다. 모든
$b \in [0,1]^{12}$와 $L$의 모든 고윳값 $w$에 대해

$$
|\operatorname{Im} w| \le 1, \qquad |\operatorname{Im} w| \le \operatorname{Re} w, \qquad
|\operatorname{Im} w| \le 4 - \operatorname{Re} w .
$$

첫 번째 한계만 따로 떼면 $z(4) = 1/4$(`z4_statement`)입니다.

## 2. 육각형과 $S_4 \subseteq \Lambda_4$

- `S4_eq`: $0, (1 \pm i)/4, (3 \pm i)/4, 1$의 볼록 껍질은
  $\{|\operatorname{Im} z| \le \operatorname{Re} z,\ |\operatorname{Im} z| \le 1 - \operatorname{Re} z,\ |\operatorname{Im} z| \le 1/4\}$
  입니다. 여섯 꼭짓점이 이 볼록 집합에 들어가므로 볼록 껍질도 그 안에 있습니다. 거꾸로
  `zono_coords`는 육각형의 점을 $s_k \in [0,1]$로
  $s_1 \tfrac{1+i}{4} + s_2 \tfrac12 + s_3 \tfrac{1-i}{4}$ 꼴로 쓰고, 꼭짓점 사이의 다중선형
  보간으로 이 점이 볼록 껍질에 있음을 보입니다.
- `S4_subset_Λ4`: 첫 행이
  $\bigl(\tfrac{s_1+s_2+s_3}{4}, -\tfrac{s_1}{4}, -\tfrac{s_2}{4}, -\tfrac{s_3}{4}\bigr)$인 순환
  행렬은 표준화 라플라시안이고, $(1, -i, -1, i)$는 고윳값
  $s_1 \tfrac{1+i}{4} + s_2 \tfrac12 + s_3 \tfrac{1-i}{4}$의 고유벡터입니다. 이것은 Agaev와
  Chebotarev의 정리 6(모든 $S_n$의 점은 어떤 순환 행렬의 고윳값)의 $n = 4$ 경우입니다.
- Lean으로 증명한 두 가지 구체적인 예: `cycle_eig`($(1+i)/4$, 유향 4-사이클)와 `h4_eig`
  ($(3+2i)/8$, 가중치 1/2인 현 $0 \to 2$와 $1 \to 3$을 더한 4-사이클). 두 번째 점은 윗변
  $\operatorname{Im} z = 1/4$ 위에 있습니다.

## 3. 특성다항식과 $\Phi$ 판정법

**삼차 인수.** `det_sub_lap`는
$\det(x - L) = x(x^3 - \sigma_1 x^2 + \sigma_2 x - \sigma_3)$을 증명합니다. 여기서
$\sigma_k$는 $L$의 $k \times k$ 주소행렬식들의 합입니다(`σ₁`, `σ₂ = c2 (lap b)`,
`σ₃ = c3 (lap b)`). 따라서 0이 아닌 모든 고윳값은 삼차식의 근 $r_a$이고
(`cubic_root_of_isEig`), 삼차식의 모든 근은 고윳값입니다(`isEig_of_cubic_root`).

**다항식.**

$$
\Phi = \underbrace{\sigma_1^2\sigma_2^2 - 4\sigma_2^3 - 4\sigma_1^3\sigma_3 + 18\sigma_1\sigma_2\sigma_3 - 27\sigma_3^2}_{\operatorname{Disc}}
  + 4(\sigma_1^2 - 3\sigma_2 + 4)^2 = \prod_{a<b}\bigl((r_a - r_b)^2 + 4\bigr).
$$

이는 열두 가중치에 대한 6차 다항식입니다.

**실수가 아닌 근** (`phiPoly_eq`). 근이 $c$와 $\alpha \pm i\beta$($\beta \ne 0$)이면
$c = \sigma_1 - 2\alpha$이고, $u = c - \alpha$로 두면

$$
\Phi = 4(1 - \beta^2)\,\bigl|(u - i\beta)^2 + 4\bigr|^2
     = 4(1 - \beta^2)\bigl((u^2 - \beta^2 + 4)^2 + 4u^2\beta^2\bigr).
$$

마지막 인수는 $u = 0$이고 $\beta^2 = 4$일 때만 0이 됩니다. 이것이 사전 탐색 실행이 짚은
퇴화 경우입니다. 이때 $|\beta| = 2 > 1$인데도 $\Phi = 0$입니다.

**Bendixson 한계** (`im_le_three_halves`). 가중치가 $[0,1]$에 있으면 모든 고윳값은
$|\operatorname{Im} w| \le 3/2$를 만족합니다. $p + iq$가 $\alpha + i\beta$의 고유벡터이면
$\beta \sum_i (p_i^2 + q_i^2) = \sum_{i<j} (L_{ij} - L_{ji})(p_i q_j - q_i p_j)$이고,
$|L_{ij} - L_{ji}| \le 1$, $|p_i q_j - q_i p_j| \le (p_i^2 + q_i^2 + p_j^2 + q_j^2)/2$이며,
각 첨자는 세 쌍에 나타납니다. 따라서 $\beta^2 \le 9/4 < 4$이고 퇴화 경우는 일어나지 않습니다
(`bracket_pos`, `Φ_eq_of_isEig`).

**판정법.** $b \in [0,1]^{12}$에 대해
- `phi_criterion`: $\Phi(b) \ge 0$이면 모든 고윳값 $w$가 $|\operatorname{Im} w| \le 1$을
  만족합니다.
- `phi_neg_of_im`: $|\operatorname{Im} w| > 1$인 고윳값이 있으면 $\Phi(b) < 0$입니다.
- `phi_nonneg_of_im_le` (역): 모든 고윳값이 $|\operatorname{Im} w| \le 1$이면
  $\Phi(b) \ge 0$입니다. 삼차식이 실근 $r$을 가지면 $(x - r)(x^2 - px + q)$와 같고,
  `phiPoly_factor`는
  $\Phi = \bigl((r^2 - pr + q)^2 + 8(r - p/2)^2 + 2(p^2 - 4q) + 16\bigr)(p^2 - 4q + 4)$를
  줍니다. $x^2 - px + q$의 근이 $|\operatorname{Im}| \le 1$을 만족하므로 두 번째 인수는
  $\ge 0$입니다. 그러면 첫 번째 인수도 $\ge 0$입니다. $p^2 - 4q \ge 0$이면 음이 아닌 항들의
  합이고, 그렇지 않으면 $p^2 - 4q \ge -4$이므로 $2(p^2 - 4q) + 16 \ge 8$입니다.

## 4. 섹터 한계와 $\Psi$ 판정법

**Gershgorin** (`re_pos_of_isEig`). 가중치가 음이 아니면 0이 아닌 모든 고윳값 $w$는 중심
$d$, 반지름 $d$인 원판에 놓이므로 $\operatorname{Re} w > 0$입니다.

**다항식.** $e_1, e_2, e_3$를 근의 제곱 $r_a^2$의 기본 대칭함수라 합니다:
$e_1 = \sigma_1^2 - 2\sigma_2$, $e_2 = \sigma_2^2 - 2\sigma_1\sigma_3$, $e_3 = \sigma_3^2$.
$\Psi = e_1 e_2 - e_3$(`sectorPoly`, `Ψ`)로 둡니다.

**실수가 아닌 근** (`sectorPoly_eq`). 근이 $c$와 $\alpha \pm i\beta$($\beta \ne 0$)이면

$$
\Psi = 2(\alpha^2 - \beta^2)\bigl((c^2 + \alpha^2 - \beta^2)^2 + 4\alpha^2\beta^2\bigr).
$$

Gershgorin에 의해 $\alpha > 0$이므로 마지막 인수는 양수이고, $\Psi \ge 0$일 필요충분조건은
$|\beta| \le \alpha$입니다.

**판정법.**
- `sector_criterion`: $b \in [0,1]^{12}$에서 $\Psi(b) \ge 0$이면 모든 고윳값 $w$가
  $|\operatorname{Im} w| \le \operatorname{Re} w$를 만족합니다.
- `psi_nonneg_of_sector` (역): 모든 고윳값이
  $|\operatorname{Im} w| \le \operatorname{Re} w$를 만족하면 $\Psi \ge 0$입니다. 실근 경우에
  `sectorPoly_factor`는 $\Psi = (p^2 - 2q)(r^4 + r^2(p^2 - 2q) + q^2)$를 주며,
  $p^2 - 2q = u^2 + v^2$는 $x^2 - px + q$의 근의 제곱의 합입니다. 근이 실수이면 이 합은
  $\ge 0$이고, 근이 $|\beta'| \le \alpha'$인 $\alpha' \pm i\beta'$일 때도 이 합은
  $2(\alpha'^2 - \beta'^2) \ge 0$입니다.

**보수 변환** (`isEig_compl`, `inBox_compl`). 사상 $b \mapsto 1 - b$는 상자를 보존하고,
$J$를 모든 성분이 1인 행렬이라 할 때
$\operatorname{lap}(1 - b) = 4I - J - \operatorname{lap} b$입니다(`lap_compl_apply`).
$w \ne 0$에 대한 $\operatorname{lap} b$의 왼쪽 고유벡터 $y$는 $\sum_i y_i = 0$을 만족하므로
$yJ = 0$이고 $y \operatorname{lap}(1 - b) = (4 - w)y$입니다. $1 - b$에 0에서의 섹터 한계를
적용하면 $|\operatorname{Im} w| \le 4 - \operatorname{Re} w$를 얻습니다. 보수 변환은 $\Phi$도
보존합니다. 0이 아닌 근을 $r \mapsto 4 - r$로 옮기므로 차 $r_a - r_b$는 부호만 바뀝니다.

**참고.** $n = 4$에서 두 섹터 한계는 Agaev와 Chebotarev의 정리 5에서도 나옵니다. 그 영역은
$e^{\pm(\pi/2 - \pi/n)i}$를 지나는 반직선들로 둘러싸인 0에서의 각과, 그에 대응하는 1에서의
각을 포함합니다. Chebotarev의 논문과 Liu의 프리프린트는 이 정리를 사용합니다. 여기서는
사용하지 않습니다. 대신 $\Psi \ge 0$을 인증하여(7절) 인용 정리 없이 Lean 동치가 명제
$\Lambda_4 = S_4$ 전체를 다루게 합니다.

## 5. 희소 가중치로의 환원

`exists_sparse`는 실선형 범함수 $\varphi : \mathbb C \to \mathbb R$를 고정합니다.
$b \in [0,1]^{12}$와 $\operatorname{lap} b$의 고윳값 $w$에 대해, 분수 가중치(0과 1 사이에
엄격히 놓인 가중치)가 네 개 이하이고 각 행에 두 개 이하인(`Sparse`) 상자 안의 $b'$과,
$\varphi(w) \le \varphi(w')$인 $\operatorname{lap} b'$의 고윳값 $w'$을 찾습니다. $b$에서 분수인
가중치만 바꿉니다. 증명은 분수 호의 개수에 대한 귀납법입니다. 각 단계에서 $b$를 분수 호에
지지된 방향 $\delta$를 따라 움직여 가중치 하나가 더 0이나 1에 닿게 합니다(`exists_move`).

- **왼쪽 이동** (`left_move`, 분수 가중치가 다섯 개 이상이고 $w \ne 0$일 때 사용). 왼쪽
  고유벡터 $y$를 잡습니다. $y \operatorname{lap} b = w y$이고 $\operatorname{lap} b$의 행 합이
  0이므로 $w \sum_i y_i = 0$, 따라서 $\sum_i y_i = 0$입니다. 실선형 사상
  $(\delta, \mu) \mapsto y \operatorname{lap}\delta - \mu y$를 처음 세 좌표로 제한한 것을
  생각합니다. 정의역의 차원은 $\#\text{분수} + 2 \ge 7$이고 공역의 차원은 6이므로, 0이 아닌
  핵 원소가 있습니다. $y \operatorname{lap}\delta$와 $\mu y$의 좌표 합이 모두 0이므로 네 번째
  좌표도 0입니다. 따라서 모든 $s$에 대해
  $y \operatorname{lap}(b + s\delta) = (w + s\mu) y$입니다. $(\delta, \mu)$의 부호는
  $\varphi(\mu) \ge 0$이 되도록 고릅니다.
- **오른쪽 이동** (`right_move`, 어떤 행에 분수 가중치가 세 개일 때 사용). 오른쪽 고유벡터
  $v$를 잡습니다. 복소 방정식 $\sum_j \delta_{ij}(v_i - v_j) = 0$은 행 $i$의 비대각 성분
  세 개에 대한 실방정식 두 개이므로, 행 $i$에 지지된 0이 아닌 해 $\delta$가 있고, $w$는
  $\operatorname{lap}(b + s\delta)$의 고윳값으로 남습니다.
- **$w = 0$.** 모든 분수 가중치를 0으로 둡니다. $0$은 모든 $\operatorname{lap} b$의
  고윳값입니다(`isEig_lap_zero`).

같은 종류의 다른 환원:
- Chebotarev의 명제 `p:sparse`(arXiv:2610.14100v2)는 고유벡터와 고윳값을 고정하고 각 행에서
  다면체의 꼭짓점을 잡습니다. 그러면 행마다 분수 성분이 두 개 이하가 되지만, 전체로는 여덟
  개까지 남습니다.
- Liu의 보조정리 16은 고정된 오른쪽 고유벡터 $v$에 대해 $L'v = \lambda' v$인 쌍
  $(b', \lambda')$의 다면체 위에서 $\operatorname{Im} \lambda'$을 최대화합니다. 여덟 개의 실
  방정식 때문에 분수 가중치가 여섯 개 이하, 행마다 두 개 이하로 남습니다.
- 왼쪽 고유벡터를 쓰면 $\sum_i y_i = 0$ 때문에 네 복소 방정식 중 하나가 중복됩니다. 그래서
  여기서는 여섯 개가 아니라 네 개의 분수 가중치가 남습니다.

## 6. 조립: 두 동치

- `im_le_one_of_faceBound`: $\varphi = \operatorname{Im}$으로 `exists_sparse`를 적용한 뒤,
  희소한 점에서 `phi_criterion`을 씁니다. $-\operatorname{Im}$은 켤레로 처리합니다.
- `sector_of_sectorFaceBound`: $\varphi = \operatorname{Im} - \operatorname{Re}$로
  `exists_sparse`를 적용한 뒤 `sector_criterion`을 씁니다.
- `sector_four_of_sectorFaceBound`: 보수 변환으로 이를
  $|\operatorname{Im} w| \le 4 - \operatorname{Re} w$로 바꿉니다.
- `z4_statement_of_faceBound`와 `statement_of_faceBounds`는 4로 척도를 바꾸고 `cycle_eig`와
  `S4_subset_Λ4`를 사용합니다.
- 역(`phi_nonneg_of_im_le`, `psi_nonneg_of_sector`)이 반대 방향을 줍니다:

```lean
theorem z4_statement_iff_faceBound : z4_statement ↔ FaceBound
theorem statement_iff_faceBounds : statement ↔ FaceBound ∧ SectorFaceBound
```

여기서 `FaceBound`는 $\Phi(b) \ge 0$, `SectorFaceBound`는 $\Psi(b) \ge 0$이라는 명제이며, 둘
다 분수 가중치가 네 개 이하이고 행마다 두 개 이하인 상자 안의 모든 $b$에 대한 것입니다.

## 7. 정확한 인증서

[`face_certificate.py`](face_certificate.py)는 Python 정수와 `fractions.Fraction`만으로
(부동소수점 없이, 외부 패키지 없이) `FaceBound`와 `SectorFaceBound`를 검증합니다.

1. **면.** 모든 희소 $b$는 *극대 패턴*의 면 위에 있습니다. 극대 패턴은 행마다 두 개 이하인
   자유 호 네 개가 호의 순서대로 $t_0, \dots, t_3 \in [0,1]$을 갖고, 나머지 여덟 호가 0이나
   1로 고정된 것입니다. $b$의 분수 호는 언제나 이런 호 네 개로 보충할 수 있고, 분수가 아닌
   가중치는 0이나 1입니다. 자유 호의 선택이 $459$가지, 채우기가 $2^8$가지이므로 패턴은
   $117504$개입니다.
2. **대칭.** 꼭짓점 재명명은 치환 닮음이므로 $\sigma_1, \sigma_2, \sigma_3$을 보존합니다.
   스크립트는 $S_4$의 생성원 $(0\,1)$과 $(0\,1\,2\,3)$에 대해 이를 열두 가중치의 다항식
   항등식으로 확인합니다. 또 보수 변환 공식 $\sigma_1' = 12 - \sigma_1$,
   $\sigma_2' = 48 - 8\sigma_1 + \sigma_2$,
   $\sigma_3' = 64 - 16\sigma_1 + 4\sigma_2 - \sigma_3$과, 이 사상에서 $\Phi$가 불변임을
   확인합니다. 대칭은 자유 변수를 치환하고 일부 $t_k$를 $1 - t_k$로 바꾸므로, $[0,1]^4$에서의
   음이 아님은 한 궤도의 모든 면에서 같습니다. $\Phi$는
   $S_4 \times \{\mathrm{id}, \text{보수 변환}\}$의 궤도마다 면 하나(2533개 궤도), $\Psi$는
   $S_4$의 궤도마다 면 하나(5021개 궤도; $\Psi$는 보수 변환에 대해 불변이 아님)가 필요합니다.
3. **상자 인증서.** 면 다항식 $P(t)$를 $[0,1]^4$의 텐서 Bernstein 기저로 씁니다. $t_k$에
   대한 차수 $d_k$는 $t_k$의 최대 지수입니다. 스크립트는 각 축을 따라
   $\sum_{j \le k} a_j \binom{d-j}{k-j}$를 계산합니다. 이것은 Bernstein 계수에 양의 이항계수를
   곱한 것입니다. 모두 $\ge 0$이면 상자에서 $P \ge 0$입니다.
4. **단체 인증서.** 그렇지 않으면 상자를 한 꼭짓점 $c$를 지나는 Kuhn 단체 24개로 자릅니다.
   $P$가 0이 되는 꼭짓점을 먼저 시도합니다. 꼭짓점이 $V_0, \dots, V_4$인 단체에서 스크립트는
   $\theta$에 대한 $d = \deg P$차 형식
   $P\bigl(\sum_j \theta_j V_j\bigr)\bigl(\sum_j \theta_j\bigr)^{d - \deg}$를 전개합니다. 그
   계수가 모두 $\ge 0$이면 단체에서 $P \ge 0$입니다. 실패한 단체는 한 모서리 위의 점 $M$에서
   그것을 덮는 두 단체로 나눕니다. Kuhn 단체 하나 아래에서 분할은 최대 6번까지 허용합니다.
   점 $M$은 다음과 같이 고릅니다.
   - 어떤 꼭짓점 $W$에서 $P(W) = 0$이고, $W$에서 나가는 두 모서리 방향 $d_k, d_l$에서 $P$의
     미분이 0이며, 헤세 형식 $q$가 $q_{kk}, q_{ll} > 0 > q_{kl}$을 만족한다고 합시다. 그러면
     그 두 이웃 꼭짓점 사이의 모서리를 비율 $q_{kk}/(q_{kk} - q_{kl})$에서 나눕니다. 그곳에서
     $q$의 계수(rank)가 1이면 이 점은 이차 형식의 영점 집합 위에 있습니다.
   - 그렇지 않으면 가장 긴 모서리를 이등분합니다.

   이 규칙은 탐색의 방향만 정합니다. 모든 분할은 단체를 그것을 덮는 두 단체로 바꿉니다.
5. **Lean 공식과의 교차 확인.** 각 대표에 대해 전개한 면 다항식을 두 무작위 유리점에서
   `Basic.lean`의 공식(`σ₁`, `c2`, `c3`, `det3`, `phiPoly`, `sectorPoly`)을 직접 계산한 값과
   비교합니다. 탐색은 결정적입니다. 궤도별 표(방법과 단체 개수)를 커밋된
   [`face_orbits.tsv`](face_orbits.tsv)와 비교합니다.

**통계** ([`face_orbits.tsv`](face_orbits.tsv)를 읽는 [`orbit_table.py`](orbit_table.py)의
출력):

| | 궤도 | 상자 | 단체가 필요한 궤도 | 단체 |
|---|---|---|---|---|
| $\Phi$ | 2533 | 2457 | 76 | 1889 |
| $\Psi$ | 5021 | 4956 | 65 | 1560 |

Apple M5 Max에서 기본값인 작업 프로세스 4개로 실행하면 약 17초 걸립니다. CPU 시간은 $\Phi$
궤도에 36.5초, $\Psi$ 궤도에 27.6초이고, 가장 느린 궤도($\Phi$의 `00110FFF00F1`)는
1.8초입니다. 모든 궤도가 인증됩니다. 단체로 닫은 궤도에 대해서는 Kuhn 단체의 꼭짓점과 최종
단체 개수를 표에 기록합니다.

패턴은 호의 순서 $01, 02, 03, 10, 12, 13, 20, 21, 23, 30, 31, 32$로 쓴 열두 글자입니다
(`F` = 자유).

**단체가 필요한 이유.** $P \ge 0$이 열린 상자 안에 영점을 가지면, 모든 기저 다항식이 그곳에서
양수이므로 $P \equiv 0$이 아닌 한 상자 Bernstein 계수가 모두 $\ge 0$일 수는 없습니다.
$\Phi$에는 이런 영점이 있습니다. 예를 들어 `01F1F00F1F10`의 궤도는 Liu의 족의 면입니다. 유향
4-사이클(여기서는 $0 \to 2 \to 3 \to 1 \to 0$)의 호 $i \to i+1$에 가중치 1, 현 $i \to i+2$는
자유, $i \to i+3$에 가중치 0입니다. 대표의 호 순서로 쓰면 이 면에서 $\Phi$는
$(t_0 - t_1 - t_2 + t_3)^2$과 다른 인수의 곱이므로, 초평면 $t_0 + t_3 = t_1 + t_2$에서
0이 됩니다. 이 초평면이 $|\operatorname{Im} w| = 1$이 달성되는 Liu의 3-매개변수 족입니다
(Liu의 첨자, 즉 $t_i$를 사이클의 $i$번째 꼭짓점에서 나가는 현에 두는 방식으로는
$t_0 + t_2 = t_1 + t_3$). 인증서는 이 궤도를 꼭짓점 0000에서 단체 32개로 닫습니다.

**8차원 면.** 행마다 고정된 호가 하나, 자유 호가 둘인 면은 $6^4 = 1296$개이고, 재명명과 보수
변환에 대해 36개 궤도를 이룹니다. 이는 사전 탐색 실행의 개수를 여기서 다시 계산한 것입니다.
모든 극대 패턴은 이런 면 위에 있습니다. 각 궤도의 대표 하나에 대해 `orbit_table.py`는 그 위에
놓인 극대 패턴의 $\Phi$-궤도 수와, 그중 단체가 필요한 궤도 수를 나열합니다:

| 대표 | 면 | 위에 놓인 $\Phi$-궤도 | 단체가 필요한 궤도 | 단체 |
|---|---|---|---|---|
| `0FF 0FF 0FF 0FF` | 24 | 432 | 0 | 0 |
| `0FF 0FF 0FF 1FF` | 48 | 912 | 0 | 0 |
| `0FF 0FF 0FF F0F` | 24 | 521 | 0 | 0 |
| `0FF 0FF 0FF F1F` | 48 | 962 | 0 | 0 |
| `0FF 0FF 0FF FF0` | 48 | 804 | 0 | 0 |
| `0FF 0FF 0FF FF1` | 48 | 830 | 0 | 0 |
| `0FF 0FF 1FF 1FF` | 24 | 549 | 0 | 0 |
| `0FF 0FF 1FF F1F` | 24 | 519 | 0 | 0 |
| `0FF 0FF 1FF FF0` | 48 | 802 | 0 | 0 |
| `0FF 0FF 1FF FF1` | 48 | 827 | 0 | 0 |
| `0FF 0FF FF0 FF0` | 6 | 156 | 0 | 0 |
| `0FF 0FF FF0 FF1` | 24 | 570 | 0 | 0 |
| `0FF 0FF FF1 FF1` | 6 | 156 | 0 | 0 |
| `0FF 1FF 0FF 0FF` | 24 | 548 | 48 | 1198 |
| `0FF 1FF 0FF 1FF` | 48 | 910 | 56 | 1380 |
| `0FF 1FF 0FF F0F` | 48 | 959 | 45 | 1099 |
| `0FF 1FF 0FF F1F` | 24 | 516 | 51 | 1284 |
| `0FF 1FF 0FF FF0` | 48 | 918 | 64 | 1599 |
| `0FF 1FF 0FF FF1` | 48 | 957 | 50 | 1246 |
| `0FF 1FF 1FF 1FF` | 24 | 431 | 0 | 0 |
| `0FF 1FF 1FF F0F` | 24 | 519 | 15 | 360 |
| `0FF 1FF 1FF FF0` | 48 | 921 | 15 | 360 |
| `0FF 1FF 1FF FF1` | 48 | 960 | 58 | 1425 |
| `0FF 1FF FF0 FF1` | 12 | 297 | 33 | 842 |
| `0FF F0F 0FF 0FF` | 48 | 706 | 52 | 1296 |
| `0FF F0F 0FF 1FF` | 48 | 813 | 51 | 1273 |
| `0FF F0F 1FF 0FF` | 48 | 1000 | 39 | 961 |
| `0FF F0F 1FF 1FF` | 48 | 881 | 0 | 0 |
| `0FF F0F 1FF F0F` | 48 | 928 | 24 | 576 |
| `0FF F0F 1FF F1F` | 48 | 947 | 15 | 360 |
| `0FF F0F 1FF FF0` | 48 | 888 | 0 | 0 |
| `0FF F0F 1FF FF1` | 48 | 992 | 51 | 1256 |
| `0FF F0F FF0 0FF` | 12 | 284 | 33 | 839 |
| `0FF F0F FF0 1FF` | 48 | 1044 | 25 | 607 |
| `0FF F0F FF1 1FF` | 24 | 554 | 15 | 360 |
| `0FF F1F FF0 1FF` | 12 | 284 | 0 | 0 |

세 글자씩 묶은 것이 행 $0, 1, 2, 3$입니다. 극대 패턴 하나가 여러 8차원 면 위에 놓이므로
세 번째 열의 개수는 행 사이에 겹칩니다. 사전 탐색 실행에서 z3(NLSAT)는 자유 가중치가 네 개
이하인 작은 부분면만 닫았고, 시도한 더 큰 면에서는 `unknown`을 반환했습니다. 여기서는 모든
면을 4차원 부분면으로 줄이며, 각 부분면은 2초 안에 닫힙니다.

## 8. 독립적인 수치 확인

[`numerical_check.py`](numerical_check.py)는 인증서와 코드를 공유하지 않습니다. 특성다항식은
Faddeev–LeVerrier 점화식으로, 고윳값은 Durand–Kerner 반복으로 배정밀도에서 계산합니다. 기본값
(시드 2026)으로 실행하면 다음을 보고합니다.

- 무작위 가중치 벡터 2000개(일부는 분수, 일부는 0/1)에서 항등식
  $\Phi = \prod_{a<b}((r_a - r_b)^2 + 4)$가 상대 오차 약 $5 \cdot 10^{-13}$ 이내로,
  $\Psi = e_1 e_2 - e_3$가 약 $4 \cdot 10^{-13}$ 이내로 성립합니다(출력되는 자릿수는 Python
  버전에 따라 다릅니다).
- 무작위 점, 무작위 0/1 점, 재명명한 4-사이클 근처에서 시작하는 목적함수당 30번의 다중 시작
  국소 상승 탐색 결과:
  - $\max \operatorname{Im} w = 1.000000000$ (한계는 1이고 4-사이클에서 달성됩니다);
  - $\max(|\operatorname{Im} w| - \operatorname{Re} w) = 0.000000000$;
  - $\max(|\operatorname{Im} w| - (4 - \operatorname{Re} w)) = 0.000000000$.

이것은 증거일 뿐이며, 증명은 3–7절입니다. 실행에는 약 2초 걸립니다.

## 9. 기계 검증된 부분

| 단계 | 확인 수단 |
|---|---|
| 정의, 육각형으로서의 $S_4$, $S_4 \subseteq \Lambda_4$, 두 예 | Lean |
| 특성다항식, Bendixson, Gershgorin, 보수 변환 | Lean |
| $\Phi$와 $\Psi$ 판정법과 그 역 | Lean |
| 희소 가중치로의 환원(`exists_sparse`) | Lean |
| `statement ↔ FaceBound ∧ SectorFaceBound`, `z4_statement ↔ FaceBound` | Lean |
| `FaceBound`, `SectorFaceBound` | `face_certificate.py`, Lean 밖의 정확한 연산 |
| 수치적 일치 | `numerical_check.py`, 부동소수점 |

Lean은 `propext`, `Classical.choice`, `Quot.sound`만 사용합니다. 마지막 단계의 신뢰 기반은
Python 인터프리터와 인증서 스크립트(약 500줄)입니다. 이 스크립트와 Lean 정의의 연결은 다음과
같습니다.
- 같은 공식;
- `Basic.lean`의 공식에 대한 무작위 유리점 교차 확인;
- 다항식 항등식으로 확인한 대칭 항등식.

**인증서를 Lean에 넣지 않은 이유.** 이 저장소에서는 `native_decide`와 `ofReduceBool`이
금지되어 있으므로, Lean 안의 확인은 커널(`decide +kernel`)에서 실행되어야 합니다. 로컬 시험에서
200,000단계의 정수 반복과 200,000항 리스트 내적이 약 2분 걸렸습니다. 인증서는 계수가 최대
$5^4 = 625$개인 다항식(각 면 다항식은 변수마다 차수 4 이하)을 궤도 대표 7554개와 최종 단체
3449개에서 전개합니다. 이를 커널에서 다시 실행하는 것은 CI 예산을 크게 넘으며, 궤도마다
`ring`/`nlinarith` 증명을 쓰는 것도 마찬가지입니다. 그래서 상태는 `partial`입니다.

## 10. 선행 연구, 중복, 출처

- **Agaev와 Chebotarev** (Linear Algebra Appl. 399 (2005) 157–168,
  [arXiv:math/0508176](https://arxiv.org/abs/math/0508176))는 다각형 추측을 제기하고,
  $S_n \subseteq \Lambda_n$(정리 6)과 $n \le 3$에서 $\Lambda_n = S_n$을 증명했으며, 정리 5의
  영역(원판, 각, Pick 띠)을 제시했습니다.
- **Chebotarev** ([arXiv:2610.14100v2](https://arxiv.org/abs/2610.14100v2), 2026-10-20)는
  모든 $n \ge 5$에서 추측을 반증하고, 환원 `p:sparse` 및 $z(4) = 1/4$와의 동치와 함께
  $n = 4$에 대해 질문 1을 던졌습니다. $n = 4$에 대한 증거는 가중치 없는 유향 그래프
  $2^{12}$개 전부와, 여러 구조적 행렬 근처 및 무작위 점에서 시작한 국소 최대화입니다. 질문
  `q:top`은 짝수 $n$에서 $\max \operatorname{Im} \Lambda_n = \frac1n \cot\frac\pi n$인지
  묻습니다. 여기서는 다루지 않습니다.

### Liu의 프리프린트와의 관계

Dylan Z. Liu, "The Agaev–Chebotarev Polygon Conjecture Holds Exactly for n ≤ 4"
([Zenodo 레코드 23630989](https://zenodo.org/records/23630989),
[doi:10.5281/zenodo.23630989](https://doi.org/10.5281/zenodo.23630989), 2026-10-25 생성,
CC BY 4.0)는 $\Lambda_4 = S_4$의 컴퓨터 보조 증명(정리 6)과 모든 $n \ge 5$에서
$\Lambda_n \ne S_n$임을 보고합니다. 심사되지 않았고 형식화되지 않았습니다. 이 작업을 시작할 때의
문헌 확인에서 찾았습니다. 비교:

| | Liu의 프리프린트 | 이 항목 |
|---|---|---|
| 부등식 | 같은 $\Phi$ (보조정리 15, 축약 삼차식 형태) | $\Phi$ |
| 퇴화 영점 | $\sqrt{3/2}$를 쓰는 Bendixson | $3/2$를 쓰는 Bendixson |
| 환원 | 오른쪽 고유벡터, 분수 6개 이하, 행마다 2개 이하 (보조정리 16) | 왼쪽 고유벡터, 분수 4개 이하, 행마다 2개 이하 |
| 면 | 패턴 445312개, 궤도 9583개 | 극대 패턴 117504개, 궤도 2533개 |
| 섹터 절반 | Agaev–Chebotarev 정리 5 인용 | 궤도 5021개에서 $\Psi \ge 0$ 인증 |
| 인증서 | 상자와 초평면 절단을 더한 Kuhn 단체에서의 Bernstein, python-flint, 약 1시간 | 상자와 모서리 분할을 더한 Kuhn 단체에서의 Bernstein, 표준 라이브러리, CPU 약 1분 |
| 형식화 | 없음 | 질문 1과 두 면 한계의 동치를 Lean으로 증명 |

Liu의 프리프린트는 검증 스크립트와 데이터 파일이 부속 파일이라고 말합니다. PDF만 있는 Zenodo
레코드에서는 이를 찾지 못했고, 실행하지 않았습니다. 두 인증서는 같은 종류의 방법(상자와 Kuhn
단체에서의 Bernstein 전개)을 씁니다. 프리프린트에서 코드를 가져오지 않았습니다.

### 그 밖의 관련 연구

- **AFTD.** 자동화 플랫폼 "Auto-Formalizing Theoretical Domains"
  ([github.com/rainwangphy/aftd-platform](https://github.com/rainwangphy/aftd-platform))는 이
  질문을 OP-465로 올려 두고 Lean에서
  `op_465_standardized_laplacian_order_four_polygon_conjecture`로 명제화합니다. 열린 stub는
  `standardized_laplacian_order_four_im_le`,
  `standardized_laplacian_order_four_two_fractional_im_le`,
  `standardized_laplacian_order_four_two_fractional_sector`입니다. 증명된 것으로는 다음 등이
  있습니다.
  - $S_n \subseteq \Lambda_n$;
  - 판별식 판정법(`real_cubic_im_le_of_discriminant_bound`);
  - 2-매개변수 족 하나(`two_adjacent_chord_cubic_im_le`);
  - Gershgorin, $\operatorname{Re} \ge 0$, $|\operatorname{Im}| \le 3/4$;
  - 섹터 한계와 Im 한계로부터의 다각형 소속;
  - 행마다 분수 성분이 두 개 이하인 영이 아닌 예
    (`exists_nonzero_two_fractional_standardized_laplacian_four`). 환원 `p:sparse` 자체는
    그곳에서 증명되어 있지 않습니다.

  2026-10-25 23:37 UTC에 지식 베이스 `web/data/kb.json`을 다시 내려받았습니다. 17:13 UTC에
  생성된 뒤 바뀌지 않았고, OP-465와 세 stub는 여전히 `stated`였습니다. AFTD는 무엇을
  명제화하고 증명하는지 알기 위해서만 읽었습니다. 코드는 가져오지 않았으며, 그 저장소에는
  라이선스 파일이 없습니다.
- **사전 탐색.** 이 프로젝트의 이전 탐색(scouting) 실행이 1296개의 8차원 면과 그 36개 궤도로의
  환원, 퇴화 경우를 포함한 $\Phi$의 이동 판별식 항등식, z3 확인, 막다른 경로(꼭짓점 환원,
  $\sigma$-공간의 볼록 껍질)를 찾았습니다.
- **문헌 확인** (2026-10-25): arXiv에서 2610.14100의 최신 버전은 v2입니다. OpenAlex에는 인용
  문헌이 없습니다. MathDB 게시물 #379199와 #318272(일반 추측)는 열려 있습니다. Formal
  Conjectures와 GitHub 검색에서는 질문 1에 관한 다른 것을 찾지 못했습니다.

새로움은 주장하지 않습니다. 이 작업은 사람이 검토하지 않았습니다. 저자에게 보고하거나 어디에도
제출하지 않았습니다.
