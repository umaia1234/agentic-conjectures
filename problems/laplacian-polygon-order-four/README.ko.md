[English](README.md) | **한국어**

# 표준화 라플라시안의 4차 다각형 질문

다각형 추측 $\Lambda_n = S_n$은 R. Agaev와 P. Chebotarev의 것입니다
(*Linear Algebra Appl.* 399 (2005) 157–168,
[arXiv:math/0508176](https://arxiv.org/abs/math/0508176)). $\Lambda_4 = S_4$인지 묻는
질문 1과, 모든 $n \ge 5$에서 추측을 반증하여 4차만 열어 둔 결과는 P. Chebotarev의
[arXiv:2610.14100v2](https://arxiv.org/abs/2610.14100v2)에 있습니다. Dylan Z. Liu의
프리프린트([Zenodo, doi:10.5281/zenodo.23630989](https://doi.org/10.5281/zenodo.23630989))는
$\Lambda_4 = S_4$의 컴퓨터 보조 증명을 보고합니다. [선행 연구와 출처](#선행-연구와-출처)를
보십시오.

## 질문

$n$차 *표준화 라플라시안*은 행 합이 0이고 비대각 성분이 $[-1/n, 0]$에 놓인 $n \times n$
실행렬입니다. $\Lambda_n \subset \mathbb C$는 이런 행렬 전체의 고윳값 전체의 집합입니다.
Agaev와 Chebotarev는 다각형 $S_n \subseteq \Lambda_n$을 정의하고 $\Lambda_n = S_n$을
추측했으며, $n \le 3$에서 이를 증명했습니다. Chebotarev의 arXiv 논문은 모든 $n \ge 5$에서
추측을 반증하고 $n = 4$를 질문 1로 남겨 둡니다. $n = 4$에서는

$$
S_4 = \operatorname{conv}\Bigl\{0,\ \tfrac{1 \pm i}{4},\ \tfrac{3 \pm i}{4},\ 1\Bigr\}
    = \bigl\{z : |\operatorname{Im} z| \le \operatorname{Re} z,\ |\operatorname{Im} z| \le 1 - \operatorname{Re} z,\ |\operatorname{Im} z| \le \tfrac14\bigr\}
$$

입니다.

**질문 1.** $\Lambda_4 = S_4$인가? 논문은 이것이 $z(4) = 1/4$와 동치라고 지적합니다. 여기서
$z(n) = \sup\{|\operatorname{Im}\lambda| : \lambda \in \Lambda_n\}$입니다.

## 결과

상태: **partial**. 마지막 부등식들은 Lean이 아니라 컴퓨터가 인증합니다.

1. **Lean** (`sorry` 없음, 표준 공리만 사용): 질문 1은 가중치 큐브의 유한 개 면, 각각 차원이
   4 이하인 면 위의 두 다항식 부등식과 *동치*입니다. $z(4) = 1/4$ 형태는 첫 번째 부등식 하나와 동치입니다.
   - `statement_iff_faceBounds : statement ↔ FaceBound ∧ SectorFaceBound`
   - `z4_statement_iff_faceBound : z4_statement ↔ FaceBound`

   여기서 호의 가중치 $b_{ij} \in [0,1]$로 $L = D - B$라 두면 $L/4$가 표준화 라플라시안이고,
   $\det(x - L) = x(x^3 - \sigma_1 x^2 + \sigma_2 x - \sigma_3)$입니다. 그리고
   - `FaceBound`는 $\Phi \ge 0$이라는 명제입니다. 여기서
     $\Phi = \operatorname{Disc} + 4(\sigma_1^2 - 3\sigma_2 + 4)^2 = \prod_{a<b}\bigl((r_a - r_b)^2 + 4\bigr)$
     이고, 곱은 삼차식의 세 근에 대한 것입니다.
   - `SectorFaceBound`는 $\Psi \ge 0$이라는 명제입니다. 여기서
     $\Psi = (\sigma_1^2 - 2\sigma_2)(\sigma_2^2 - 2\sigma_1\sigma_3) - \sigma_3^2$입니다.
   - 두 부등식 모두, 0과 1 사이에 엄격히 놓인 성분(분수 가중치)이 네 개 이하이고 각 행에
     두 개 이하인 가중치에 대해서만 요구됩니다.
2. **컴퓨터 보조** (Lean 밖에서 정확한 정수·유리수 연산):
   [`face_certificate.py`](face_certificate.py)가 `FaceBound`와 `SectorFaceBound`를
   검증합니다.
   - 117504개의 극대 희소 패턴을 열거하고 대칭 항등식을 확인합니다.
   - 대칭 궤도마다 면 하나를 확인합니다. $\Phi$는 2533개 궤도, $\Psi$는 5021개 궤도입니다.
   - 각 확인은 계수가 모두 음이 아닌 Bernstein 전개이며, 상자 전체에서 하거나 모서리 분할을
     더한 Kuhn 단체들에서 합니다.

(1)과 (2)를 합치면 $\Lambda_4 = S_4$와 $z(4) = 1/4$가 컴퓨터 보조 결과로 얻어집니다. Liu의
프리프린트도 관련된 방법으로 같은 결론을 보고합니다. Lean에서 `FaceBound`와
`SectorFaceBound`는 가정이나 동치의 한쪽으로만 나타나며, Lean은 인증서를 확인하지 않습니다.

[DETAILS.ko.md](DETAILS.ko.md)에 전체 논증이 있습니다. 환원, 두 판정법, 대칭 단계, 인증서,
면 궤도 통계, 수치 확인을 다룹니다.

## Lean 선언

모듈 [`AgenticConjectures/LaplacianPolygonOrderFour.lean`](../../AgenticConjectures/LaplacianPolygonOrderFour.lean)과
그 폴더, 이름공간 `AgenticConjectures.LaplacianPolygonOrderFour`.

| 선언 | 내용 |
|---|---|
| `statement` | 질문 1: `Λ₄ = S₄` |
| `z4_statement` | `IsGreatest {x \| ∃ z ∈ Λ₄, x = \|z.im\|} (1/4)`, 논문의 형태 $z(4) = 1/4$ |
| `statement_iff_faceBounds` | `statement ↔ FaceBound ∧ SectorFaceBound` |
| `z4_statement_iff_faceBound` | `z4_statement ↔ FaceBound` |
| `statement_of_faceBounds`, `z4_statement_of_faceBound` | 결과에 쓰이는 두 방향 |
| `S4_eq` | 볼록 껍질이 반평면 표현과 같음 |
| `S4_subset_Λ4` | 순환 행렬로 보인 $S_4 \subseteq \Lambda_4$ |
| `cycle_eig`, `h4_eig` | $(1+i)/4 \in \Lambda_4$ (유향 4-사이클)와 $(3+2i)/8 \in \Lambda_4$ (현 두 개를 더한 4-사이클, 윗변 위의 점) |
| `mem_Λ₄_iff` | $z \in \Lambda_4$ ⟺ 가중치가 $[0,1]$인 어떤 $L = D - B$의 고윳값이 $4z$ |
| `exists_sparse` | 분수 가중치를 네 개 이하, 행마다 두 개 이하로 줄이는 환원 |
| `phi_criterion`, `phi_nonneg_of_im_le` | 모든 고윳값이 $\lvert\operatorname{Im}\rvert \le 1$ ⟺ $\Phi \ge 0$ |
| `sector_criterion`, `psi_nonneg_of_sector` | 모든 고윳값이 $\lvert\operatorname{Im}\rvert \le \operatorname{Re}$ ⟺ $\Psi \ge 0$ |
| `im_le_three_halves` | Bendixson 한계 $\lvert\operatorname{Im}\rvert \le 3/2$ |

## 명제의 충실성

상류(upstream) 형식 명제가 없으므로 정의는 이 저장소의 것입니다.
- **행렬.** 4차 표준화 라플라시안(`IsStdLaplacian`)은 행 합이 0이고 $i \ne j$에서
  $-1/4 \le \ell_{ij} \le 0$인 `Matrix (Fin 4) (Fin 4) ℝ`입니다.
- **고윳값.** 고윳값(`IsEig`)은 복소화한 행렬의 고윳값,
  `Module.End.HasEigenvalue (Matrix.toLin' (L.map (↑))) z`입니다. `isEig_iff_det`는 이것이
  $\det(z - L) = 0$과 같음을 보입니다.
- **다각형.** `S₄`는 여섯 꼭짓점의 볼록 껍질이며, $n = 4$에서 논문의 정의와 같습니다.
  `S4_eq`가 반평면 표현을 증명합니다.
- **논문의 동치 형태.** `z4_statement`는 $\Lambda_4$ 위에서 $|\operatorname{Im} z|$의 최댓값이
  존재하고 $1/4$와 같기를 요구합니다. $(1+i)/4 \in \Lambda_4$(`cycle_eig`)이므로 이는 상한
  $z(4)$에 대한 $z(4) = 1/4$와 같습니다.

## 재현

저장소 루트에서:

```bash
lake build AgenticConjectures.LaplacianPolygonOrderFour
```

Mathlib을 빌드한 뒤 아홉 모듈의 컴파일은 벽시계 시간으로 약 28초 걸립니다(Apple M5 Max,
모듈별 빌드 시간의 합은 약 38초).

```bash
cd problems/laplacian-polygon-order-four && python3 face_certificate.py
```

정확한 인증서입니다. 기본값인 작업 프로세스 4개로 약 17초(CPU 시간 약 64초) 걸립니다.
궤도별 표를 [`face_orbits.tsv`](face_orbits.tsv)와 비교합니다.

```bash
cd problems/laplacian-polygon-order-four && python3 numerical_check.py
```

인증서와 코드를 공유하지 않는 독립적인 부동소수점 확인이며 약 2초 걸립니다. 무작위 가중치에서
$\Phi$와 $\Psi$의 항등식을 확인하고, $\max \operatorname{Im}$과 두 섹터 위반량에 대해 국소 상승
탐색을 실행합니다.

두 스크립트 모두 Python 표준 라이브러리만 사용합니다.

## 선행 연구와 출처

- **추측.** Agaev와 Chebotarev(2005)는 $S_n \subseteq \Lambda_n$을 증명하고, $n \le 3$에서
  $\Lambda_n = S_n$을 증명했으며, 추측을 제기했습니다.
- **질문 1.** Chebotarev([arXiv:2610.14100v2](https://arxiv.org/abs/2610.14100v2),
  2026-10-20)는 모든 $n \ge 5$에서 추측을 반증하고 $n = 4$에 대해 질문 1을 던졌습니다. 이
  논문은 행마다 분수 성분을 두 개 이하로 줄이는 환원과 수치적 증거도 제시합니다.
- **Liu의 프리프린트.** Dylan Z. Liu, "The Agaev–Chebotarev Polygon Conjecture Holds Exactly
  for n ≤ 4" ([Zenodo 레코드](https://zenodo.org/records/23630989), 2026-10-25 생성,
  CC BY 4.0, 심사·형식화되지 않음). $\Lambda_4 = S_4$의 컴퓨터 보조 증명을 보고합니다.
  - 분수 가중치를 여섯 개 이하로 줄이는 LP 환원;
  - 같은 다항식 $\Phi$;
  - 면의 9583개 클래스에서의 정확한 Bernstein 전개.

  모든 $n \ge 5$에서 $\Lambda_n \ne S_n$임도 증명합니다. 검증 스크립트는 부속 파일이라고
  되어 있지만 Zenodo 레코드에서 찾지 못했고 실행하지 않았습니다.
  [DETAILS.ko.md](DETAILS.ko.md#liu의-프리프린트와의-관계)에서 두 접근을 비교합니다.
- **AFTD (관련 연구).** 자동화 플랫폼 AFTD
  ([github.com/rainwangphy/aftd-platform](https://github.com/rainwangphy/aftd-platform))는
  이 질문을 OP-465로 Lean에 명제화하고 부분 보조정리들을 증명합니다(DETAILS에 나열).
  AFTD의 코드는 가져오지 않았습니다.
- **사전 탐색.** 이 프로젝트의 이전 탐색(scouting) 실행이 이 작업의 출발점인 면 환원, z3
  확인, 막다른 경로들을 찾았습니다.

새로움은 주장하지 않습니다. 이 작업은 사람이 검토하지 않았습니다. 저자에게 보고하거나 어디에도
제출하지 않았습니다.
