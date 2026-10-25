[English](README.md) | **한국어**

# Finite projective plane of order 12

확인 기준일: 2026-08-11 (조사), 2026-10-24 (아래의 인증된 재현).

## 문제

order 12인 유한 projective plane이 존재하는지를 묻는다. 이는 대칭
`2-(157,13,1)` design의 존재와 동치이다. 행과 열의 합이 13인
`157 x 157` 영일 incidence matrix `A`를 사용하면 조건을

```text
A A^T = 12 I + J
```

로 쓸 수 있다.

## 현재 상태와 알려진 부분결과

2026년 1차 자료는 12를 존재 여부가 알려지지 않은 가장 작은 order로
기록한다. 2023년 논문은 order 4인 collineation group을 배제했고, 기존
결과와 합치면 가능한 전체 collineation group의 order는 1, 2, 3뿐이다.

이 디렉터리는 새로운 존재·비존재 결과를 주장하지 않는다. 상태
`partial`은 아래에 설명한, 대칭성이 큰 order 12 plane에 대한 고전적
배제 결과의 인증된 재현만을 가리킨다.

## 계산 관점

Incidence 조건은 exact cover나 SAT로 표현하기 좋지만 변수 수가 크다.
알려진 대칭 배제 결과 때문에 큰 순환대칭을 가정하는 비교적 쉬운 탐색은
이미 막혀 있다. 따라서 trivial 또는 매우 작은 자기동형군을 다루는
canonical search가 핵심 병목이다.

## 고전적 배제 결과의 인증된 재현 (2026-10-24)

이 절의 내용은 모두 알려진 결과(Singer, Hall, Evans--Mann, Bose,
Hoffman, Gordon; 근거 참조)를 재현한 것이다. 새로운 것은 없으며, order
12인 plane의 존재 여부도 결정하지 않는다. multiplier theorem은 어디에서도
사용하지 않는다.

### 1. 순환 plane 없음: `Z_157`에는 `(157,13,1)` difference set이 없다

**주장.** `Z_157`의 13원소 부분집합 `D` 가운데, 0이 아닌 모든 잉여가 차
`d - d'` (`d, d'`는 `D`의 원소)로 정확히 한 번씩 나타나는 것은 없다.
Singer 대응으로 말하면, 157개 점 위에 정칙(regular)으로 작용하는 순환
collineation group을 갖는 order 12 projective plane은 없다.

*정규화.* difference set의 평행이동 `D + c`와 단원 `u`에 의한 확대 `uD`도
difference set이다. 차 1은 정확히 한 번 나타나므로 어떤 평행이동은 0과
1을 포함한다 (방법 A). 방법 B는 아핀 정규형을 쓴다. 곧 `0, 1`이 `D`에
있고, `D`에서 세 번째로 작은 원소 `t`가 `b - a`가 단원인 서로 다른
`a, b, c`에 대한 비 `(c - a)/(b - a)` (`[0, v)`의 정수로 본 값)의
최솟값과 같다. 최솟값을 주는 세 원소를 `0, 1, t`로 보내면 어떤
difference set이든 이 꼴이 되며, 비가 2이면 차가 반복되므로 `t >= 3`이다.

서로 독립인 세 가지 방법:

- **A** (`ds_enumerate.cpp`): `{0, 1}`을 포함하고 차가 모두 다른 집합
  전체를 추가 가지치기 없이 단순 backtracking으로 훑으며 크기별로 센다.
  이런 집합은 최대 11원소이고 (2,052,820개), 12원소나 13원소인 것은 없다.
- **B** (`ds_search_normalized.cpp`): 정규형만 탐색하는 별도 구현으로,
  bitset 관리와 Golomb형 gap bound를 쓴다. 해가 없고 (21,979,581 nodes),
  12원소인 것도 없다. 해가 존재하는 크기에서는 두 방법이 정확히 일치한다.
  방법 A의 11원소 집합 2,052,820개를 정규형으로 거르면 방법 B의 133,091개와
  정확히 같다 (`crosscheck_ab.py`).
- **C** (SAT): `ds_cnf.py`는 정규형 difference set을 부호화한다 (변수
  `x_i`, 원소와 차 class마다 pair 변수, class마다 exactly-one 제약, 단위 절
  `x_0, x_1`, 5까지의 ratio 절). 독립적인 감사 스크립트 `audit_ds_cnf.py`가
  1,062,698개 절을 하나하나 다시 정당화한다. CaDiCaL 3.0.1은 UNSAT를,
  drat-trim (commit `2e3b2dc`)은 `s VERIFIED`를 보고한다. 15.5 MB 공식과
  320 MB 증명은 커밋하지 않았다. 공식은 결정적으로 재생성된다 (SHA-256
  `731268546c33d2f0f5bc86ec84559adefc9c943a37d880f787633a34c92d8999`).

대조 실험 (`verify_difference_sets.py controls`): `q = 2, 3, 4, 5, 7, 8, 9`에서
방법 A는 `phi(q^2+q+1)/(3e)`개 (`q = p^e`), 곧 `{0, 1}`을 포함하는 Singer
difference set의 개수만큼 찾는다. 방법 B는 정규형으로 거른 방법 A의 결과와
같고, `q = 6, 10`에서는 두 방법 모두 아무것도 찾지 못한다.

### 2. 순환 affine plane 없음: `Z_143`에는 `(13,11,12,1)` relative difference set이 없다

**주장.** `Z_143`의 12원소 부분집합 `D` 가운데, `N = 13 Z_143` (위수 11인
부분군) 밖의 모든 원소가 차로 정확히 한 번씩 나타나고 0이 아닌 `N`의
원소는 차로 나타나지 않는 것은 없다. Bose 대응으로 말하면, 한 점을
고정하고 나머지 143개 점 위에 정칙으로 작용하는 위수 143의 순환
collineation group을 갖는 order 12 affine plane은 없다.

같은 세 방법을 쓴다 (차에서 `N`을 제외). 방법 A가 찾는 `{0, 1}` 포함
집합은 최대 10원소이고 (크기 10이 25,068개, 크기 11과 12는 없음), 방법 B는
해가 없으며 (346,794 nodes), SAT 공식 (6까지의 ratio 절, 절 764,295개)은
UNSAT이다. SAT 반박은 CI가 다시 검사하는 인증서로 커밋했다.
`rds143_core.cnf`는 반박의 drat-trim core (공식의 절 36,827개, 각각
`audit_ds_cnf.py`로 다시 정당화됨)이고, `rds143_core.drat`는 다듬은 증명
(lemma 20,213개, 1.8 MB)으로 drat-trim이 약 2초 만에 검증한다.
`make_rds143_certificate.sh`가 두 파일을 재생성한다. 대조 실험:
`q = 3, 4, 5, 7, 8, 9, 11`에서 방법 A는 `phi(q^2-1)/(2e)`개, 곧 `{0, 1}`을
포함하는 Bose relative difference set의 개수만큼 찾고, `q = 6, 10`에서는 두
방법 모두 아무것도 찾지 못한다.

### 3. 위수가 13 이상의 소수인 collineation (Lean)과 위수 13인 경우

Lean 모듈 `AgenticConjectures/ProjectivePlaneOrder12.lean`은 order 12인 모든
projective plane에 대해 다음을 증명한다.

- `order13_fixed_antiflag`: 위수 13인 collineation은 정확히 한 점과 정확히
  한 직선을 고정하며, 그 점은 그 직선 위에 있지 않다.
- `prime_gt_13`: 위수가 소수 `p > 13`인 collineation이면 `p = 157`이고,
  고정하는 점도 직선도 없다.

따라서 collineation group의 위수를 나눌 수 있는 13 이상의 소수는 13과
157뿐이다. 위수 157인 원소가 생성하는 군은 점들 위에 정칙으로 작용하므로
1번의 순환 경우가 된다 (이 마지막 단계인 Singer 대응은 형식화하지 않았다).
증명은 고정점 세기이다. 소수 위수 `p`인 원소가 불변 집합에서 고정하는
원소의 수는 그 집합의 크기와 `p`를 법으로 합동이다. `p = 13`이면 고정
직선 위의 고정점은 0개 또는 13개이고, 두 고정점은 점별로 고정되는 직선을
만들며, 그 직선 밖에 고정점이 하나 더 있으면 항등 변환이 된다. 그래서
고정점은 0, 1, 13개 중 하나인데 `157 = 1 (mod 13)`이므로 정확히 하나이다.
쌍대적으로 고정 직선도 정확히 하나이고, 그 직선이 고정점을 지난다면 그
점을 지나는 13개 직선이 모두 고정되어야 하므로 불가능하다. `p > 13`이면
모든 고정 직선이 점별로 고정되고, `157 - 1 = 2^2 * 3 * 13`,
`157 - 13 = 2^4 * 3^2`이므로 고정점 0개와 `p = 157`만 남는다.
(비형식적으로는 위수 7도 같은 세기와 Bruck의 subplane 정리로 불가능하다.
위수 2, 3, 5, 11은 여기서 다루지 않는다.)

| 선언 | 내용 |
|---|---|
| `Collineation P L` | `pts p ∈ lns l ↔ p ∈ l`을 만족하는 순열 `pts`, `lns` |
| `card_fixed_modEq` | `σ ^ p = 1`, `p` 소수: 고정점 수 ≡ 전체 원소 수 (mod `p`) |
| `card_fixed_on_line_modEq` | 고정 직선 위의 고정점 수 ≡ `order + 1` (mod `p`) |
| `pts_eq_one_of_fixed_off_line` | 점별로 고정된 직선과 그 밖의 고정점이 있으면 `c.pts = 1` (모든 고정 직선이 점별로 고정되거나 고정점을 갖지 않을 때) |
| `order13_fixed_antiflag` | `order = 12`, `c.pts ^ 13 = 1`, `c.pts ≠ 1` ⇒ 유일한 고정점 `x₀`, 유일한 고정 직선 `l₀`, `x₀ ∉ l₀` |
| `prime_gt_13` | `order = 12`, `p` 소수, `13 < p`, `c.pts ^ p = 1`, `c.pts ≠ 1` ⇒ `p = 157`, 고정점과 고정 직선 없음 |

*명제 충실성.* plane은 mathlib의 `Configuration.ProjectivePlane P L`이면서
`ProjectivePlane.order P L = 12`인 것으로, upstream
`Erdos723.erdos_723.variants.eq_12`가 양화하는 개념 (`pp.order = 12`)과
같다. collineation은 결합 관계를 양방향으로 보존한다. "위수 `p`"는
`c.pts ^ p = 1`이고 `c.pts ≠ 1`이라는 뜻이며, 모듈은 이때
`c.lns ^ p = 1`과 `c.lns ≠ 1`도 성립함을 보인다. 정리들은 가상의 plane에
대한 조건부 명제이며, 그런 plane이 존재한다고 주장하지 않는다.

*위수 13 (탐색 미완료).* `order13_fixed_antiflag`의 antiflag `(P, l)`과
생성원 `g`에 대해 궤도는 `{P}`, `{l}`, `l`의 13개 점, `P`를 지나는 13개
직선, 그리고 길이 13인 점 궤도 11개와 직선 궤도 11개이다. `l` 위의 점
`R`을 고르고 `M = PR`로 두며, `Q_i`를 `i`번째 점 궤도에서 `M` 위에 있는
점, `L_j`를 `j`번째 직선 궤도에서 `R`을 지나는 직선이라 하자. 그러면
plane은 `{0, ..., 10}`의 순열 12개 `pi_s` (`s`는 `Z_13 \ {0}`의 원소)로서,
모든 `delta != 0`과 모든 `i, i'`에 대해 `{0, delta}` 밖의 `s` 가운데
정확히 하나가 `pi_s(i) = pi_{s-delta}(i')`를 만족하는 것과 동치이다
(자세한 내용은 `antiflag_cnf.py`). `antiflag_cnf.py`는 이를 `pi_1 = id`와
interval form의 `pi_2` (둘 다 궤도의 재명명에서 나옴)로 부호화하고,
`antiflag_decode.py`는 모델로부터 plane 전체를 다시 만들어 검사한다. 같은
부호화의 대조 실험에서 order 2, 4, 8은 SAT이고 복원한 plane이 검사를
통과한다. order 3, 5, 6, 7은 예상대로 UNSAT이다 (order 6인 plane은 없고,
order 3, 5, 7인 plane은 Desarguesian이며, 홀수 `q`에서는 `GF(q^2)`에서
`-1`의 norm이 1이므로 `PGL(3, q)`에 antiflag를 고정하고 그 직선 위에서
정칙인 위수 `q + 1`의 원소가 없다). order 12 인스턴스 (변수 9,438개, 절
231,188개)는 CaDiCaL 3.0.1로 3.8시간 (약 1.4 * 10^8 conflicts) 동안 답을
내지 못해 중단했다. 위수 13인 collineation에 대해서는 아무것도 주장하지
않으며, 문헌은 이를 배제한다 (Janko--van Trung).

### 재현

이 디렉터리에서 실행한다. 시간은 다른 작업과 함께 쓰는 Apple M5 Max에서
측정했다. CI는 표의 처음 다섯 명령을 실행한다.

| 명령 | 검사 내용 | 시간 |
|---|---|---|
| `python3 verify_difference_sets.py controls` | 1번과 2번의 대조 실험 | 11초 |
| `python3 verify_difference_sets.py affine` | 2번, 방법 A와 B | 10초 |
| `python3 verify_difference_sets.py planar` | 1번, 방법 B | 24초 |
| `python3 audit_ds_cnf.py 143 12 13 6 rds143_core.cnf` | 2번, 절 감사 | 1초 미만 |
| `drat-trim rds143_core.cnf rds143_core.drat` | 2번, DRAT 증명 | 2초 |
| `python3 verify_difference_sets.py planar-full` | 1번, 방법 A의 크기별 개수 | 15-25분 |
| `sh make_rds143_certificate.sh` | 2번 인증서 재생성 (우리 실행에서는 바이트 단위로 동일) | 8분 |

1번, 11원소 집합에 대한 A와 B 비교 (약 17분):

```sh
mkdir -p build
g++ -O3 -std=c++17 -o build/ds_enumerate ds_enumerate.cpp
g++ -O3 -std=c++17 -o build/ds_search_normalized ds_search_normalized.cpp
build/ds_enumerate 157 11 157 > build/a157_k11.out          # 15 min
build/ds_search_normalized 157 11 157 > build/b157_k11.out  # 50 s
python3 crosscheck_ab.py 157 157 build/a157_k11.out build/b157_k11.out
```

1번, 방법 C (약 15분, 증명 320 MB):

```sh
python3 ds_cnf.py 157 13 157 build/pds157.cnf 5
python3 audit_ds_cnf.py 157 13 157 5 build/pds157.cnf
cadical build/pds157.cnf build/pds157.drat     # exit code 20 (UNSAT), 5 min
drat-trim build/pds157.cnf build/pds157.drat   # s VERIFIED, 11 min
```

3번, 위수 13 부호화의 대조 실험 (몇 초):

```sh
for n in 2 3 4 5 6 7 8; do
  python3 antiflag_cnf.py $n build/af$n.cnf --interval
  cadical -q build/af$n.cnf > build/af$n.out; echo "n=$n exit=$?"  # 10 SAT, 20 UNSAT
done
python3 antiflag_decode.py 8 build/af8.out
```

### 주장하지 않는 것

- order 12인 projective plane의 존재에 대해서는 아무것도 주장하지 않는다.
  collineation group의 위수가 2 또는 3이거나 5, 11, 13으로 나누어지는
  plane에 대해서도 마찬가지이다.
- 새로움을 주장하지 않는다. 1번과 2번은 고전적 결과이고 (multiplier
  theorem과, 이 대상들에 대한 prime power conjecture의 출판된 컴퓨터
  검증으로부터도 따라 나온다), Lean 명제들은 초등적이다.
- 1번의 SAT 인증서는 로컬에서만 검사한다. CI는 1번의 방법 B, 2번의 방법
  A와 B, 대조 실험, 2번의 인증서를 다시 실행한다.

## FormalConjectures 원본

[로컬 upstream snapshot](upstream/README.md)은 Erdős problem 723의
`eq_12` Lean 선언과 고정 commit 정보를 보존한다. 선언은 `sorry`가 있는
존재 문제 명제이고, 이 디렉터리는 새 존재·비존재 결과를 주지 않는다.

## 근거

- Alexeev--Mixon,
  [Forbidden Sidon subsets of perfect difference sets](https://arxiv.org/html/2510.19804v2)
  (2026 판).
- Akiyama--Suetake--Tanaka,
  [Projective planes of order 12 do not have a collineation group of order 4](https://doi.org/10.1002/jcd.21869),
  *Journal of Combinatorial Designs* 31 (2023), 87--123.
- J. Singer, A theorem in finite projective geometry and some applications
  to number theory, *Trans. Amer. Math. Soc.* 43 (1938), 377--385.
- M. Hall Jr., Cyclic projective planes, *Duke Math. J.* 14 (1947),
  1079--1090.
- T. A. Evans and H. B. Mann, On simple difference sets, *Sankhya* 11
  (1951), 357--364.
- R. C. Bose, An affine analogue of Singer's theorem, *J. Indian Math. Soc.*
  6 (1942), 1--15.
- A. J. Hoffman, Cyclic affine planes, *Canad. J. Math.* 4 (1952),
  295--301.
- R. H. Bruck, Difference sets in a finite group, *Trans. Amer. Math. Soc.*
  78 (1955), 464--481 (subplane 정리).
- D. M. Gordon, The prime power conjecture is true for n < 2,000,000,
  *Electron. J. Combin.* 1 (1994), R6.
- Z. Janko and Tran van Trung, The full collineation group of any
  projective plane of order 12 is a {2, 3}-group, *Geom. Dedicata* 12
  (1982), 101--110.
