[English](README.md) | **한국어**

# R(3,10)의 인증된 대칭 부분 경우

상태: **계산으로 인증되었으나 동료 심사는 거치지 않음**.

이 디렉터리는 미해결 Ramsey 수 문제 `R(3,10) in {40,41}`과 관련된 정확한
탐색을 기록한다. 이 결과들은 `R(3,10)`의 값을 **결정하지 않는다**.

## 전체 문제와 현재 상태

`R(3,10)`은 모든 `n`정점 그래프가 삼각형이나 크기 10인 독립집합을 반드시
포함하게 되는 가장 작은 `n`이다. 그 값은 40 또는 41이다. Exoo의 39정점
구성이 하한 40을 주고, Angeltveit의 2025년 계산은 약 1,500억 개의 `(3,8)`
그래프를 약 3 CPU-년에 걸쳐 처리하여 상한 41을 준다. 2026년 동적 서베이는
이 구간을 그대로 유지하며, 39정점 `(3,10)` 그래프가 적어도 4,300만 개 있음을
기록한다.

독립수가 9 이하인 삼각형 없는 40정점 그래프가 하나라도 있으면 값이 41임이
증명된다. 그런 그래프를 모두 인증된 방식으로 철저히 배제하면 값이 40임이
증명된다. 아래 결과들은 그 탐색 공간 가운데 몇몇 자기동형 부류만을 배제한다.

## 배제된 부류 한눈에 보기

| 부류 | 반정칙으로 작용하는 군 | 궤도 | 추가 절 | CI에서 증명 재검사 |
|---|---|---|---|---|
| C20 bicirculant | `C20` | 2 x 20 | 없음 | 예 |
| `c10xc2-2orb` | `C10 x C2` | 2 x 20 | 없음 | 예 |
| `dic5-2orb` | `Dic5` | 2 x 20 | 없음 | 예 |
| `f20-2orb` | `F20` | 2 x 20 | 없음 | 예 |
| `d10-2orb` | `D10` | 2 x 20 | 없음 | 예 |
| `c10-4orb` | `C10` | 4 x 10 | 정규화 보조정리 | 예 |
| `d5-4orb` | `D5` | 4 x 10 | 정규화 보조정리 | 아니요, 로컬 검사만 |
| `q8-5orb` | `Q8` | 5 x 8 | 정규화 보조정리 | 아니요, 로컬 검사만 |
| `c8-5orb` | `C8` | 5 x 8 | 정규화 보조정리 | 아니요, 로컬 검사만 |

C20 bicirculant 인증서를 원래 기록된 형태로 먼저 설명하고, 나머지 부류는
[그 밖의 반정칙 부류](#그-밖의-반정칙-부류)에서 다룬다.

## C20 bicirculant: 인증된 명제

위수 20인 순환군이 40개의 정점에 두 궤도

`A_0,...,A_19` 와 `B_0,...,B_19`

로 작용하며, 두 첨자를 동시에 법 20으로 1씩 증가시킨다고 하자. 이 작용 아래
불변이면서 삼각형이 없고 독립수가 9 이하인 그래프는 존재하지 않는다.

동치로, 가상의 40정점 `(3,10)` Ramsey 그래프는 순환 구조가 `20^2`인
자기동형사상을 가질 수 없다. 그래프 이론의 용어로 말하면 반정칙(semiregular)
두 궤도 `C20` bicirculant 부류를 배제하는 것이다.

문헌상의 새로움은 주장하지 않는다. 표적 문헌 검색에서 이 정확한 부분 경우를
찾지 못했지만, 동료 심사를 거치지는 않았다. `search_circulant_r310.py`의 더
단순한 한 궤도 circulant 배제는 이미 출판된 더 강한 순환 그래프 결과에
함의되며, 독립적인 건전성 점검으로만 포함되어 있다.

## C20 bicirculant: 인코딩

이 작용에는 무향 간선 궤도가 정확히 40개 있다.

- 변수 1--10은 `A` 궤도 안의 순환 거리 1--10을 고른다.
- 변수 11--20은 `B` 안에서 같은 일을 한다.
- 변수 21--40은 20개의 오프셋 `A_i -- B_(i+d)`를 고른다.

보조 변수가 없는 권장 인증서는 변수 40개와 절 15,804개로 이루어진다.

- 서로 다른 음의 절 444개가 작용으로 몫을 취한 뒤의 모든 삼각형을 금지한다.
- 양의 절 15,360개는 각각 구체적인 10정점 집합에서 나오며, 그 집합의 쌍 가운데
  적어도 하나가 간선이어야 함을 요구한다.

10-집합 절 전체 가운데 일부만 있으면 된다. 모든 목표 그래프는 이렇게 유효한
절을 모두 만족해야 하고, 이 부분집합과 삼각형 절만으로 이미 UNSAT이다. 절들은
SAT+CEGAR로 찾았다. 반복마다 정확한 비트집합 탐색이 현재 모델의 독립 10-집합을
찾아 그 차단 절을 추가했다.

## C20 bicirculant: 인증서 산출물

| 파일 | 용도 | SHA-256 |
|---|---|---|
| `c20_final_nopb.cnf` | 40변수 DIMACS 식 | `d60efdded33920e02fcb60eb14bf3cb3b6d8990b5043a74e8ec716e617b33710` |
| `c20_separators_nopb.txt` | 각 양의 절의 근거인 구체적인 10-집합 | `30f1f231d96f3cf37aac19654361b863b20dfb24ba3720af355db974b84e933d` |
| `c20_nopb_unsat.drup` | Glucose 4.2 UNSAT 증명 | `4ff189f48b9b818f7113dae09fda6d492d43d360f047e5d9a8d737332fc53108` |
| `c20_result_nopb.json` | 생성기 통계와 해시 | -- |

`audit_c20_certificate.py`는 Python 표준 라이브러리만 사용한다. 처음 444개
절이 40정점 삼각형 제약 전체의 몫과 정확히 같은지, 그리고 나머지 각 절이
분리자 파일의 해당 줄에 있는 구체적인 10-집합과 정확히 일치하는지 확인한다.
이로써 DIMACS 식이 생성기와 독립적으로 주장하는 그래프 문제와 연결된다.

PySAT의 서로 다른 네 백엔드(Glucose 4.2, Lingeling, MiniSat 2.2, MapleSAT)가
모두 UNSAT을 보고한다. DRUP 증명은 34,864줄이다. 커밋
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`의 공식 `drat-trim`이 이를
`s VERIFIED`로 검증했다(증명 코어에 입력 절 8,114개와 보조정리 21,645개,
해소 단계 366,859개).

## C20 bicirculant: 검사 재현

`/home/user/projects/agentic-conjectures`에서:

```bash
python problems/ramsey-r3-10/audit_c20_certificate.py \
  problems/ramsey-r3-10/c20_final_nopb.cnf \
  problems/ramsey-r3-10/c20_separators_nopb.txt
```

기대 상태: `SEMANTICS VERIFIED`.

탐색에는 Python 3.13.12, `python-sat==1.9.dev13`, `pypblib==0.0.4`를
사용했다. 기존 식을 다른 솔버로 다시 풀고 증명을 재생성하려면:

```bash
python -m venv problems/ramsey-r3-10/.venv
problems/ramsey-r3-10/.venv/bin/pip install \
  'python-sat[pblib]==1.9.dev13'
problems/ramsey-r3-10/.venv/bin/python \
  problems/ramsey-r3-10/verify_c20_cnf.py \
  problems/ramsey-r3-10/c20_final_nopb.cnf \
  --proof problems/ramsey-r3-10/c20_nopb_unsat.drup
```

독립적인 공식 검사기로 증명을 검증하려면:

```bash
git clone https://github.com/marijnheule/drat-trim.git /tmp/drat-trim-r310
git -C /tmp/drat-trim-r310 checkout \
  2e3b2dc0ecf938addbd779d42877b6ed69d9a985
make -C /tmp/drat-trim-r310
/tmp/drat-trim-r310/drat-trim \
  problems/ramsey-r3-10/c20_final_nopb.cnf \
  problems/ramsey-r3-10/c20_nopb_unsat.drup
```

CEGAR 탐색으로 식을 재생성하려면:

```bash
problems/ramsey-r3-10/.venv/bin/python \
  problems/ramsey-r3-10/search_c20_bicirculant_r310.py \
  --solver cadical195 --omit-degree-encoding \
  --cnf-output problems/ramsey-r3-10/c20_final_nopb.cnf \
  --witness-output problems/ramsey-r3-10/c20_separators_nopb.txt \
  --json-output problems/ramsey-r3-10/c20_result_nopb.json
```

생성기가 내놓는 SAT 모델의 순서는 솔버와 버전에 따라 달라질 수 있다. 재생성된
유효한 인증서가 바이트 단위로 같을 필요는 없으며, 의미 감사와 독립적으로
검증된 UNSAT 증명이 실질적인 검사이다.

## 그 밖의 반정칙 부류

2026-10-24에 일반화된 도구 `search_symmetric_r310.py`,
`cegar_symmetric_r310.cpp`, `audit_symmetric_certificate.py`,
`build_symmetric_certificate.py`와 함께 추가했다. 인증서는 `symmetric/`에 있다.

### 인증된 명제

`H`를 위수 `m`이 40의 약수인 군이라 하고 `k = 40/m`으로 두자. `H`는 정점 집합
`{0,...,k-1} x H`에 왼쪽 곱셈 `g.(j, x) = (j, g x)`로 작용한다. 이 작용은
반정칙이며(항등원이 아닌 원소는 어떤 정점도 고정하지 않는다) 크기 `m`인 궤도
`k`개를 가진다. 40개의 점 위에서 `H`의 반정칙 작용은 모두 이 작용과 순열
동형이다. 궤도의 대표 `v_j`를 골라 `(j, x)`를 `x.v_j`로 보내면 된다.

표의 각 부류에 대해, **이 정점 집합 위에서 작용 아래 불변이고 삼각형이 없으며
독립수가 9 이하인 그래프는 존재하지 않는다.** 동치로, 어떤 40정점
`(3,10)`-그래프도 `H`와 동형이면서 `k`개의 궤도로 반정칙 작용하는 자기동형군을
갖지 않는다.

| 부류 | `H` | 궤도 | 변수 | 삼각형 절 | 정규화 절 | 10-집합 절 | 증명 보조정리 | 증명 (xz) | drat-trim |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|
| `c10xc2-2orb` | `C10 x C2` | 2 x 20 | 42 | 444 | -- | 3,168 | 25,148 | 0.33 MB | 0.6 s |
| `dic5-2orb` | `Dic5` | 2 x 20 | 40 | 444 | -- | 2,474 | 12,668 | 0.17 MB | 0.2 s |
| `f20-2orb` | `F20` | 2 x 20 | 44 | 492 | -- | 8,772 | 89,487 | 1.17 MB | 5.0 s |
| `d10-2orb` | `D10` | 2 x 20 | 50 | 484 | -- | 21,660 | 324,773 | 4.36 MB | 38 s |
| `c10-4orb` | `C10` | 4 x 10 | 80 | 968 | 27 + 93 | 22,146 | 276,690 | 4.25 MB | 28 s |

`Dic5`는 dicyclic 군 `<x, y | x^10 = 1, y^2 = x^5, y x y^-1 = x^-1>`이고,
`F20 = AGL(1,5)`는 `Z/5` 위의 사상 `z -> a z + b`(`a != 0`)로 이루어진
Frobenius 군이며, `D10`, `D5`는 위수 20과 10인 이면체군이다. 두 궤도
인증서는 C20 인증서처럼 순수하다(삼각형 절과 10-집합 절만 쓴다). 네 궤도와
다섯 궤도 인증서에는 아래 정규화 보조정리의 절이 더해진다. "증명 보조정리"는 커밋된 이진
DRAT 증명의 절 수이며, drat-trim 시간은 부하가 큰 공유 기계(Apple M5 Max)에서
잰 로컬 벽시계 시간이다.

다음 세 부류는 DRAT 증명이 파일당 5 MB 한도보다 훨씬 커서 분리자 목록만
커밋한다. CI는 감사 스크립트를 다시 실행하여 분리자를 확인하고, 스크립트가 쓰는
식의 SHA-256이 기록된 값과 같은지 확인한다. 증명 자체는 CaDiCaL 3.0.1로 다시
만들어 로컬에서 drat-trim으로 검사한다(명령은 `status.yaml`에 있으며 CI에서는
실행하지 않는다).

| 부류 | `H` | 궤도 | 변수 | 삼각형 절 | 정규화 절 | 10-집합 절 | 증명 보조정리 | 증명 크기 | drat-trim |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|
| `d5-4orb` | `D5` | 4 x 10 | 88 | 984 | 27 + 9 | 125,459 | 3,417,647 | 178 MB | 2,120 s |
| `q8-5orb` | `Q8` | 5 x 8 | 100 | 1,220 | 28 + 60 | 269,223 | 5,281,325 | 290 MB | 4,955 s |
| `c8-5orb` | `C8` | 5 x 8 | 100 | 1,225 | 28 + 60 | 292,542 | 6,422,834 | 360 MB | 5,349 s |

증명 열은 아래 로컬 명령이 다시 만드는 CaDiCaL `--unsat` 원본 증명, 곧
drat-trim이 검사한 증명을 나타낸다("증명 보조정리"는 drat-trim이 보고한 보조정리
수이고, `d5-4orb`의 시간은 drat-trim이 보고한 검증 시간이다). `d5-4orb`의 경우
빌드 단계에서 127 MB 크기의 코어 보조정리 증명(보조정리 2,517,278개, xz 압축 후
40.6 MB, drat-trim 407초)도 뽑았으며 `symmetric/d5-4orb.build.json`에 기록되어
있다. `d5-4orb` 분리자는 코어 줄이기를 세 번 거쳐 168,651개에서 125,459개로
줄였고, `q8-5orb`와 `c8-5orb` 목록은 줄이지 않은 탐색 출력 그대로이다.

### 따름정리 (손으로 한 논증이며 기계 검증되지 않음)

1. 동형을 무시하면 위수 20인 군은 `C20`, `C10 x C2`, `D10`, `Dic5`, `F20`뿐이다.
   따라서 C20 인증서와 순수한 두 궤도 인증서들을 합치면, 두 궤도로 반정칙
   작용하는 위수 20인 군은 모두 배제된다.
2. 그러므로 어떤 40정점 `(3,10)`-그래프도 Cayley 그래프가 아니다. 위수 40인 군
   `G`가 정칙으로 작용하면, Sylow 5-부분군의 개수는 8의 약수이면서 법 5로 1이므로
   Sylow 5-부분군 `P`는 정규이다. 따라서 Sylow 2-부분군의 위수 4인 임의의
   부분군 `Q`에 대해 `PQ`는 위수 20인 부분군이고, 두 궤도로 반정칙 작용하므로
   1번이 적용된다.
3. `c10-4orb`는 모든 순환의 길이가 10인(순환 구조 `10^4`) 자기동형사상을 모두
   배제한다. 순환 구조가 `20^2`인 자기동형사상의 제곱, `40^1`인 것의 네제곱,
   그리고 반정칙으로 작용하는 `C10 x C2`, `D10`, `Dic5`의 위수 10인 원소는 모두
   이 순환 구조를 가지므로, `c10-4orb` 하나만으로 circulant 경우, C20 인증서,
   두 궤도 부류 가운데 셋을 다시 덮는다. 위수 10인 원소가 없는 `F20`은 덮지
   않는다.
4. `c10-4orb`와 `d5-4orb`를 합치면 위수 10인 두 군이 모두 배제되므로, 어떤
   40정점 `(3,10)`-그래프도 위수 10인 반정칙 자기동형군을 갖지 않는다. 위수
   20이나 40인 군은 정규 Sylow 5-부분군 `P`와 involution `t`를 가지므로 `P<t>`는
   위수 10인 부분군이고, 반정칙 군의 부분군은 반정칙이다. 따라서 이 두 부류만으로
   1번과 2번을 다시 덮지만, 정규화 보조정리를 거쳐서만 그렇다.
5. `c8-5orb`는 순환 구조가 `8^5`인 자기동형사상을 모두 배제하며, 따라서 순환
   구조가 `40^1`인 것도 배제한다(그 다섯제곱의 순환 구조가 `8^5`이다).
   `q8-5orb`는 반정칙 `Q8` 작용을 배제한다. 위수 8인 나머지 군(`C4 x C2`,
   `C2^3`, `D4`)은 덮지 않는다.

### 방법

인코딩은 C20의 것을 일반화한다. 780개의 정점 쌍 위의 `H`-궤도마다 Boolean
변수를 하나씩 두고, 9,880개 삼각형 절 전체의 몫과, 구체적인 10정점 집합 `S`마다
"`S`의 어떤 쌍은 간선이다"라는 양의 절을 하나씩 쓴다. 이런 절은 `S`를 어떻게
찾았든 독립수가 9 이하인 모든 그래프에서 성립하므로, 탐색 휴리스틱은 건전성에
전혀 영향을 주지 않는다.

- `search_symmetric_r310.py`는 생성원으로 부류를 정의하고, 탐색 인스턴스,
  정규화 블록, 최종 CNF를 쓴다. 분리자 목록을 drat-trim 코어로 줄이는 기능과,
  혹시 모델이 나오면 독립수를 정확히 검사하는 `check-sat`도 있다.
- `cegar_symmetric_r310.cpp`는 CaDiCaL 3.0.1 C++ API 위의 탐색 백엔드이다.
  `--up`을 주면 IPASIR-UP 외부 전파기로 동작한다. 현재 거짓으로 할당된 쌍들이
  10-클릭(부분 할당이 강제하는 독립 10-집합)을 품으면 그 10-집합 절을 추가하고,
  완전한 모델마다 독립수를 정확히 검사하므로, 실행은 UNSAT으로 끝나거나 진짜
  `(3,10)`-그래프를 내놓는다. `--up` 없이는 C20 탐색과 같은 모델 단위 CEGAR
  루프를 돌며, 분기 한정으로 찾은 짧은 분리자 절을 추가한다. 두 궤도 분리자
  목록은 이 루프(`--k 1`)에서, 네 궤도와 다섯 궤도 목록은 정규화
  절(`--extra`)과 함께 쓴 `--up`에서 나왔다.
- 코어 줄이기: CaDiCaL이 현재 식이 UNSAT임을 DRAT 증명과 함께 보이고,
  `drat-trim -c`가 UNSAT 코어를 뽑으며, 코어에 들어 있는 절의 분리자만 남긴다.
- 최종 인증서: 감사 스크립트가 DIMACS 식을 쓰고, CaDiCaL 3.0.1(`--unsat`)이
  DRAT 증명으로 UNSAT을 보이며, `drat-trim -C -l`이 코어 보조정리를 이진 DRAT
  증명으로 뽑고, drat-trim이 그 증명을 다시 검증한다. 커밋하는 것은 코어
  보조정리 증명(xz 압축)뿐이다. `q8-5orb`와 `c8-5orb`(`--no-proof-output`)는
  drat-trim이 CaDiCaL 원본 증명을 한 번 검사하고 분리자만 저장한다.
- `build_symmetric_certificate.py`는 한 부류에 대해 이 파이프라인 전체를
  실행한다.

### 정규화 보조정리 (네 궤도와 다섯 궤도 부류)

`H`-불변 그래프는 연결 집합 `D_ij = { x^-1 y : (i, x) ~ (j, y) }`로 결정된다.
다음 두 종류의 정점 사상은 모든 `g.`와 가환하므로, 불변 그래프를 그와 동형인
불변 그래프로 보낸다.

- 한 궤도의 오른쪽 평행이동 `(j, x) -> (j, x h)`(다른 궤도는 고정): `D_0j`를
  `D_0j h`로, `D_jj`를 `h^-1 D_jj h`로 바꾸고, `D_00`과 `l != j`인 모든 `D_0l`은
  그대로 둔다.
- 궤도의 재번호 `(j, x) -> (pi(j), x)`: 내부 집합 `D_jj`들을 치환한다.

내부 집합의 위치 `{d, d^-1}`가 모든 켤레 사상에 의해 자기 자신으로 가면 그
위치를 *안정적*이라 하자. `H`가 아벨 군이면 모든 위치가 안정적이고(`C10`은
다섯 개, `C8`은 네 개), `Q8`에서도 그렇다(`x`의 켤레는 `x`와 `x^-1`뿐이다).
`D5`에서는 회전 쌍 두 개만 안정적이다. 궤도 `j`의 *키*는 안정적인 위치에서의 내부
변수들의 벡터이다. 임의의 불변 그래프가 주어지면, 먼저 키가 사전식으로
감소하지 않도록 궤도를 재번호하고, 그다음 `D_0j`가 비어 있지 않은
`j = 1, ..., k-1`마다 `D_0j`의 원소 `d`를 골라 궤도 `j`를 `h = d^-1`로
평행이동한다. 평행이동은 어떤 키도, 앞서 맞춘 `D_0l`도 바꾸지 않으므로,
결과는 처음 그래프와 동형이며 다음을 만족한다.

- (n) `D_0j`가 비어 있지 않으면(`j >= 1`) `e`가 `D_0j`에 들어 있다: 이항 절
  `-x((0,e),(j,d)) OR x((0,e),(j,e))`, 모두 `(k-1)(m-1)`개(크기 10인 궤도
  넷이면 27개, 크기 8인 궤도 다섯이면 28개).
- (s) `key_0 <= key_1 <= ... <= key_(k-1)`: "같은 접두부 다음에 1 대 0"이라는
  금지된 배치마다 절 하나씩, 보조 변수 없이 쓴다.

따라서 그 부류에 `(3,10)`-그래프가 있다면 정규화된 식의 모델이 생기고, 그
식이 UNSAT이면 부류가 배제된다. 감사 스크립트는 가설(두 가환 성질과 키
위치의 안정성)을 기계적으로 확인하고 두 블록을 다시 만든다. 보조정리 자체는
위의 손 논증이다.

### 감사

`audit_symmetric_certificate.py`는 Python 표준 라이브러리만 사용하고 탐색
코드를 가져오지 않는다. 각 부류에 대해 다음을 한다.

1. 전체 곱셈 법칙으로 군을 만들고 군 공리를 확인하며, 같은 위수의 군들
   가운데 그 군을 식별하는 불변량(아벨 여부, 원소 위수 분포)을 확인한다.
2. 모든 원소의 작용을 만들고, 그 작용이 충실하고 반정칙인지 확인한다.
3. 쌍 궤도, 삼각형 절, (요청하면) 정규화 블록을 다시 계산하고, 분리자의
   각 줄이 서로 다른 정점 열 개인지 확인한 뒤 줄마다 절 하나를 만든다.
4. 주어진 DIMACS 파일이 정확히 이 식인지 확인하거나(`--check-cnf`) 식을
   쓴다(`--write-cnf`).

커밋된 증명은 감사 스크립트가 쓰는 식을 대상으로 하므로 CNF 파일은 커밋하지
않는다. CNF는 바이트 단위로 똑같이 재생성된다.

커밋된 파일의 SHA-256(옆의 각 `<class>.build.json`은 최종 빌드 단계의 CaDiCaL
옵션, 시간, drat-trim 요약을 기록한다):

```text
cb3fc8a19d1d46e6609cdd34e910852a7c30a0d192157feff77829676c0afa71  symmetric/c10xc2-2orb.separators.txt.xz
9196015b435c8375f456c9784b307cec0c0201bb60439d987578165b0a008fdc  symmetric/c10xc2-2orb.drat.xz
3e5fc65b37fe5f90c62b9e4b654a7b316ced9221859e011f6afdb691cdcf9a53  symmetric/dic5-2orb.separators.txt.xz
9ebefa3ba909637f8318aa9d27e0e79900be7d2fa3169ff53a4c27e9f21f957a  symmetric/dic5-2orb.drat.xz
be22cb0267a612c635c6ed13757449b8ae098e8091e40ee509af269a383f743c  symmetric/f20-2orb.separators.txt.xz
da23988d3099b2e060b93080f912bf08a6e8ff69c38a13a3699acf4ccbfca5c7  symmetric/f20-2orb.drat.xz
ae0ae1d6f6f2280f642b0bc0e7d2d57834f3f20e6a1218cc754fb62882b48ad7  symmetric/d10-2orb.separators.txt.xz
6c31867abaa1b341ccc61e022ed98542c03dd733bb8f08e180dad4e4f11bc437  symmetric/d10-2orb.drat.xz
2bd4e27729718573138f392768530c9ed37bedf360fbe09ff744d8a90038f352  symmetric/c10-4orb.separators.txt.xz
3575294b1feb798cbd28a1254c5af41d26c26ef789425470259f5b2d17190e03  symmetric/c10-4orb.drat.xz
28d2d9ce4085b3282b17713c37e57b6b4b87814d1ec7937a92e0dd5569bb4dc0  symmetric/d5-4orb.separators.txt.xz
8f7355a5c2b5b435724597360deb35d3cdd251fcd6037cccc088b0a00f6e976c  symmetric/q8-5orb.separators.txt.xz
189b55136dd823bbfb41b1effcd37e30002fcd77498cd3db2607451b603cb462  symmetric/c8-5orb.separators.txt.xz
```

아래 명령으로 감사 스크립트가 쓰는 CNF 파일의 SHA-256:

```text
e55ec00928f6c250e4ac993044f324282921f7ef04598a8c008959673678c16d  /tmp/r310-c10xc2-2orb.cnf
855674742fcf30e55e1f88de2ae6547096ef2004cdb40f0726d1147d82f2c105  /tmp/r310-dic5-2orb.cnf
dc4d776d2decf023f3aca0209f462f16e3bc15373b56702d8e6af512be7bccf8  /tmp/r310-f20-2orb.cnf
9d6bc946c4e7350819d74a82fbb9809a9297b040711f87410ad4b1ce9639f6a5  /tmp/r310-d10-2orb.cnf
73e3f95d8707846eaf75d12957f5b09d94a10a8c5c3deb0f5d24bdea22be1d02  /tmp/r310-c10-4orb.cnf
7c6e1822ef33c1c073c1d8fe6fa25bedfc080f44050291325da6738558c99c2c  /tmp/r310-d5-4orb.cnf
42a69ef999a4c653e1268ece7e020c6c99dac91848b9f851497af19c34026beb  /tmp/r310-q8-5orb.cnf
071704c2b10c71893e9e06e564863184fbc28ce05f73ce3eb0227a2cb8b934c1  /tmp/r310-c8-5orb.cnf
```

증명을 커밋하지 않은 세 부류에 대해 drat-trim이 검사한 CaDiCaL 3.0.1 `--unsat`
원본 증명의 SHA-256(아래 명령으로 `d5-4orb` 증명을 다시 만들었더니 같은
기계에서 바이트 단위로 똑같이 재현되었다. 다른 빌드나 플랫폼에서는 다른 유효한
증명이 나올 수 있다):

```text
f8905f653ff412ec6e9bb4962d6d5327009bc0c799e04a2bd4ceaaecdd652fe3  /tmp/r310-d5-4orb.drat (178,315,102 bytes)
5189558b0c0f3a1d26628379bae66c20a90381ed9c5f55a268ac80e36ecb8160  /tmp/r310-q8-5orb.drat (289,693,016 bytes)
fc039656b902c4af9f4f0758c8c4d6a03a85fdd08f1ff2ae75415eae756cc2d9  /tmp/r310-c8-5orb.drat (360,045,378 bytes)
```

### 검사 재현

`problems/ramsey-r3-10`에서, `PATH`에 `drat-trim`이 있는 상태로:

```bash
python3 audit_symmetric_certificate.py f20-2orb \
  symmetric/f20-2orb.separators.txt.xz --write-cnf /tmp/r310-f20-2orb.cnf
xz -dc symmetric/f20-2orb.drat.xz | drat-trim /tmp/r310-f20-2orb.cnf -i
```

기대 출력: `"status": "SEMANTICS VERIFIED"`와 `s VERIFIED`. `c10-4orb`는
감사 호출에 `--normalised --sorted-orbits`를 더한다. `status.yaml`의 `verify`
항목은 증명이 커밋된 다섯 부류에 대해 이 명령들을 실행한다(로컬에서 각각 25초
이내).

`d5-4orb`, `q8-5orb`, `c8-5orb`는 증명을 다시 만들어야 한다(로컬 전용이며
`cadical` 실행 파일이 필요하다. 종료 코드 20이 UNSAT을 뜻한다):

```bash
python3 audit_symmetric_certificate.py d5-4orb symmetric/d5-4orb.separators.txt.xz \
  --normalised --sorted-orbits --write-cnf /tmp/r310-d5-4orb.cnf \
  --expect-sha256 7c6e1822ef33c1c073c1d8fe6fa25bedfc080f44050291325da6738558c99c2c
cadical -q --unsat /tmp/r310-d5-4orb.cnf /tmp/r310-d5-4orb.drat
drat-trim /tmp/r310-d5-4orb.cnf /tmp/r310-d5-4orb.drat
```

이 부류들에 대한 CI 검사는 첫 번째 명령뿐이다. 로컬에서 감사는 2~4초
걸린다. 부하가 큰 공유 기계에서 CaDiCaL은 `d5-4orb`에 약 4~8분, `q8-5orb`와
`c8-5orb`에 각각 46분이 걸렸고, drat-trim은 약 35분(`d5-4orb`), 83분
(`q8-5orb`), 89분(`c8-5orb`)이 걸렸다.

인증서를 처음부터 재생성하려면(로컬 전용이며 C++17 컴파일러, 라이브러리와
실행 파일 형태의 CaDiCaL >= 2.0, drat-trim이 필요하다. `--cadical-prefix`로
CaDiCaL 설치 위치를 지정하며 기본값은 `/opt/homebrew`이다):

```bash
python3 build_symmetric_certificate.py dic5-2orb --outdir /tmp/r310-symmetric
python3 build_symmetric_certificate.py c10-4orb --normalise --outdir /tmp/r310-symmetric
```

부하가 큰 로컬 기계에서 잰 시간: `dic5-2orb` 예는 약 6초, `c10-4orb` 예는 약
5분 걸린다(탐색 30초, 코어 줄이기 세 번, 최종 증명. 분리자 23,062개로 끝나며,
커밋된 목록은 코어 줄이기를 한 번 더 거쳤다). 커밋된 네 궤도와 다섯 궤도 목록을
만든 탐색은 50초(`c10-4orb`), 15분(`d5-4orb`), 44분(`q8-5orb`), 54분(`c8-5orb`)
걸렸고, `d5-4orb`는 코어 줄이기 세 번과 최종 증명에 약 두 시간이 더 걸렸다.
커밋된 분리자 목록은 같은 백엔드의 임시 실행에서 나온 것이므로, 재생성된
인증서는 유효하지만 바이트 단위로 같을 필요는 없다.

### 결과 없이 시도한 것

- `c5-8orb`(여덟 궤도의 `C5`, 변수 156개, 정규화 절 포함): `--up` 탐색이 5.2시간
  동안 분리자 226만 개를 모았지만 끝나지 않아 중단했다. 90분 예산을 넘긴 것은
  실행을 감독하던 세션이 중단되었기 때문이다. 이 부류를 배제하면 순환 구조가
  `5^8`인 자기동형사상이 모두 배제된다.
- 시도하지 않은 것: 다섯 궤도의 `C4 x C2`, `C2^3`, `D4`, 열 궤도의 `C4`와
  `C2 x C2`, 그리고 고정점 없는 involution(스무 궤도의 `C2`, 변수 400개). 생성기,
  백엔드, 감사 스크립트에는 이 부류들이 이미 정의되어 있다(`c4xc2-5orb`,
  `c2xc2xc2-5orb`, `d4-5orb`, `c4-10orb`, `c2xc2-10orb`, `c2-20orb`).

### 주장하지 않는 것

- `R(3,10)`의 값은 결정하지 않는다.
- 나열한 반정칙 작용만 배제한다. 고정점이 있거나 길이가 다른 순환을 가진
  자기동형사상(예: 고정점이 있는 involution)은 덮지 않으며, 결과 없이 시도한
  부류도 마찬가지이다.
- 정규화 보조정리와 위의 따름정리는 손으로 한 논증이다. 기계로 검증한 것은
  감사를 거친 식들이 UNSAT이라는 사실이다.
- `d5-4orb`, `q8-5orb`, `c8-5orb`의 증명은 로컬 기계 한 대에서만 drat-trim으로
  검사했다. CI는 분리자와 식의 해시를 확인할 뿐 증명은 검사하지 않는다.
- 문헌상의 새로움은 주장하지 않는다.

### 문헌 메모

- Circulant 그래프: 한 궤도 순환 경우는 출판된 순환 그래프 결과에 함의된다(위
  참조). `c10-4orb`도 이를 다시 덮는다.
- Cayley 그래프와 정점 추이 그래프: Holt와 Royle이 48개 미만의 정점을 가진 정점
  추이 그래프를 모두 열거했으므로, 따름정리 2(40정점 Cayley `(3,10)`-그래프는
  없다)는 원리적으로 그 목록에서 읽어 낼 수 있고 아마 이미 알려져 있을 것이다.
  명시적인 진술을 찾아보지는 않았다.
- 위의 여러 궤도 부류를 다룬 출판물은 알지 못하지만, 이번 추가 작업에서는 여기
  인용한 자료 외에 새로운 문헌 검색을 하지 않았으므로 새로움을 주장하지 않는다.

## 출판된 맥락

- Vigleik Angeltveit, [R(3,10) <= 41](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i4p30/pdf/), *Electronic Journal of Combinatorics* 32(4), 2025, #P4.30.
- Stanislaw Radziszowski, [Small Ramsey Numbers, revision 18](https://www.combinatorics.org/ojs/index.php/eljc/article/download/DS1/pdf/), *Electronic Journal of Combinatorics*, 2026년 4월 24일.
- Derek Holt, Gordon Royle, A census of small transitive groups and vertex-transitive graphs, *Journal of Symbolic Computation* 101 (2020).
