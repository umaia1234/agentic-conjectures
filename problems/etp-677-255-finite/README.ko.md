[English](README.md) | **한국어**

# ETP 문제 8.1: 유한 마그마에서의 등식 677과 등식 255

등식 677은 $x=y\diamond(x\diamond((y\diamond x)\diamond y))$이고 등식 255는
$x=((x\diamond x)\diamond x)\diamond x$이다. Equational Theories
Project(ETP)는 일반 마그마에서 677이 255를 함의하지 않음을 보였고, 유한한
경우는 [Tao 외, *The Equational Theories Project*](https://arxiv.org/abs/2512.07087)의
문제 8.1이다. FormalConjectures의 진술([upstream 스냅샷](upstream/README.md))은
다음과 같이 묻는다.

> “Does Equation 677 imply Equation 255 in every finite magma?”

docstring에는 프로젝트가 잠정적으로 답을 "아니오", 즉 유한 반례 모델이
존재한다고 추측한다는 설명이 덧붙어 있다. **이 문제는 여전히 미해결이다.** 이
디렉터리는 부분 결과를 기록한다. 반례 모델 크기에 대한 인증된 하한과 전수
탐색 하한, 구조화된 한 모델 족에 대한 탐색, 그리고 이들을 뒷받침하는 Lean
사실들이다. 새로움을 주장하지 않는다.

## 결과

*반례 모델*이란 E677을 만족하지만 E255를 만족하지 않는 유한 마그마이다.

1. **Lean** ([`Etp677Implies255Finite.lean`](../../AgenticConjectures/Etp677Implies255Finite.lean),
   `sorry`, 추가 공리, `native_decide` 없음): upstream 진술을
   `def statement : Prop`로 옮겼다. 모든 탐색 규칙의 근거가 되는 구조적 사실
   (왼쪽 곱의 전단사성, 고정자의 유일성, E677의 역형태, 한 점에서 E255가
   실패할 때의 결과), 한 원소로 생성되는 반례 모델로의 환원, 그리고 평행이동
   불변 가설과 그 CNF 및 자기동형 대칭 깨기의 건전성을 증명했다.
2. **원소가 10개 이하인 반례 모델은 없다(DRAT 인증).** 각 $n\le10$에 대해
   "$\{0,\dots,n-1\}$ 위에 $0$으로 생성되고 표준 라벨링을 따르며 $0$에서
   E255가 실패하는 E677 마그마가 있다"는 CNF가 충족 불가능하며, `drat-trim`이
   그 DRAT 증명을 검증한다. $n\le8$의 증명은 커밋되어 CI에서 검사되고,
   $n=9,10$의 증명은 아래 명령으로 다시 생성한다.
3. **두 번째 방법으로 얻은 같은 하한(전수 탐색, 인증서 없음).** SAT
   인코딩과 코드를 공유하지 않는 DFS가 원소 10개 이하의 반례 모델을 찾지
   못한다. $n\le9$는 CI에서 다시 실행하고 $n=10$은 로컬에서 실행했다(아래
   표). $n=11$에서는 DFS의 부분 트리 27개 중 24개를 반례 모델 없이 끝냈고
   나머지 3개는 끝나기 전에 중단했다. 따라서 이 디렉터리는 $n=11$을 다루지
   **않는다**(앞선 탐색들이 다루었다. 아래 참고).
4. **위수 29 이하의 군 위에는 평행이동 불변 반례 모델이 없다(SAT,
   인증서 없음).** GAP SmallGroups 라이브러리에 있는 위수 29 이하의
   모든 군 $G$에 대해, $x\diamond y=x\,f(x^{-1}y)$가 E677을 만족하는 고정점
   없는 $f:G\to G$는 없다.

general 모드(E255를 부정하지 않음)에서 같은 탐색은 한 원소로 생성되는 점
붙은 E677 마그마를 센다. 크기 $1,\dots,9$에서 표준 표는
$1,0,0,0,0,0,2,0,1$개이며
[`results/general_tables.txt`](results/general_tables.txt)에 있다. DFS와
SAT 나열의 결과가 일치한다.

모든 절과 규칙의 수학적 근거, 그리고 각 결과가 무엇을 신뢰하는지는
[수학적 세부 사항](DETAILS.ko.md)에 있다.

## 기존 작업과의 관계

아래 내용은 모두 ETP Zulip 스레드
[FINITE: 677 -> 255](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255)와
[등식 677에 관한 블루프린트 장](https://teorth.github.io/equational_theories/blueprint/677-chapter.html)에서
2026-10-24에 확인한 것이다.

- **크기 하한.** Mace4 탐색으로 크기 11까지 반례 모델이 배제되었고
  (2025-03-12 보고, 크기 11에 57일), 이후 DPLL 모델 탐색(`eq677` 프로젝트)이
  크기 11을 약 3시간에 끝낸다고 보고되었다. 크기 12–16에 대한
  CaDiCaL 실행은 244일이 지나도 끝나지 않았다. 따라서 우리의 $n\le10$
  하한은 **새롭지 않으며**, 앞선 탐색들은 $n=11$까지 간다. 이 디렉터리가
  더하는 것은 $n\le10$에 대한 DRAT 인증서(스레드는 이런 비존재 결과를
  형식화하는 방법으로 unsat 인증서를 제안하며, 올라온 인증서는 찾지
  못했다)와, $n=10$을 단일 스레드 SAT 실행 몇 분으로 만드는 인코딩이다.
- **평행이동 불변 모델.** 명시적 군에 대한 탐색으로 위수 26 이하의 어떤 군에도
  고정점 없는 해가 없다고 보고되었고, 제한된 탐색(예를 들어 $f^2=1$이나
  $f^4=1$)은 더 멀리 갔으며,
  [`eq677`](https://github.com/memoryleak47/eq677) 모델 데이터베이스는 여러
  방법 가운데 $\mathbb Z/n$ 위의 평행이동 불변 탐색을 $n=37$까지 써서
  만들어졌다. 여기서의 제한 없는 탐색은 위수 1부터 다시 시작해 29까지
  진행한다. 우리가 찾은 보고를 넘어서는 부분은 위수 27과 28의 비순환군
  일곱 개뿐이다.
- 한 원소로 생성되는 반례 모델로의 환원, 성질 F1–F6, 평행이동 불변 재구성은
  스레드와 블루프린트에서 표준적인 내용이다. 여기서는 이를 Lean으로
  형식화하고 인코딩의 근거로 사용한다.

## 전수 탐색 실행

| $n$ | SAT (CaDiCaL 3.0.1) | DRAT 검사 (drat-trim) | DFS 노드 수 | DFS 시간 |
|---|---|---|---|---|
| ≤8 | < 0.3 s | < 0.3 s, 증명 커밋됨 | ≤ 13,705 | < 0.1 s |
| 9 | 5.2 s | 3.6 s (이진 증명 12.7 MB) | 831,060 | 1.3 s |
| 10 | 474.6 s | 421.9 s (이진 증명 631 MB) | 179,952,881 | 294 s |
| 11 | — | — | 부분 트리 27개 중 24개에서 25,714,117,407 (3개 중단) | CPU 13.5시간 (끝난 부분) |

DFS 시간은 Apple silicon 노트북의 단일 스레드 기준이다. $n=11$은 깊이 7에서
300개 부분으로 나누고(부분 1은 다시 깊이 12에서 40개로 나눔) 네 개씩
동시에 실행했다. 깊이 7의 노드는 부분 0–26에만 있고, 나머지 부분은 공유하는
위쪽 노드 49개만 다시 지난다. 부분 20, 25, 26은 계산 예산이 다해 각각
4.8, 6.3, 9.5 CPU 시간 뒤에 중단했으며 아무 결과도 내지 않는다. 부분별 결과는
[`results/dfs_n11.txt`](results/dfs_n11.txt)에 있다.

평행이동 불변 탐색은 위수 29 이하의 군 88개를 대칭 깨기 경우 2,417개로
나누었고, 모든 경우가 UNSAT이었으며 솔버 시간은 4.4시간이었다(한 번에 한두
경우, 제한 600초). 제한에 걸린 위수 28의 두 경우는 3600초 제한으로 다시
실행했고 각각 1,575초와 2,227초가 걸렸다. 위수 30은 283개 경우 중 61개를
끝낸 뒤 중단했고(시간 초과 하나 더, 모델 없음) 위수 31은 시작하지 않았다.
군별 결과는 [`results/tinv_groups.txt`](results/tinv_groups.txt)에 있다.

## 재현

이 디렉터리에서:

```bash
python3 verify_drat.py
```

이 명령은 `search/gen_cnf.py`로 $n\le8$의 CNF를 다시 만들고, SHA-256을
[`certificates/SHA256SUMS`](certificates/SHA256SUMS)와 비교한 뒤 커밋된
증명에 `drat-trim`을 실행한다(CI, 1초 미만). CaDiCaL이 설치되어 있으면

```bash
python3 verify_drat.py --solve 9 10
```

으로 $n=9,10$을 다시 풀고 검사한다(약 16분, 임시 디스크 0.7 GB).

```bash
python3 verify_dfs.py
```

는 DFS를 컴파일하고 두 모드에서 $n\le9$를 다시 실행하며, 나열된 general
모드 표를 Python으로 다시 검사한다(CI, 몇 초). $n=10,11$의 실행은

```bash
g++ -O2 -std=c++17 search/dfs677.cpp -o build/dfs677
build/dfs677 10 sel 2
build/dfs677 11 sel 2 split 300 P depth 7
```

이며 $P=0,\dots,299$에 대해 실행하고, 부분 1은 $Q=0,\dots,39$에 대해
`split 300 1 depth 7 split2 40 Q depth2 12`로 다시 나눈다. 평행이동 불변
탐색(CaDiCaL과 GAP용 Python 패키지 `passagemath-gap` 필요)은

```bash
python3 tinv/export_groups.py 1 29 > groups.txt
python3 tinv/export_cases.py groups.txt 1 29 > cases.txt
echo 2 > workers
python3 tinv/run_cases.py groups.txt cases.txt 600 tinv.log workers
```

이다(경우마다 600초 제한. 제한에 걸린 경우는 로그에 `UNKNOWN`으로 남고,
별도의 경우 파일과 로그로 3600초 제한을 두어 다시 실행했다). 또한
`python3 tinv/test_sb.py groups.txt general_cases.txt 1 19`
(`general_cases.txt`는 `export_cases.py ... general`로 생성)이 대칭 깨기를
검증한다.

## Lean 선언

모두 이름공간 `AgenticConjectures.Etp677Implies255Finite`에 있다.

| 선언 | 내용 |
|---|---|
| `Magma`, `◇`, `Equation255`, `Equation677` | upstream 정의를 항 하나하나 그대로 옮긴 것 |
| `statement` | 미해결 upstream 정리 `Finite.Equation677_implies_Equation255`를 `Prop`으로 옮긴 것(증명하지 **않음**) |
| `noCountermodelUpTo`, `statement_iff_forall_noCountermodelUpTo` | 탐색이 인증하는 유한 버전 명제. `statement`는 모든 상한에서 이것이 성립하는 것과 동치 |
| `leftMul_bijective`, `inv_form`, `inv_form₂`, `backward_recurrence` | 유한 E677 마그마에서 모든 왼쪽 곱은 전단사이고, 전파에 쓰는 E677의 역형태 |
| `fixer_unique`, `eq255_at_iff_exists_fixer`, `fixer_free_of_not255`, `ne_of_not255_v`, `ne_of_not255_vii` | $x$에서 E255가 성립하는 것은 $x$의 (유일한) 고정자가 있는 것과 동치이며, E255가 실패하는 점에서 성립하는 부등식들 |
| `exists_generated_countermodel`, `not_statement_iff` | 반례 모델이 있으면 E255가 실패하는 한 원소로 생성되는 반례 모델도 있다(동치) |
| `tinv_translate`, `tinv_eq677_iff`, `tinv_fixer_iff`, `tinv_eq255_iff` | $x\diamond y=x\,f(x^{-1}y)$에서 E677은 $f$에 대한 함수 방정식 하나이고, E255는 $f$에 고정점이 있는 것과 동치 |
| `not_statement_of_tinv` | 유한군 위의 고정점 없는 해 $f$는 `statement`를 반박한다 |
| `tinv_cnf_constraints`, `tinv_conj_solution`, `tinv_conj_fixed_iff` | 군 CNF의 추가 절과 자기동형 대칭 깨기의 건전성 |

## 진술의 충실성

`Magma`, `◇`, `Equation255`, `Equation677`은 upstream 파일에서 항 하나하나
그대로 복사했고, `statement`는 `Finite.Equation677_implies_Equation255`의
명제와 정확히 같다(같은 `Type` 유니버스, `Finite` 가정, 같은 한정사 순서).
인덱스나 뺄셈 때문에 달라질 부분은 없다. `noCountermodelUpTo N`은 탐색이
인증하는 유한 버전이다. 상한은 Lean이 아니라 DRAT와 탐색 결과에 근거하므로
이것은 정의일 뿐이다.

## 파일

- [`search/gen_cnf.py`](search/gen_cnf.py), [`search/enum_sat.py`](search/enum_sat.py):
  CNF 생성기와 모델 나열기(SAT 방법).
- [`search/dfs677.cpp`](search/dfs677.cpp): 전수 DFS(두 번째 방법).
- [`certificates/`](certificates/): $n\le8$의 DRAT 증명과, $n\le10$의 모든
  CNF 및 커밋된 증명의 SHA-256.
- [`verify_drat.py`](verify_drat.py), [`verify_dfs.py`](verify_dfs.py): CI
  검사.
- [`tinv/`](tinv/): 평행이동 불변 탐색(군 내보내기, 경우 분할, CNF, 실행기,
  전수 모델 검사기, 대칭 깨기 테스트).
- [`results/`](results/): general 모드 표, DFS와 SAT 실행 기록, 평행이동
  불변 결과.
- [`upstream/`](upstream/README.md): FormalConjectures 스냅샷.
