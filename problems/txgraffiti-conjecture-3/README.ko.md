[English](README.md) | **한국어**

# TxGraffiti 추측 3: 정칙 그래프의 독립 지배수와 포화수

## 명제

출처: R. Davila, B. Brimkov, R. Pepper, *In Reverie Together: Ten Years of Mathematical
Discovery with a Machine Collaborator*, [arXiv:2507.17780](https://arxiv.org/abs/2507.17780),
추측 3. 논문은 `r > 0`인 모든 `r`-정칙 그래프 `G`에 대해
"i(G) ≤ µ∗(G), and this bound is sharp"라고 추측한다.

여기서 `i(G)`는 독립 지배수(극대 독립 집합의 최소 크기)이고, `µ*(G)`는 포화수(극대 매칭의
최소 크기)로서 변 지배수 `γ_e(G)`와 같다. Formal Conjectures는 이 부등식을
`Arxiv.«2507.17780».tx_graffiti_conjecture_3`로 진술한다([상류 스냅샷](upstream/README.md)).

## 결과

**주장하는 상태: 반증됨(refuted).** 상류 명제는 거짓이고, 차수를 `r ≥ 4`로 제한한 명제도
거짓이다.

1. **3-정칙 반례는 우리가 찾은 것이 아니다.** `G48`은 공개 저장소
   [ipitchford/txgraffiti-order48-successor](https://github.com/ipitchford/txgraffiti-order48-successor)에
   있는 정점 48개짜리 3-정칙 그래프 `counterexample.g6`이며, 정점 번호도 같다
   (`python3 certificates/g48_cnf.py --same-as FILE`이 graph6 파일과 Lean 그래프를 비교한다).
   이 그래프는 `i = 16 > 15 = µ*`이다. 이보다 앞서거나 관련된 공개 반례는
   [선행 연구](#선행-연구와-범위)에 정리했다.
2. **3의 배수인 모든 차수에서 추측이 거짓이다.** 그래프 `G`의 각 정점을 서로 인접하지 않은
   쌍둥이 정점 `t`개로 바꾼다(사전식 곱 `G[K̄_t]`). `G`가 `r`-정칙이면 `G[K̄_t]`는
   `tr`-정칙이고 `i(G[K̄_t]) = t·i(G)`, `µ*(G[K̄_t]) ≤ t·µ*(G)`이다. 따라서 `G48[K̄_t]`는
   정점이 `48t`개인 `3t`-정칙 그래프이고 `i = 16t > 15t ≥ µ*`이다. `t = 2`이면 정점 96개인
   6-정칙 반례가 되어, `r ≥ 4`로 제한한 명제도 반증된다. 우리가 확인한 자료에서는 이 블로업
   관찰을 찾지 못했다. 새로움을 주장하는 것은 아니다.
3. **나머지 차수는 여전히 미해결이다.** 4와 5를 포함해 3의 배수가 아닌 모든 차수 `r ≥ 4`에서
   추측은 열려 있다. 정점이 17개 이하인 연결 4-정칙 그래프와 정점이 14개 이하인 연결 5-정칙
   그래프 가운데 반례는 없고, 구조를 갖춘 여러 그래프 족에서도 반례가 나오지 않았다
   ([탐색](#탐색)). 이 부분은 컴퓨터 보조 결과이며 형식화되지 않았다.
4. **손으로 한 논증이며 기계 검증은 거치지 않았다.** [DETAILS.ko.md](DETAILS.ko.md)에 몇 가지
   부류에 대한 결과를 적었다.
   - `r ≥ 7`이면 효율적 변 지배 집합을 가진 모든 `r`-정칙 그래프가 `i ≤ µ*`를 만족한다.
     Gupta의 비대칭(lopsided) 국소 보조정리 논증(arXiv:2608.22498, 정리 1)의 직접적인
     따름정리이다. 특히 Iwane의 문제 17은 `k ≥ 7`에서 답이 부정적이다.
   - 결손도(deficiency)가 1인 극소 비충족 `k`-CNF 가운데 모든 리터럴이 `k − 1`번 이하로
     나타나는 것은 없다.

## 무엇을 무엇으로 검사했는가

| 주장 | 검사 수단 |
|---|---|
| `G48`은 3-정칙이다; `µ*(G48) = 15`; `D48`은 크기 16인 독립 지배 집합이다 | Lean (`decide`, 커널) |
| 최대 차수가 `r` 이하인 모든 그래프에서 `\|E\| ≤ (2r − 1)·µ*(G)` | Lean |
| 블로업 보조정리: 차수, `i(G[K̄_t]) = t·i(G)`, `µ*(G[K̄_t]) ≤ t·µ*(G)` | Lean |
| `G48LowerBound`(`G48`에는 정점 15개 이하의 독립 지배 집합이 없다) ⇒ 3으로 나누어떨어지는 모든 `r`에서 추측이 거짓이고, 특히 `¬ statement`와 `¬ statementGeFour` | Lean |
| `G48LowerBound` 자체 | CI의 `drat-trim`이 검사하는 DRAT 증명. 대상 CNF는 CI가 Lean 소스에서 다시 만들고 해시를 확인한다 |
| 그 CNF가 `G48LowerBound`를 인코딩한다는 것 | 손으로 한 논증: [g48_cnf.py](certificates/g48_cnf.py)와 [DETAILS.ko.md](DETAILS.ko.md)의 건전성 논증. `--check`는 `D48`에 대해 건전성 구성을 직접 실행하기도 한다 |
| SAT와 무관하게 `i(G48) = 16`, `µ*(G48) = 15` | C 분기 한정법 [search/tx3check.c](search/tx3check.c), CI에서 실행 |
| 차수 4, 5, 6에 대한 탐색 | C 분기 한정법과 nauty `geng`, 로컬에서만 실행 |
| `r ≥ 7` 부류 결과와 MU(1)에 관한 언급 | 손으로 한 논증뿐 |

반증은 Lean 밖의 사실 하나, `G48LowerBound`만 쓴다. Lean은 이것을 가설로 받고, CI는 그 DRAT
인증서를 검사한다. 독립적인 C 검사는 같은 사실을 또 다른 구현으로 확인한다.

### Lean 정리

모듈 `AgenticConjectures.TxGraffitiConjecture3`. 모듈 독스트링에 상류 정의와의 대응을 적었다.

- `statement`: 상류 정리의 전칭 폐포. `statementGeFour`는 `1 ≤ r`를 `4 ≤ r`로 바꾸고,
  `statementDeg r`는 차수를 고정한다.
- `card_edgeFinset_le_mul_saturationNumber`: 모든 차수가 `r` 이하이면 `|E| ≤ (2r − 1)·µ*`.
- `degree_blowup`, `indepDominationNumber_blowup`, `saturationNumber_blowup_le`: 블로업
  보조정리.
- `G48_degree`, `card_edgeFinset_G48`, `isMaximalEdgeMatching_M48`, `saturationNumber_G48`,
  `isNIndepDominatingSet_D48`.
- `indepDominationNumber_G48 (h : G48LowerBound) : indepDominationNumber G48 = 16`.
- `not_statementDeg (h : G48LowerBound) (hr : 3 ∣ r) (hr0 : 0 < r) : ¬ statementDeg r`.
- `not_statement (h : G48LowerBound) : ¬ statement`와
  `not_statementGeFour (h : G48LowerBound) : ¬ statementGeFour`.

`sorry`, 추가 공리, `native_decide`는 쓰지 않았다. `#print axioms`에는 `propext`,
`Classical.choice`, `Quot.sound`만 나온다.

### 인증서

[certificates/g48_cnf.py](certificates/g48_cnf.py)는 Lean 모듈에서 이웃 목록 `nbrs48`을 읽어,
`G48`에 정점 15개 이하의 독립 지배 집합이 있을 때 그리고 그때에만 충족 가능한 CNF를 만든다.
CNF는 다음 부분으로 이루어진다.

- 정점마다 지배 절 하나;
- 변마다 독립 절 하나;
- 고른 정점의 수를 15 이하로 묶는 토탈라이저(totalizer). 크기를 줄이려고, 매칭
  `{0,1}, …, {28,29}`가 덮는 정점 30개는 쌍 지시 변수 15개를 거쳐 들어간다. 각 쌍이 변이므로
  이렇게 해도 건전하다.

스크립트 독스트링에 변수, 절의 순서, 건전성 논증을 적었다. 그 결과인
[g48_ids_le15.cnf](certificates/g48_ids_le15.cnf)는 변수 212개와 절 692개로 이루어지며,
sha256은 `f916d6b4…bbbf2`이다.

증명 [g48_ids_le15.drat](certificates/g48_ids_le15.drat)의 크기는 1.0 MB이다. CaDiCaL 3.0.1이
텍스트 DRAT 형식으로 만들었고, `drat-trim -l`을 두 번 거쳐 줄였다. `drat-trim`은 약 0.1초 만에
이를 검증하며, 절 692개 가운데 534개가 코어에 들어간다. `cadical --no-binary`를 새로 실행하면
다른 증명(1.8 MB)이 나오고 그것도 검증된다. 증명이 바이트 단위로 같을 필요는 없다.

## 탐색

모든 탐색은 정확한 풀이기 [search/tx3check.c](search/tx3check.c)를 쓴다.

- **검사기.** graph6 그래프마다 분기 한정법으로 `i`를 계산한다. `µ*`는
  `i ≥ ⌈|E|/(2r − 1)⌉`일 때만 정확히 계산한다. 그렇지 않으면 하한에서 곧바로 `i < µ*`가
  나오기 때문이다.
- **교차 검사.** `r = 3, …, 6`이고 `6 ≤ n ≤ 12`인 연결 `r`-정칙 그래프 18,058개 모두에서
  [search/tx3lib.py](search/tx3lib.py)의 pysat 풀이기와 결과가 일치한다. 무작위 정칙 그래프
  2,000개에 대해서는 [search/crosscheck.py](search/crosscheck.py)가 `i`를 pysat, CP-SAT, 극대
  독립 집합 열거로 비교하고, `µ*`를 pysat, CP-SAT, (작은 그래프에서는) 전수 대입으로 비교한다.
- **생성.** 그래프는 nauty `geng -c -dR -DR`로 만든다. 개수는 OEIS A006820(4-정칙),
  A006821(5-정칙), A006822(6-정칙)와 일치한다.

| 그래프 족 | 범위 | 그래프 수 | 반례 |
|---|---|---|---|
| 연결 4-정칙 | `n ≤ 16` | 8,943,749 | 0 |
| 연결 4-정칙 | `n = 17` | 86,221,634 | 0 |
| 연결 5-정칙 | `n ≤ 14` | 3,467,295 | 0 |
| 연결 6-정칙 | `n ≤ 14` | 21,985,302 | 0 |
| 연결 3-정칙 그래프 `G`의 선 그래프, 프리즘 `G□K_2`, 곱 `G□K_3` | `\|G\| ≤ 20` | 각각 556,471 | 0 |
| 차수 4, 5, 6의 가중 블로업 `B[t]` (3-정칙 또는 4-정칙 바탕 그래프 `B`의 정점 `v`를 쌍둥이 `t(v)`개로 바꿈) | `\|B\| ≤ 18`, 정점 62개 이하 | 104,109 | 0 |

곱 `G48□K_2`(4-정칙, 정점 96개)와 `G48□K_3`(5-정칙, 정점 144개)에는 하한 `⌈|E|/(2r − 1)⌉`
(각각 28과 40)보다 크지 않은 독립 지배 집합이 있으므로, 둘 다 `i ≤ µ*`를 만족한다.

효율적 변 지배 집합을 가진 4-정칙 반례가 있다면, 모든 리터럴이 정확히 3번씩 나타나는 충족
불가능한 4-CNF가 생긴다([DETAILS.ko.md](DETAILS.ko.md) 5절). 이런 식에 대한 담금질 기법
(simulated annealing, [search/sa_balanced_cnf.c](search/sa_balanced_cnf.c))은 모든 리터럴이
정확히 두 번씩 나타나고 변수 15개, 절 20개로 이루어진 충족 불가능한 3-CNF를 20초 안에
찾는다. 그러나 `k = 4`이고 변수가 20개 이하일 때는, 도달한 충족 할당 수의 최솟값이 수백
이상에 머문다.

실행별 개수와 시간, 정확한 명령은 [search/search_summary.txt](search/search_summary.txt)에
있다. `sh search/reproduce.sh`는 탐색을 다시 실행한다. `n = 17` 단계는 따로 요청할 때만
실행된다.

## 재현

문제 디렉터리에서 실행한다.

```bash
python3 certificates/g48_cnf.py --check                                    # 1초 미만, 표준 라이브러리만 사용
drat-trim certificates/g48_ids_le15.cnf certificates/g48_ids_le15.drat     # 약 0.1초
cc -O2 -o /tmp/txgraffiti3_tx3check search/tx3check.c && python3 certificates/g48_cnf.py --g6 | /tmp/txgraffiti3_tx3check   # COUNTEREXAMPLE i=16 mu*=15 출력
(cd ../.. && lake env lean problems/txgraffiti-conjecture-3/upstream_statement_check.lean)  # lake build 뒤에 실행, 표준 공리 3개 출력
sh search/reproduce.sh              # 기본 단계: 코어 하나로 약 2.5시간
sh search/reproduce.sh quartic17    # n = 17: JOBS=3 병렬 조각으로 약 2 CPU시간
```

`reproduce.sh`에는 `cc`, nauty의 `geng`, 그리고 networkx, python-sat, ortools가 설치된
`python3`가 필요하다(`PY`로 지정한다). Lean 모듈은 저장소 루트에서 `lake build`로 빌드한다.

## 명제의 충실성

- `statement`는 상류 정리의 전칭 폐포이다. 바인더 `V : Type`, `[Fintype V] [DecidableEq V]`,
  `[DecidableRel G.Adj]`를 갖춘 `G`, `r : ℕ`가 같고, 가설 `∀ v, G.degree v = r`와 `1 ≤ r`,
  결론도 같다. 보조 정의는 formal-conjectures c094b97에서 항 하나하나 그대로 옮겼다.
  이름공간이나 `IsNIndepDominatingSet`의 명시적 `G` 인자 같은 표면적인 수정은 모듈
  독스트링에 적었다.
- 두 불변량은 모두 `ℕ` 위의 하한(infimum)이고 `sInf ∅ = 0`이다. Lean은 모든 유한 그래프에서
  해당 집합이 공집합이 아님을 증명하므로, 이 관례는 아무 역할도 하지 않는다.
- 논문의 최선성 주장("and this bound is sharp")은 상류의 형식 명제에 들어 있지 않으며,
  우리도 다루지 않는다. 반증은 부등식에 관한 것이다.
- 논문은 `r > 0`인 `r`-정칙 그래프를 대상으로 하며, 이는 `1 ≤ r`와 일치한다. 반례들은
  유한하고 단순하며 연결되어 있다.
- `statementGeFour`는 차수를 `r ≥ 4`로 제한한 우리 명제로, 3-정칙 반례가 공개된 뒤에도 열려
  있던 부분이다. 상류 선언이 아니다.
- **기계적 검사.** [`upstream_statement_check.lean`](upstream_statement_check.lean)은 상류 정의
  여섯 개를 상류 이름공간 `SimpleGraph`에 그대로 다시 선언한다. 이어서
  `Arxiv.«2507.17780».tx_graffiti_conjecture_3`의 바인더와 결론을 상류 이름공간에서 부정 아래에
  다시 진술하고, `G48LowerBound`를 전제로 우리의 `not_statement`에서 그 부정을 이끌어 낸다
  (`4 ≤ r` 판은 `not_statementGeFour`에서). 두 다리 보조정리가 상류 상수를 우리 상수로 펼쳐야
  하므로, 정의나 바인더에 어긋남이 있으면 이 파일이 실패한다. 출력은 표준 공리 세 개이다. 이
  파일은 라이브러리에서 import하지 않으므로 CI는 이것을 실행하지 않는다.

## 선행 연구와 범위

- **3-정칙 반례는 이 작업 이전에 이미 공개되어 있었다.**
  - 우리가 찾은 가장 이른 공개 반례인 `n = 50`: 저장소
    [djma/TxGraffiti-conjecture3-counterexample](https://github.com/djma/TxGraffiti-conjecture3-counterexample)
    (커밋 `7810f30`, 2026-07-23). 이 저장소에는 `i ≥ 16`에 대한 CNF와 LRAT 증명이 이미 들어 있다.
    Zenodo 릴리스 [10.5281/zenodo.21852504](https://doi.org/10.5281/zenodo.21852504)
    (2026-08-08)는 이 저장소에서 파생되었다. K. Afrasyab,
    [arXiv:2609.10783](https://arxiv.org/abs/2609.10783)은 같은 그래프가 `γ = 16 > 15 = γ_e`까지
    만족함을 보인다. 그 논문 2절은 변수 15개, 절 20개인 식에서 이 그래프를 만들며,
    `search/check_blowup.py`가 이를 다시 만든다.
  - 정점 50개와 60개인 3-정칙 반례 113개: H. Iwane, GitHub 저장소
    `HirotadaIwane/independent-domination-counterexample`(첫 릴리스 2026-07-27). 논문 Zenodo
    [10.5281/zenodo.22924244](https://doi.org/10.5281/zenodo.22924244)(2026-09-23)는 `k`-정칙
    그래프에 대한 절–리터럴 대응과 `k ≥ 4`에 관한 미해결 문제 17을 더한다.
  - `n = 48`: 위 저장소
    [ipitchford/txgraffiti-order48-successor](https://github.com/ipitchford/txgraffiti-order48-successor)의
    익명 릴리스(2026-08-24). 이 릴리스에는 `i ≥ 16`에 대한 전수 증명 트리 인증서와 그 Python
    검사기가 이미 들어 있다. Zenodo 기록은
    [10.5281/zenodo.22083656](https://doi.org/10.5281/zenodo.22083656)이다.
  - Formal Conjectures 이슈
    [#6737](https://github.com/google-deepmind/formal-conjectures/issues/6737)(열림, 2026-09-30)은
    추측이 거짓이라고 보고한다.
- **이전 탐색과 증명된 부류.** 저장소
  [takumayellow/math-autoresearch](https://github.com/takumayellow/math-autoresearch)(2026-07-26)는
  `r = 3, n ≤ 18`, `r = 4, n ≤ 14`, `r = 5, n ≤ 12`, `r = 6, n ≤ 11`, `r = 7, n ≤ 10`인 연결
  `r`-정칙 그래프를 모두 검사했고 반례를 찾지 못했다. H. Achour, *The Clique-Fiber Principle*
  ([10.5281/zenodo.21819055](https://doi.org/10.5281/zenodo.21819055), 2026-08-06)은 `m ≥ 3`이고
  `m > Δ(H)`인 데카르트 곱 `H□K_m`에서 `i ≤ µ*`를 증명한다. 이 부류에는 위에서 탐색한 3-정칙
  그래프의 프리즘 `G□K_2`도, 곱 `G□K_3`도 들어 있지 않다.
- **지배수 대 변 지배수.** C. Gupta, [arXiv:2608.22498](https://arxiv.org/abs/2608.22498)은
  최소 극대 매칭의 무작위 횡단(transversal)과 비대칭 국소 보조정리를 써서, 차수 7 이상인
  정칙 그래프에서 `γ ≤ γ_e`를 증명한다. 그 논문의 Remark 1은 이 논증이 일반적으로
  `i ≤ γ_e`를 주지 못하는 이유를 설명하며, 우리의 `r ≥ 7` 부류 결과는 같은 논증을 그대로
  적용한 것이다. 이 논문은 또 `3 ≤ Δ ≤ 6`일 때 둘레(girth)가 충분히 큰 `Δ`-정칙 그래프에서
  `i ≤ γ_e`를 이끌어 내고, 8절에서 `Δ ∈ {4, 5, 6}`에 대해 충족 불가능한
  `(Δ, Δ − 1, Δ − 1)`-식이 존재하는지 묻는다.
- **출현 횟수가 제한된 SAT.** T. Zhang, T. Peitl, S. Szeider,
  [arXiv:2405.16149](https://arxiv.org/abs/2405.16149)(SAT 2024)는 가장 작은 충족 불가능한
  `(3, p, q)`-식을 결정한다. `k = 3`일 때 우리의 MU(1) 언급은 그들의 표 6에서
  `p = q = 2`인 `∞` 항목에 해당한다.
- **우리가 확인한 자료에서 찾지 못한 것:** 블로업 관찰과, 6을 포함해 3의 배수인 차수의 반례,
  반증의 Lean 형식화, `G48`에 대한 DRAT 인증서(`G48` 릴리스에는 증명 트리 인증서가, djma
  저장소에는 정점 50개 그래프에 대한 LRAT 인증서가 있다), 위 크기에서의 차수 4–6 탐색. 외부
  검토 전에는 새로움을 주장하지 않는다.

이 결과는 아직 사람이 검토하지 않았다. AI 모델이 만들었으며, Lean 커널, `drat-trim`, 수치 교차
검사로만 확인했다. Formal Conjectures를 비롯해 어디에도 제출하지 않았으며, 외부 제출에는 사람의
승인이 필요하다.

## 파일

- `certificates/g48_cnf.py`: Lean 소스에서 CNF를 다시 만들고 감사한다(`--check`). `G48`을
  graph6로 출력하고(`--g6`), graph6 파일과 비교하기도 한다(`--same-as`).
- `certificates/g48_ids_le15.cnf`, `certificates/g48_ids_le15.drat`: CNF와 그 DRAT 증명.
- `search/`: `tx3check.c`(정확한 `i`와 `µ*`), `transform.c`(선 그래프와 곱), `wblow.c`(가중
  블로업), `sa_balanced_cnf.c`(균형 CNF에 대한 담금질), `tx3lib.py`와 `crosscheck.py`,
  `xcheck_c.py`, `check_blowup.py`, `prod_check.py`(SAT와 CP-SAT 교차 검사), `reproduce.sh`,
  `search_summary.txt`.
- `upstream/`: Formal Conjectures 스냅샷.
- `upstream_statement_check.lean`: 명제 충실성의 기계적 검사(라이브러리에서 import하지 않는다).
- [DETAILS.ko.md](DETAILS.ko.md): 증명과 유도.
