[English](README.md) | **한국어**

# WOWII 그래프 추측 72

## 추측

E. DeLaViña의 *Written on the Wall II*(Graffiti.pc 프로그램이 만든 추측
목록)에 실린 추측 72는 2004년 4월 4일 날짜로 상태 `O`(미해결)로 올라
있습니다. 원문 행은 다음과 같습니다.

> If G is a simple connected graph, then tree(G) ≥ CEIL[average of ecc(v) + maximum of λ(v) /3]

위 문장은 목록의
[2026-07-26 Wayback 캡처](https://web.archive.org/web/20260726061534/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/all.html)에
나온 그대로입니다. HTML 원문은 λ를 Symbol 글꼴의 `l`로 씁니다. 이 행이
연결한 정의(목록의 `wowIIdefs.js`,
[2023-09-01 캡처](https://web.archive.org/web/20230901203307/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/wowIIdefs.js)의
48, 21, 4, 16번 항목)는 다음과 같습니다.

- \(\operatorname{tree}(G)\)는 \(G\)의 가장 큰 유도 트리의 꼭짓점 개수입니다.
- \(\operatorname{ecc}(v)\)는 \(v\)의 이심률, 즉 \(v\)에서 \(G\)의
  꼭짓점까지의 거리 중 가장 큰 값입니다.
- \(\lambda(v)\)는 \(v\)의 이웃들이 유도하는 부분그래프의 독립수입니다.
- \(\operatorname{CEIL}[x]\)는 \(x\) 이상인 가장 작은 정수입니다.

평균과 최댓값은 모든 꼭짓점에 대해 취합니다.
\(A=\frac1n\sum_v\operatorname{ecc}(v)\), \(L=\max_v\lambda(v)\)로
씁니다.

### 두 가지 읽기

원문 행은 `/3`이 무엇을 나누는지 밝히지 않습니다.

- **Formal Conjectures의 읽기.** google-deepmind/formal-conjectures의 형식
  명제는 \(L\)만 3으로 나눕니다.
  \[
  \operatorname{tree}(G)\ \ge\ \bigl\lceil A+L/3\bigr\rceil .
  \]
  **이 읽기는 거짓입니다.** 이는 2026-07-23에 이미 공개적으로 언급되었으며
  ([선행 연구와 상태](#선행-연구와-상태) 참고), 이 디렉터리는 Lean 반박을
  더합니다.
- **고르게 나누는 읽기.** \(\operatorname{tree}(G)\ge\lceil(A+L)/3\rceil\).
  이 읽기는 참이며, 2026-07-23의 공개 게시물에 짧은 논증이 있습니다
  ([선행 연구와 상태](#선행-연구와-상태) 참고). 거리가 최대 \(D\)인 두
  꼭짓점 사이의 최단 경로는 유도 경로이므로
  \(\operatorname{tree}(G)\ge D+1\ge A+1\)입니다. 한 꼭짓점과 그 이웃 중
  가장 큰 독립집합은 별을 유도하므로 \(\operatorname{tree}(G)\ge L+1\)입니다.
  따라서 \(A+L\le2\operatorname{tree}(G)-2\)입니다. 이 저장소는 이 논증을
  형식화하지 않았습니다.

Graffiti.pc나 목록 작성자가 어느 읽기를 의도했는지는 여기서 판단하지
않습니다.

## 결과

**정리.** Formal Conjectures의 명제
`WrittenOnTheWallII.GraphConjecture72.conjecture72`(커밋 `c094b97`)는
거짓입니다. 꼭짓점이 28개인 연결 그래프 \(G\)로서
\(\operatorname{tree}(G)=7\), \(A=75/14\), \(L=5\)인 것이 있으며,
\[
\bigl\lceil A+L/3\bigr\rceil=\bigl\lceil 295/42\bigr\rceil=8>7=\operatorname{tree}(G)
\]
입니다.

이 명제가 거짓이라는 사실은 새롭지 않습니다
([선행 연구와 상태](#선행-연구와-상태) 참고). 이 반박은 아직 사람이 검토하지
않았습니다.

그래프 \(G\)([`g28.txt`](g28.txt))는 다음 부분으로 이루어집니다.

- \(q_1,\dots,q_{10},p_0\) 위의 완전그래프 \(K_{11}\),
- 변 \(p_0p_1\),
- 서로 인접하지 않으며 각각 \(p_1\), \(p_3\)과 인접한 네 꼭짓점
  \(m_1,\dots,m_4\),
- 변 \(p_3p_4\),
- \(p_4,r_1,\dots,r_{10}\) 위의 완전그래프 \(K_{11}\).

변은 120개입니다. `g28.txt`와 Lean 파일의 번호로는
\(p_0,p_1,m_1,\dots,m_4,p_3,p_4\)가 꼭짓점 \(0,\dots,7\)이고, \(q_i\)는
\(8,\dots,17\), \(r_i\)는 \(18,\dots,27\)입니다.

| 꼭짓점 | \(q_i\), \(r_i\) | \(p_0\), \(p_4\) | \(p_1\), \(p_3\) | \(m_i\) |
| --- | ---: | ---: | ---: | ---: |
| 개수 | 20 | 2 | 2 | 4 |
| \(\operatorname{ecc}(v)\) | 6 | 5 | 4 | 3 |
| \(\lambda(v)\) | 1 | 2 | 5 | 2 |

따라서 \(\sum_v\operatorname{ecc}(v)=120+10+8+12=150\)이고
\(A=150/28=75/14\)입니다. 최댓값 \(L=5\)는 이웃 \(p_0,m_1,\dots,m_4\)가
서로 인접하지 않는 \(p_1\)에서, 그리고 \(p_3\)에서 얻어집니다. 집합
\(\{q_1,p_0,p_1,m_1,\dots,m_4\}\)는 꼭짓점 7개짜리 트리를 유도하고,
꼭짓점 8개로는 트리를 유도할 수 없습니다. 고르게 나누는 읽기는 \(G\)에서
성립합니다. \(\lceil(A+L)/3\rceil=\lceil145/42\rceil=4\le7\)입니다.

## 증명 아이디어

각 꼭짓점에 층을 붙입니다. \(q_i\)는 0, \(p_0\)은 1, \(p_1\)은 2,
\(m_i\)는 3, \(p_3\)은 4, \(p_4\)는 5, \(r_i\)는 6입니다. 서로 다른 두
꼭짓점은 층의 차이가 1이거나, 두 층이 모두 0이거나, 모두 6일 때 정확히
인접합니다.

1. **평균 이심률.** 변을 따라가면 층이 많아야 1 바뀌므로, 두 꼭짓점 사이의
   거리는 층의 차이 이상입니다. 따라서 층이 \(\ell\)인 꼭짓점은 \(q_1\)
   또는 \(r_1\)까지의 거리가 \(\max(\ell,6-\ell)\) 이상입니다. 이 하계들의
   합이 150이므로 \(A\ge75/14\)입니다.
2. **국소 독립수.** \(p_1\)의 다섯 이웃은 서로 인접하지 않으므로
   \(L\ge\lambda(p_1)\ge5\)입니다.
3. **유도 트리.** \(T\)가 트리를 유도한다고 합시다.
   - 완전그래프의 세 꼭짓점은 삼각형을 이루므로, \(T\)는 각 \(K_{11}\)의
     꼭짓점을 많아야 두 개 포함합니다.
   - \(p_1,p_3\in T\)이면 \(m_i\) 두 개가 4-사이클 \(p_1m_ip_3m_j\)를
     닫으므로 \(T\)에는 \(m_i\)가 많아야 하나 있습니다. 그러면 꼭짓점은
     많아야 \(2+1+1+1+2=7\)개입니다.
   - \(p_1\in T\)이고 \(p_3\notin T\)이면 \(T\) 안의 어떤 경로도 3층에서
     5층으로 넘어갈 수 없습니다. \(T\)는 연결되어 있으므로 두 번째
     완전그래프와 만나지 않고, \(|T|\le2+1+4=7\)입니다. \(p_3\in T\),
     \(p_1\notin T\)인 경우도 대칭입니다.
   - \(p_1,p_3\notin T\)이면 모든 \(m_i\)는 \(T\)에서 고립됩니다. 따라서
     \(T=\{m_i\}\)이거나, \(T\)가 두 완전그래프 안에 있어 \(|T|\le4\)입니다.

   그러므로 \(\operatorname{tree}(G)\le7\)이고,
   \(\operatorname{tree}(G)\le7<8\le\lceil75/14+5/3\rceil\le\lceil A+L/3\rceil\)
   입니다.

[DETAILS.ko.md](DETAILS.ko.md)는 각 단계와 그것을 증명하는 Lean 보조정리를
함께 제시합니다.

## Lean 형식 증명

[`AgenticConjectures/WowiiGraphConjecture72.lean`](../../AgenticConjectures/WowiiGraphConjecture72.lean)이
upstream 명제를 반박합니다. `sorry`, 추가 공리, `native_decide`를 쓰지
않습니다. 28개 층에 관한 작은 사실들은 커널에서 `decide`로 확인합니다.
`#print axioms`는 `propext`, `Classical.choice`, `Quot.sound`만 보여 줍니다.

| 선언 | 내용 |
| --- | --- |
| `statement`, `refuted` | 모든 꼭짓점 타입 `α : Type u`에 대한 upstream 명제와, 모든 universe에서의 그 부정. |
| `graph`, `graph_connected` | `V ≃ Fin 28`인 임의의 타입 위의 반례와 그 연결성. |
| `averageEccentricity_ge` | `ecc_ge`와 `sum_lvl`에서 얻는 \(A\ge150/28\). |
| `five_le_indepNeighborsCard` | \(\lambda(p_1)\ge5\). |
| `card_le_seven`, `largestInducedTreeSize_le` | 모든 유도 트리의 꼭짓점은 많아야 7개이므로 \(\operatorname{tree}(G)\le7\). |
| `tree_lt_ceil` | 반례에서 \(\operatorname{tree}(G)<\lceil A+L/3\rceil\). |
| `not_isAcyclic_of_triangle`, `not_isAcyclic_of_square`, `of_preserved` | 삼각형이나 4-사이클을 포함하는 유도 부분그래프는 비순환이 아니며, 연결된 유도 부분그래프의 변을 따라 전해지는 성질은 그 전체에서 성립함. |
| `card_le_indepNeighborsCard` | \(u\)의 이웃으로 이루어진 독립집합이 \(\lambda(u)\)의 하계를 줌. |

## 명제 충실성

반박하는 선언을
[`upstream/GraphConjecture72.lean`](upstream/GraphConjecture72.lean)의 40행과
52–56행에서 그대로 옮기면 다음과 같습니다.

```lean
variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

@[category research open, AMS 5]
theorem conjecture72 (G : SimpleGraph α) (h : G.Connected) :
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    ⌈averageEccentricity G + (maxL : ℝ) / 3⌉ ≤ (largestInducedTreeSize G : ℝ) := by
  sorry
```

- **정의.** `averageEccentricity`, `largestInducedTreeSize`,
  `indepNeighborsCard`는 커밋 `c094b97`의 FormalConjecturesForMathlib에서
  항 그대로 옮겼습니다. 원래 위치는
  `Combinatorics/SimpleGraph/Eccentricity.lean`의 34행,
  `Combinatorics/SimpleGraph/LargestInducedTree.lean`의 39행,
  `Combinatorics/SimpleGraph/Independence.lean`의 40행이며, 같은 섹션
  변수를 씁니다. 이름공간만 다릅니다. 여기서는 `SimpleGraph`가 아니라
  `AgenticConjectures.WowiiGraphConjecture72`에 있습니다.
- **원래 정의와의 대응.** `averageEccentricity G`는
  `(G.eccent v).toNat`의 \(\frac1n\sum_v\)입니다. 유한 연결 그래프에서
  `G.eccent v`는 유한하고 \(\operatorname{ecc}(v)\)와 같으므로 이 값은
  \(A\)입니다. `largestInducedTreeSize G`는 트리를 유도하는 꼭짓점 집합의
  크기들의 상한이며, 그 크기들의 집합이 유한하므로
  \(\operatorname{tree}(G)\)와 같습니다. `indepNeighborsCard G v`는 열린
  이웃이 유도하는 부분그래프의 독립수, 즉 \(\lambda(v)\)입니다.
- **명제.** `statement`는 upstream 정리의 가정과 결론을 그대로 옮겨(꼭짓점
  타입은 명시적으로 묶고 가정 `h`에는 이름을 붙이지 않음) 모든 꼭짓점 타입
  `α : Type u`에 대해 양화한 것입니다. 올림은 `Int.ceil`이고,
  3으로 나누는 것은 \(L\)만의 실수 나눗셈이며, 양변은 \(\mathbb R\)에서
  비교합니다. 자연수 뺄셈은 나오지 않습니다. `FormalConjecturesUtil` 대신
  `import Mathlib`를 쓰고, `@[category research open, AMS 5]` 속성과
  `module`/`public`/`@[expose]` 키워드를 뺐습니다.
- **가정.** 반례는 upstream 가정
  `[Fintype α] [DecidableEq α] [Nontrivial α]`와 `G.Connected`를 만족합니다.
  upstream의 `α : Type*`는 universe 다형적이며, `refuted`는
  `ULift (Fin 28)` 위의 반례로 모든 universe에서 성립합니다.
- **기계적 검사.**
  [`upstream_statement_check.lean`](upstream_statement_check.lean)은 세
  정의를 upstream 이름공간 `SimpleGraph`에 다시 선언합니다. 그다음 upstream
  정리를 upstream 이름공간 `WrittenOnTheWallII.GraphConjecture72`에서
  명제로 쓰고, 우리의 `refuted`로 반박합니다. elaboration 과정에서 upstream
  상수를 우리 상수로 펼쳐야 하므로, 조금이라도 어긋나면 이 파일은 실패합니다.
  이 파일은 표준 공리 세 개를 출력합니다. 저장소 밖에서 실행한 변형 네 개는
  예상대로 실패합니다. 명제의 `/ 3`을 `/ 2`로 바꾼 것과, 각 정의를 하나씩
  바꾼 것(\(n+1\)로 나누기, 유도 숲 세기, 이웃의 클릭 수 쓰기)입니다. 이
  파일은 라이브러리에서 import하지 않습니다.
- **툴체인.** 이 저장소는 Lean과 mathlib v4.30.0으로 빌드하고, `c094b97`의
  Formal Conjectures는 v4.33.1을 씁니다. 명제가 쓰는 그래프 정의(`eccent`,
  `edist`, `dist`, `IsAcyclic`, `IsTree`, `induce`, `neighborSet`,
  `indepNum`, `Connected`)는 두 버전에서 글자 그대로 같습니다. `SimpleGraph`의
  변화는 증명 필드 `symm`의 타입(`Symmetric Adj` 대신 `Std.Symm Adj`)뿐이며
  `Adj`는 바뀌지 않습니다. 이 반박을 v4.33.1에서 컴파일해 보지는 않았습니다.
- **범위.** Formal Conjectures의 읽기만 반박합니다. 고르게 나누는 읽기는
  여기서 형식화하지 않으며, 목록이 어느 읽기를 의도하는지에 대해서는 아무것도
  주장하지 않습니다.

## 수치 교차 검증

인증서는 Lean 증명입니다. [`verify_wowii72.py`](verify_wowii72.py)는
Python 표준 라이브러리와 정확한 분수만으로, 반례를 독립적인 구현으로 다시
계산합니다.

- 층 규칙에서 그래프를 다시 만들고 `g28.txt`와 같은지 확인합니다.
- 너비 우선 탐색으로 모든 이심률을(합 150), 전수 탐색으로 모든
  \(\lambda(v)\)를(최댓값 5) 계산합니다.
- \(\operatorname{tree}(G)=7\)을 두 가지 방법으로 계산합니다. 첫째 방법은
  모든 유도 트리를 잎을 하나씩 붙여 키웁니다. 둘째 방법은 크기가 8 이하인
  모든 꼭짓점 부분집합을 검사합니다. 잎을 지워 나가면, 꼭짓점이 8개보다
  많은 유도 트리는 꼭짓점이 정확히 8개인 유도 트리를 포함하기 때문입니다. 두
  방법은 모든 크기에서 일치합니다. 크기 1부터 7까지의 유도 트리는 각각 28,
  120, 44, 108, 214, 162, 420개이고, 크기 8인 것은 없습니다.
- \(\lceil75/14+5/3\rceil=8>7\)과 \(\lceil(75/14+5)/3\rceil=4\le7\)을
  확인하고, 경로, 사이클, 완전그래프, 별에서 불변량을 점검합니다.

기본(CI) 모드는 약 6초가 걸립니다. `--graph6`를 주면 `geng`가 만드는 모든
연결 그래프에서 두 읽기를 모두 평가합니다.

| 입력 | 그래프 수 | \(\lceil A+L/3\rceil=\operatorname{tree}\) | \(\operatorname{tree}-(A+L/3)\)의 최솟값 | 위반 | 시간 |
| --- | ---: | ---: | ---: | ---: | ---: |
| `geng -c`, \(n=2,\dots,9\) | 273,192 | 1,407 | 1/3 | 0 | 49초 |
| `geng -c`, \(n=10\), 세 부분으로 나눔 | 11,716,571 | 3,761 | 4/15 | 0 | 실제 29.2분, CPU 74.9분 |

그래프 수는 OEIS A001349와 일치합니다. 꼭짓점이 10개 이하인 그래프에서는
어느 읽기도 실패하지 않으므로, 형식 명제의 반례에는 꼭짓점이 10개보다 많이
필요합니다.

## 선행 연구와 상태

- **WOWII.** 목록의
  [2026-07-26 캡처](https://web.archive.org/web/20260726061534/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/all.html)에서
  72번 행의 상태는 `O`입니다. 해결된 추측 목록 두 곳
  ([resolved.htm](https://web.archive.org/web/20260723211227/http://cms.uhd.edu/faculty/delavinae/research/wowII/resolved.htm)과
  [resolvedT.htm](https://web.archive.org/web/20260723211215/http://cms.uhd.edu/faculty/delavinae/research/wowII/resolvedT.htm),
  2026-07-23 캡처) 어디에도 나오지 않습니다.
- **공개 주장(2026-07-23).**
  [@4thRT의 X 게시물](https://x.com/4thRT/status/2080412225232400539)은
  GPT 5.6 Sol 모델로 만든 것으로, 고르게 나누는 읽기를 증명합니다. 또한
  \(L\)만 3으로 나누는 읽기, 즉 Formal Conjectures가 나중에 택한 읽기가 한
  그래프 족에서 거짓이라고 밝힙니다. 추적 사이트 VibeMathed는 이 게시물을
  상태 "Candidate"로
  [기록하고](https://vibemathed.com/problem/wowii-conjecture-72-two-induced-trees-pin-down-tree-g)
  2026-08-17에 증명된 읽기를 독자적으로 다시 유도했습니다. **따라서 형식
  명제가 거짓이라는 사실은 새롭지 않습니다.** 우리 그래프를 그 게시물의
  그래프 족과 비교하지는 않았습니다.
- **Formal Conjectures.** `conjecture72`는
  [google-deepmind/formal-conjectures#3796](https://github.com/google-deepmind/formal-conjectures/pull/3796)
  (커밋 `4eee17c`, 2026-10-23)으로 추가되었습니다. `c094b97`과 `main`
  `37f0808`(2026-10-24)에서 `research open`으로 표시되어 있고 `sorry`로
  닫혀 있으며, 그 뒤로 이 파일을 건드린 커밋은 없습니다. 그 저장소의 이슈와
  풀 리퀘스트에서 `GraphConjecture72`와 `conjecture72`를 검색한 결과는
  없었습니다(2026-10-25 UTC). #3796 검토에서 첫 초안은 합 전체를 3으로
  나누었으나, 검토자가 원문 행에 표시된 묶음을 따르라고 요청했고, 병합된
  명제는 \(L\)만 3으로 나눕니다.
- **형식 산출물.** GitHub 코드에서 `GraphConjecture72`와 `conjecture72`를
  검색했으나(2026-10-25 UTC) 어느 읽기에 대해서도 형식 증명이나 반증을 찾지
  못했습니다. upstream 파일 말고는 추적 사이트의 검토 스크립트와,
  `conjecture7292`를 포함하는 무관한 식별자만 나옵니다.

이 Lean 반박은 아직 사람이 검토하지 않았습니다. Formal Conjectures, WOWII
관리자, 그 밖의 어디에도 제출하지 않았으며, upstream 명제를 고치자는 제안
같은 외부 제출에는 사람의 승인이 필요합니다.

## 재현

저장소 루트에서:

```bash
lake build AgenticConjectures.WowiiGraphConjecture72
lake env lean problems/wowii-graph-conjecture-72/upstream_statement_check.lean
python3 scripts/check_axioms.py
```

mathlib이 빌드되어 있으면 모듈 컴파일은 약 4초, upstream 검사는 약 5초가
걸립니다.

이 디렉터리에서(`geng` 실행에는 nauty가 필요합니다):

```bash
python3 verify_wowii72.py
for n in 2 3 4 5 6 7 8 9; do geng -cq $n; done | python3 verify_wowii72.py --graph6
for k in 0 1 2; do geng -cq 10 $k/3 | python3 verify_wowii72.py --graph6; done
```

[upstream 스냅샷](upstream/README.md)에 Formal Conjectures 원본을 그대로
보관합니다.
