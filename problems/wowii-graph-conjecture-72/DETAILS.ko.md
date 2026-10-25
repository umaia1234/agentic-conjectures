[English](DETAILS.md) | **한국어**

# WOWII 추측 72의 수학적 세부 사항

이 파일은 반박의 모든 단계를, 그것을 증명하는 Lean 선언이나 내부 `have`와
함께 제시합니다. 모든 이름은
[`AgenticConjectures/WowiiGraphConjecture72.lean`](../../AgenticConjectures/WowiiGraphConjecture72.lean)의
이름공간 `AgenticConjectures.WowiiGraphConjecture72`를 가리킵니다.

범위: 이 파일은 \(L\)만 3으로 나누는 Formal Conjectures 명제
`conjecture72`(커밋 `c094b97`)만 반박합니다. 고르게 나누는 읽기
\(\lceil(A+L)/3\rceil\le\operatorname{tree}(G)\)는 다루지 않습니다. 이 명제가
거짓이라는 사실은 2026-07-23에 이미 공개적으로 언급되었습니다
([README](README.ko.md#선행-연구와-상태) 참고).

## 기호

반례는 동치 \(e:V\simeq\) `Fin 28`이 있는 임의의 꼭짓점 타입 \(V\) 위에
있습니다. 아래에서는 꼭짓점 \(e^{-1}(i)\)를 \(i\)라고 부릅니다.

| 기호 | 뜻 | Lean |
| --- | --- | --- |
| \(G\) | 반례 | `graph e` |
| \(\ell(v)\) | \(v\)의 층, \(\{0,\dots,6\}\)의 원소 | `lvl (e v)` |
| \(d(x,y)\) | 그래프 거리 | `(graph e).dist x y` |
| \(\operatorname{ecc}(v)\) | 자연수로 본 이심률 | `((graph e).eccent v).toNat` |
| \(A\) | 평균 이심률 | `averageEccentricity (graph e)` |
| \(\lambda(v)\) | \(N(v)\)가 유도하는 부분그래프의 독립수 | `indepNeighborsCard (graph e) v` |
| \(L\) | \(\max_v\lambda(v)\) | `maxL`, 즉 `(Finset.univ.image …).max' hne` |
| \(\operatorname{tree}(G)\) | 가장 큰 유도 트리의 꼭짓점 수 | `largestInducedTreeSize (graph e)` |

이름 붙인 꼭짓점은 [`g28.txt`](g28.txt)와 같이 \(p_0=0\), \(p_1=1\),
\(m_1,\dots,m_4=2,\dots,5\), \(p_3=6\), \(p_4=7\),
\(q_1,\dots,q_{10}=8,\dots,17\), \(r_1,\dots,r_{10}=18,\dots,27\)입니다.

## 의존 관계

```text
refuted (§6)
└── tree_lt_ceil (§5)
    ├── averageEccentricity_ge (§2.3)
    │   └── sum_ecc_ge (§2.2) ── ecc_ge (§2.1) ── lvl_le_dist ── lvl_walk
    │                                          └── graph_connected (§1.2)
    ├── five_le_indepNeighborsCard (§3) ── card_le_indepNeighborsCard
    └── largestInducedTreeSize_le (§4.5) ── card_le_seven (§4.3, §4.4)
        ├── not_isAcyclic_of_triangle, not_isAcyclic_of_square (§4.1)
        ├── of_preserved (§4.2)
        └── adj_of_succ, adj_of_le_one, adj_of_five_le (§1.1)
```

## 1. 그래프

### 1.1 층과 인접 관계

`lvl`은 \(q_i\)에 층 0, \(p_0\)에 1, \(p_1\)에 2, \(m_i\)에 3, \(p_3\)에
4, \(p_4\)에 5, \(r_i\)에 6을 줍니다. 28개 값에 관한 사실은 커널에서
`decide`로 증명합니다.

- `lvl_le_six`: \(\ell\le6\).
- `lvl_eq_one`, `lvl_eq_two`, `lvl_eq_four`, `lvl_eq_five`: 층 1, 2, 4,
  5에는 각각 \(p_0\), \(p_1\), \(p_3\), \(p_4\)만 있습니다.
- `lvl_eq_three`: 층 3은 \(m_1,\dots,m_4\)로 이루어집니다.

`graph e`에서 두 꼭짓점은 서로 다르고 \(\ell(u)+1=\ell(v)\),
\(\ell(v)+1=\ell(u)\), \(\ell(u)=\ell(v)=0\), \(\ell(u)=\ell(v)=6\) 가운데
하나가 성립할 때 인접합니다. 이 관계는 대칭이고 비반사적입니다.
[`verify_wowii72.py`](verify_wowii72.py)는 이 관계가 `g28.txt`의 변 120개와
정확히 같음을 확인합니다.

- `lvl_adj`: 변을 따라가면 층이 많아야 1 바뀝니다.
- `adj_of_succ`: 이웃한 층의 꼭짓점들은 인접합니다.
- `adj_of_le_one`: 층이 1 이하인 서로 다른 두 꼭짓점은 인접합니다. 층 1인
  꼭짓점은 \(p_0\)뿐이므로 둘 다 층 1일 수는 없고, 두 층은 0과 0 또는
  0과 1입니다. `adj_of_five_le`는 층 5 이상에 대한 같은 명제입니다.

따라서 층 0과 1은 완전그래프 \(K_{11}\)을 이루고, 층 5와 6도 그렇습니다.

### 1.2 연결성: `graph_connected`

\(\operatorname{depth}(i)=|\ell(i)-2|\)로 둡니다(`depth`). 꼭짓점
`par i`는 층 0이면 \(p_0\), 층 4이면 \(m_1\), 층 5이면 \(p_3\), 층 6이면
\(p_4\), 그 밖에는 \(p_1\)입니다. `par_spec`(`decide`로 증명)에 따르면
\(i\ne p_1\)일 때 `par i` \(\ne i\)이고
\(\operatorname{depth}(\texttt{par } i)+1=\operatorname{depth}(i)\)이며, 두
층이 이웃해 있으므로 `par i`는 \(i\)의 이웃입니다. depth에 대한 귀납법으로
모든 꼭짓점이 \(p_1\)에 도달하고, depth가 0이면 \(i=p_1\)입니다
(`depth_eq_zero`). 따라서 \(G\)는 연결되어 있습니다.

## 2. 평균 이심률

### 2.1 거리는 층의 차이 이상: `lvl_walk`, `lvl_le_dist`, `ecc_ge`

- `lvl_walk`: 길이가 \(k\)인 보행을 따라가면 층이 많아야 \(k\) 바뀝니다.
  `lvl_adj`를 써서 보행에 대한 귀납법으로 증명합니다.
- `lvl_le_dist`: 이것을 최단 경로(`Connected.exists_path_of_dist`)에
  적용하면 \(|\ell(u)-\ell(v)|\le d(u,v)\)입니다.
- `ecc_ge`: \(\max(\ell(u),6-\ell(u))\le\operatorname{ecc}(u)\).
  1. `hne`: \(G\)는 연결된 유한 그래프이므로 확장 지름이 유한하고
     (`connected_iff_ediam_ne_top`), 따라서 `eccent u`도 유한합니다
     (`eccent_le_ediam`).
  2. `key`: 모든 \(w\)에 대해 \(d(u,w)\le\operatorname{ecc}(u)\)입니다.
     `edist_le_eccent`, `Reachable.coe_dist_eq_edist`,
     `ENat.toNat_le_toNat`에서 나옵니다.
  3. `key`와 `lvl_le_dist`를 \(w=r_1\)(층 6)과 \(w=q_1\)(층 0)에
     적용합니다. 그러면 \(6-\ell(u)\le d(u,r_1)\le\operatorname{ecc}(u)\)이고
     \(\ell(u)\le d(u,q_1)\le\operatorname{ecc}(u)\)입니다.

### 2.2 합: `sum_ecc_ge`

`sum_lvl`(`decide`로 증명)은
\(\sum_{i<28}\max(\ell(i),6-\ell(i))=150\)을 줍니다. 층별 기여는
\(10\cdot6+5+4+4\cdot3+4+5+10\cdot6=150\)입니다. \(e\)를 따라 첨자를 바꾸고
(`Equiv.sum_comp`) `ecc_ge`를 쓰면 \(\sum_v\operatorname{ecc}(v)\ge150\)입니다.

### 2.3 평균: `averageEccentricity_ge`

\(|V|=28\)(`Fintype.card_congr e`)이므로
\(A=\frac1{28}\sum_v\operatorname{ecc}(v)\ge150/28=75/14\)입니다. 이 하계에서
등호가 성립합니다. 스크립트는 층 0부터 6까지에서 이심률 6, 5, 4, 3, 4, 5,
6을 얻습니다. Lean에는 하계만 필요합니다.

## 3. 국소 독립수: `five_le_indepNeighborsCard`

`card_le_indepNeighborsCard u S`: \(S\)의 모든 꼭짓점이 \(u\)와 인접하고
\(S\)가 독립집합이면 \(|S|\le\lambda(u)\)입니다. 증명은 \(S\)를 \(N(u)\)가
유도하는 부분그래프의 독립집합으로 보고 `IsIndepSet.card_le_indepNum`을
적용합니다.

\(u=p_1\), \(S=\{p_0,m_1,\dots,m_4\}\)에 적용합니다.

- 이 꼭짓점들의 층은 1과 3이므로, 각각 층이 2인 \(p_1\)과 인접합니다.
- 이 중 두 꼭짓점의 층 차이는 0이나 2이고, 층이 0이나 6인 것은 없으므로
  어느 두 꼭짓점도 인접하지 않습니다.

따라서 \(L\ge\lambda(p_1)\ge5\)입니다. \(\lambda(p_1)\)에서 최댓값으로 넘어가는
단계는 `tree_lt_ceil` 안의 `Finset.le_max'`입니다. 실제로 \(L=5\)이며, 스크립트가
찾은 대로 \(p_1\)과 \(p_3\)에서 얻어집니다.

## 4. 유도 트리의 꼭짓점은 많아야 7개

### 4.1 짧은 사이클: `not_isAcyclic_of_triangle`, `not_isAcyclic_of_square`

\(s\)를 꼭짓점 집합이라 합시다.

- \(a,b,c\in s\)가 서로 인접하면, 변 \(ab\)와 경로 \(a\,c\,b\)는 \(s\)가
  유도하는 부분그래프에서 \(a\)에서 \(b\)로 가는 길이 1과 2인 두
  경로입니다. 이는 `IsAcyclic.path_unique`에 모순입니다.
- \(a,b,c,d\in s\)가 \(a\ne c\), \(b\ne d\)인 4-사이클 \(a\,b\,c\,d\,a\)를
  이루면, 경로 \(a\,b\,c\)와 \(a\,d\,c\)는 지나는 꼭짓점이 다릅니다.

### 4.2 전파: `of_preserved`

\(s\)가 유도하는 부분그래프가 연결되어 있고, 성질 \(P\)가 인접한
\(u,v\in s\)에서 \(u\)로부터 \(v\)로 항상 전해진다고 합시다. 그러면 \(P\)가
\(s\)의 한 꼭짓점에서 성립할 때 \(s\)의 모든 꼭짓점에서 성립합니다. 증명은
유도 부분그래프 안의 보행에 대한 귀납법입니다.

### 4.3 유도 트리에 관한 사실: `card_le_seven`

\(T\)를 트리를 유도하는 꼭짓점 집합이라 합시다. 증명은 \(T\)를 층에 따라
나눕니다.

- `sQ`는 층이 1 이하인 부분,
- `s1`은 층이 2인 부분,
- `sM`은 층이 3인 부분,
- `s6`은 층이 4인 부분,
- `sR`은 층이 5 이상인 부분입니다.

`htot`는 \(|T|\le\) `sQ.card + s1.card + sM.card + s6.card + sR.card`를
줍니다. 내부 `have`는 다음과 같습니다.

- `hQ`, `hR`: \(|sQ|\le2\), \(|sR|\le2\). 한 완전그래프의 세 꼭짓점은
  삼각형을 이룹니다(§4.1).
- `hM`: `sM`은 \(\{m_1,\dots,m_4\}\)에 들어 있으므로 \(|sM|\le4\).
- `h1`, `h6`: 층 2와 층 4에는 꼭짓점이 하나씩뿐이므로 \(|s1|\le1\),
  \(|s6|\le1\).
- `h1'`, `h6'`: \(p_1\notin T\)이면 `s1`이 비어 있고, \(p_3\notin T\)이면
  `s6`이 비어 있습니다.
- `hsq`: \(|sM|\ge2\)이면 \(p_1\)과 \(p_3\)이 둘 다 \(T\)에 있을 수는
  없습니다. 그렇지 않으면 `sM`의 두 꼭짓점 \(m,m'\)이 4-사이클
  \(p_1\,m\,p_3\,m'\,p_1\)을 이룹니다(§4.1).
- `hiso`: \(p_1,p_3\notin T\)이고 \(m\in sM\)이면 \(T=\{m\}\)입니다. \(m\)의
  이웃은 \(p_1\)과 \(p_3\)뿐이므로, 성질 "\(m\)과 같다"는 \(T\) 안의 모든
  변을 따라 전해집니다. §4.2에 따라 \(T\)의 모든 꼭짓점이 \(m\)입니다.
- `hsepR`: \(p_1\in T\)이고 \(p_3\notin T\)이면 `sR`은 비어 있습니다. 층
  4 이하에서 층 5 이상으로 가는 변은 층 4, 즉 \(p_3\)에서 출발해야 합니다.
  따라서 "층이 4 이하"라는 성질은 \(T\) 안의 변을 따라 전해집니다. 이
  성질은 \(p_1\)에서 성립하므로 §4.2에 따라 \(T\) 전체에서 성립합니다.
- `hsepQ`: 대칭적으로, \(p_3\in T\)이고 \(p_1\notin T\)이면 `sQ`는 비어
  있습니다. 성질 "층이 2 이상"을 씁니다.

### 4.4 네 가지 경우

| \(p_1\in T\) | \(p_3\in T\) | 사용하는 사실 | \(\lvert T\rvert\)의 상계 |
| --- | --- | --- | --- |
| 예 | 예 | `hsq`: \(\lvert sM\rvert\le1\) | \(2+1+1+1+2=7\) |
| 예 | 아니오 | `hsepR`, `h6'` | \(2+1+4=7\) |
| 아니오 | 예 | `hsepQ`, `h1'` | \(4+1+2=7\) |
| 아니오 | 아니오 | `h1'`, `h6'`, `sM`이 비어 있지 않으면 `hiso` | \(1\) 또는 \(2+2=4\) |

### 4.5 트리 수: `largestInducedTreeSize_le`

`largestInducedTreeSize`의 정의에 나오는 집합의 모든 원소는 트리를 유도하는
꼭짓점 집합의 크기이므로 7 이하입니다. 그러면 `csSup_le'`가
\(\operatorname{tree}(G)\le7\)을 줍니다. 실제로 \(\operatorname{tree}(G)=7\)입니다.
\(\{q_1,p_0,p_1,m_1,\dots,m_4\}\)가 트리를 유도합니다. 이는 스크립트가
확인하며, Lean에는 필요하지 않습니다.

## 5. 위반: `tree_lt_ceil`

§2.3과 §3에서 \(A+L/3\ge75/14+5/3=295/42>7\)입니다. `Int.lt_ceil`에 따라
\(\mathbb Z\)에서 \(7<\lceil A+L/3\rceil\)이므로, \(\mathbb R\)로 옮기면
\(8\le\lceil A+L/3\rceil\)입니다. §4.5와 합치면
\(\operatorname{tree}(G)\le7<8\le\lceil A+L/3\rceil\)입니다. 올림 전의 여유는
\(295/42-7=1/42\)에 불과합니다.

## 6. 반박: `refuted`

`statement.{u}`는 꼭짓점 타입 `α : Type u` 위의, 꼭짓점이 두 개 이상인 모든
유한 연결 그래프가 \(\lceil A+L/3\rceil\le\operatorname{tree}(G)\)를
만족한다는 명제입니다. 이를 `α = ULift (Fin 28)`과 `graph Equiv.ulift`에
적용합니다. `ULift (Fin 28)`의 인스턴스 `Fintype`, `DecidableEq`,
`Nontrivial`은 mathlib에서 오고, 연결성은 `graph_connected`입니다. 그 결론은
`tree_lt_ceil`에 모순입니다. 따라서 `refuted : ¬ statement.{u}`는 모든
universe에서 성립합니다.

## 7. Lean 밖의 점검

- [`verify_wowii72.py`](verify_wowii72.py)는 정확한 값 \(A=75/14\), \(L=5\),
  \(\operatorname{tree}(G)=7\)을 다시 계산하며, 트리 수는 서로 독립적인 두
  방법으로 계산합니다(README의 *수치 교차 검증*).
- \(G\)에서 고르게 나누는 읽기는 성립합니다.
  \(\lceil(A+L)/3\rceil=\lceil145/42\rceil=4\le7\)입니다.
- 꼭짓점이 10개 이하인 연결 그래프 가운데 어느 읽기라도 위반하는 것은
  없습니다.
