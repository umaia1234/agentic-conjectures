[English](DETAILS.md) | **한국어**

# WOWII 추측 96의 수학적 세부 사항

이 문서는 증명의 모든 단계를, 그 단계를 증명하는 Lean 선언이나 내부
`have`와 함께 적습니다. 모든 이름은
[`AgenticConjectures/WowiiGraphConjecture96.lean`](../../AgenticConjectures/WowiiGraphConjecture96.lean)의
이름공간 `AgenticConjectures.WowiiGraphConjecture96`에 있습니다.

## 기호

\(G\)는 꼭짓점 타입 \(V\) 위의 유한 단순 그래프이고 \(n=|V|\)입니다.

| 기호 | 뜻 | Lean |
| --- | --- | --- |
| \(d(x,y)\) | 그래프 거리. \(y\)가 \(x\)에서 도달 불가능하면 0 | `G.dist x y` |
| \(N(u)\) | \(u\)의 열린 이웃 | `G.neighborSet u` |
| \(\alpha\) | \(G\)의 독립수 | `G.indepNum` |
| \(\lambda(u)\) | \(N(u)\)가 유도하는 부분그래프의 독립수 | `indepNeighborsCard G u` |
| \(\mathcal E_v\) | \(v\)를 포함하는 집합 \(\{w : d(v,w)\text{가 짝수}\}\) | `Finset.univ.filter fun w => Even (G.dist v w)` |
| \(E(v)\) | \(\lvert\mathcal E_v\rvert\) | `distEven G v` |
| \(\Lambda\) | \(\max_u\lambda(u)\) | `conjecture96`의 `maxL` |
| \(a\mathbin{\dot-}b\) | 0에서 잘리는 자연수 뺄셈 | `ℕ` 위의 `a - b` |

## 의존 관계

```text
conjecture96 (§6)
├── one_le_indepNeighborsCard (§2.3)
│   ├── exists_parent (§1.1)
│   └── card_le_indepNeighborsCard (§2.1)
├── indepNum_le_one (§3)
│   ├── exists_dist_two (§1.2)
│   ├── exists_parent (§1.1)
│   └── two_le_indepNeighborsCard (§2.2) ── card_le_indepNeighborsCard (§2.1)
└── indepNum_le_of_two_le (§5)
    └── indepNum_le_perRoot (§4)
        ├── exists_parent (§1.1)
        └── card_le_indepNeighborsCard (§2.1)
```

`statement_holds`는 원소가 두 개 이상인 모든 유한 꼭짓점 타입에 대해
`conjecture96`을 양화한 것입니다.

## 1. 거리에 관한 사실

**사실 1.0** (mathlib `SimpleGraph.Adj.diff_dist_adj`). \(a\)와 \(b\)가
이웃하면 모든 \(u\)에 대해 \(d(u,b)\)는 \(d(u,a)\), \(d(u,a)+1\),
\(d(u,a)\mathbin{\dot-}1\) 중 하나입니다. 연결성 가정은 필요 없습니다.

### 1.1 BFS 부모: `exists_parent`

**주장.** \(G\)가 연결이고 \(x\ne v\)이면, \(x\)와 이웃하고
\(d(v,y)+1=d(v,x)\)를 만족하는 \(y\)가 있습니다.

**증명.**

1. 길이가 \(d(v,x)\)인 \(v\)에서 \(x\)로 가는 경로 \(p\)를 잡습니다
   (`Connected.exists_path_of_dist`).
2. 그 역은 \(x\)에서 \(v\)로 가는 같은 길이의 보행입니다. 내부 `key`가 이
   보행을 경우로 나누어 다룹니다.
   - `nil` 경우는 \(x=v\)를 뜻하므로 제외됩니다.
   - `cons` 경우 보행은 변 \(x\sim y\)로 시작하고, 이어서
     \(\lvert q'\rvert+1=d(v,x)\)인 \(y\)에서 \(v\)로 가는 보행 \(q'\)가
     옵니다(`hlen`).
3. \(d(y,v)\le\lvert q'\rvert\)(`dist_le`)이고 거리는 대칭이므로
   \(d(v,y)\le d(v,x)-1\)입니다(`h1`).
4. 변 \(y\sim x\)에 사실 1.0을 적용하면 \(d(v,y)<d(v,x)-1\)일 수 없습니다.
   따라서 \(d(v,y)+1=d(v,x)\)입니다.

### 1.2 거리가 2인 꼭짓점: `exists_dist_two`

**주장.** \(G\)가 연결이고 \(d(x,z)\ge2\)이면 \(d(x,w)=2\)인 \(w\)가
있습니다.

**증명.** \(d(x,z)=k+2\)로 쓰고 \(k\)에 대한 귀납법을 씁니다.

- \(k=0\)이면 \(w=z\)로 둡니다.
- 그렇지 않으면 \(d(x,x)=0\)이므로 \(z\ne x\)입니다. 루트 \(x\)에 대해
  §1.1을 적용하면 \(d(x,y)=k+1\)인 \(z\)의 이웃 \(y\)가 있습니다. \(y\)에
  귀납 가정을 적용합니다.

## 2. 국소 독립수의 하계

### 2.1 `card_le_indepNeighborsCard`

**주장.** \(S\subseteq N(u)\)이고 \(S\)의 서로 다른 두 원소가 이웃하지
않으면 \(\lvert S\rvert\le\lambda(u)\)입니다.

**증명.**

1. \(S\)를 부분 타입 `G.neighborSet u`의 finset \(T\)로 올립니다. \(S\)의
   모든 원소가 조건을 만족하므로 \(\lvert T\rvert=\lvert S\rvert\)입니다
   (`hT`, `Finset.card_subtype`에서).
2. `G.induce (G.neighborSet u)`에서 두 원소는 밑에 있는 꼭짓점들이 \(G\)에서
   이웃할 때 정확히 이웃합니다(`comap_adj`). 따라서 \(T\)는 그 그래프에서
   독립집합입니다.
3. `IsIndepSet.card_le_indepNum`이 \(\lvert T\rvert\le\lambda(u)\)를
   줍니다. \(V\)가 `Fintype`이므로 부분 타입은 `Finite`입니다.

### 2.2 `two_le_indepNeighborsCard`

**주장.** \(x\sim y\), \(y\sim z\), \(x\ne z\), \(x\not\sim z\)이면
\(\lambda(y)\ge2\)입니다.

**증명.** \(S=\{x,z\}\subseteq N(y)\)에 §2.1을 적용합니다.
\(x\not\sim z\)이므로 독립이고, \(x\ne z\)이므로 원소가 두 개입니다
(`Finset.card_pair`).

### 2.3 `one_le_indepNeighborsCard` (`[Nontrivial α]` 사용)

**주장.** \(G\)가 연결이고 \(n\ge2\)이면 모든 \(u\)에 대해
\(\lambda(u)\ge1\)입니다.

**증명.**

1. \(n\ge2\)이므로 \(u\)와 다른 \(x\)가 있습니다(`exists_ne`).
2. 루트 \(x\)에 대해 §1.1을 적용하면 \(u\)에 이웃 \(y\)가 있습니다.
3. \(S=\{y\}\)에 §2.1을 적용합니다.

\(n\ge2\)가 필요한 단계는 여기뿐입니다. `[Nontrivial α]`의 다른 쓰임은
꼭짓점 집합이 비어 있지 않아 `min'`과 `max'`가 존재한다는 점입니다.
\(K_1\)에서는 \(\lambda=0\)이고 추측이 성립하지 않습니다.

## 3. \(\Lambda\le1\)인 경우: `indepNum_le_one`

**주장.** \(G\)가 연결이고 모든 \(u\)에 대해 \(\lambda(u)\le1\)이면
\(\alpha\le1\)입니다.

**증명.**

1. \(\lvert I\rvert=\alpha\)인 독립집합 \(I\)를 잡습니다
   (`exists_isNIndepSet_indepNum`, `card_eq`). \(\lvert I\rvert>1\)이라고
   가정합니다(`hlt'`).
2. 서로 다른 \(x,z\in I\)를 고릅니다(`Finset.one_lt_card`). 둘은 이웃하지
   않습니다(`hnadj`).
3. \(x\ne z\)이고 \(G\)가 연결이므로 \(d(x,z)\ne0\)입니다
   (`Connected.dist_eq_zero_iff`). \(x\not\sim z\)이므로 \(d(x,z)\ne1\)입니다
   (`dist_eq_one_iff_adj`). 따라서 \(d(x,z)\ge2\)입니다(`h2`).
4. §1.2에 의해 \(d(x,w)=2\)인 \(w\)가 있습니다. 특히 \(w\ne x\)입니다
   (`hwx`).
5. 루트 \(x\)에 대해 §1.1을 적용하면 \(d(x,y)=1\)인 \(w\)의 이웃 \(y\)가
   있습니다. 따라서 \(x\sim y\)입니다(`hxy`).
6. \(x\sim w\)라면 \(d(x,w)=1\)이므로 \(x\not\sim w\)입니다(`hnxw`).
7. \(x\sim y\sim w\)에 §2.2를 적용하면 \(\lambda(y)\ge2\)이고, 이는
   \(\lambda(y)\le1\)에 모순입니다.

## 4. 루트별 상계: `indepNum_le_perRoot`

**주장.** \(G\)가 연결이면(\(n\)의 하한은 필요 없음) 모든 꼭짓점 \(v\)에
대해

\[
\alpha\le\max\bigl(1,\lambda(v)\bigr)
+\sum_{u\in\mathcal E_v\setminus\{v\}}\max\bigl(1,\lambda(u)\mathbin{\dot-}1\bigr)
\]

입니다.

**준비.**

- \(I\)는 \(\lvert I\rvert=\alpha\)인 독립집합입니다. 내부 `hind`는 \(I\)의
  서로 다른 두 원소가 이웃하지 않음을 기록합니다.
- `hpar`와 `choose`로 함수 \(\pi\)(`par`)를 얻습니다. \(x\ne v\)이면 §1.1에
  의해 \(\pi(x)\sim x\)이고 \(d(v,\pi(x))+1=d(v,x)\)입니다. \(\pi(v)\)의
  값은 쓰이지 않습니다.
- \(d(v,x)\)가 짝수이면 \(\varphi(x)=x\), 아니면 \(\varphi(x)=\pi(x)\)입니다
  (`φ`).
- \(u\) 위의 올(fibre)은 \(F(u)=\{x\in I:\varphi(x)=u\}\)입니다.

**단계 4.1 (`hφ`).** \(\varphi(x)=u\)이고 \(x\ne u\)이면 \(u\sim x\)이고
\(d(v,u)+1=d(v,x)\)입니다.

- \(d(v,x)\)가 짝수이면 \(\varphi(x)=x=u\)이므로 제외됩니다.
- 그렇지 않으면 \(d(v,v)=0\)이 짝수이므로 \(x\ne v\)입니다. 이때
  \(u=\pi(x)\)이고 부모의 성질이 적용됩니다.

**단계 4.2 (`hmaps`).** \(\varphi\)는 \(I\)를 \(\mathcal E_v\) 안으로
보냅니다.

- \(d(v,x)\)가 짝수이면 \(\varphi(x)=x\in\mathcal E_v\)입니다.
- 아니면 \(d(v,x)=d(v,\pi(x))+1\)이 홀수이므로 \(d(v,\pi(x))\)는
  짝수입니다(`Nat.even_add_one`).

**단계 4.3 (`hF1`).** \(u\in I\)이면 \(\lvert F(u)\rvert\le1\)입니다.

\(x\in F(u)\)이고 \(x\ne u\)라고 합시다. 4.1에 의해 \(u\sim x\)인데, \(u\)와
\(x\)는 \(I\)의 서로 다른 원소입니다. 따라서 \(F(u)\subseteq\{u\}\)입니다.

**단계 4.4 (`hfib`).** \(u\notin I\)이고 \(x\in F(u)\)이면 \(u\sim x\)이고
\(d(v,u)+1=d(v,x)\)입니다.

\(x\in I\)이고 \(u\notin I\)이므로 \(x\ne u\)입니다. 4.1을 적용합니다.

**단계 4.5 (`hF2`).** \(u\notin I\)이면
\(\lvert F(u)\rvert\le\lambda(u)\)입니다.

4.4에 의해 \(F(u)\subseteq N(u)\)이고, \(F(u)\subseteq I\)는 독립입니다.
§2.1을 적용합니다.

**단계 4.6 (`hF3`).** \(u\notin I\)이고 \(u\ne v\)이면
\(\lvert F(u)\rvert+1\le\lambda(u)\)입니다.

\(w=\pi(u)\)로 둡니다. \(u\ne v\)이므로 \(w\sim u\)이고
\(d(v,w)+1=d(v,u)\)입니다.

- (a) \(w\notin F(u)\) (`hwnot`). 4.4에 의해 모든 \(x\in F(u)\)는
  \(d(v,x)=d(v,u)+1\)인데, \(d(v,w)=d(v,u)-1\)입니다.
- (b) \(w\)는 \(F(u)\)의 어떤 원소와도 이웃하지 않습니다(`hnadj`). 여기서
  \(d(v,x)=d(v,w)+2\)인데, 이웃한 두 꼭짓점의 \(v\)까지 거리는 많아야 1
  차이 납니다(사실 1.0).
- (c) \(S=F(u)\cup\{w\}\)로 둡니다.
  - \(S\subseteq N(u)\)입니다. \(w\sim u\)이고, 4.4에 의해
    \(F(u)\subseteq N(u)\)입니다.
  - \(S\)는 독립입니다. \(F(u)\subseteq I\) 안의 쌍은 이웃하지 않고, 쌍
    \((w,x)\)는 (b)에 의해 이웃하지 않습니다.
  - §2.1이 \(\lvert S\rvert\le\lambda(u)\)를 주고, (a)와
    `Finset.card_insert_of_notMem`에 의해
    \(\lvert S\rvert=\lvert F(u)\rvert+1\)입니다.

\(w\)가 \(I\)에 속하는지는 상관없습니다.

**단계 4.7 (조립).** \(\varphi\)가 \(I\)를 \(\mathcal E_v\) 안으로 보내고(4.2)
\(v\in\mathcal E_v\)이므로(`hv`), `Finset.card_eq_sum_card_fiberwise`와
`Finset.add_sum_erase`에 의해

\[
\alpha=\lvert I\rvert=\sum_{u\in\mathcal E_v}\lvert F(u)\rvert
=\lvert F(v)\rvert+\sum_{u\in\mathcal E_v\setminus\{v\}}\lvert F(u)\rvert
\]

입니다. 각 항은 다음과 같이 누릅니다.

| 항 | 경우 | 상계 | 근거 |
| --- | --- | --- | --- |
| \(\lvert F(v)\rvert\) | \(v\in I\) | \(\le1\le\max(1,\lambda(v))\) | 4.3 |
| \(\lvert F(v)\rvert\) | \(v\notin I\) | \(\le\lambda(v)\le\max(1,\lambda(v))\) | 4.5 |
| \(\lvert F(u)\rvert\), \(u\ne v\) | \(u\in I\) | \(\le1\le\max(1,\lambda(u)\mathbin{\dot-}1)\) | 4.3 |
| \(\lvert F(u)\rvert\), \(u\ne v\) | \(u\notin I\) | \(\le\lambda(u)\mathbin{\dot-}1\le\max(1,\lambda(u)\mathbin{\dot-}1)\) | 4.6 |

마지막 행에서는 \(\lambda(u)\ge\lvert F(u)\rvert+1\ge1\)이므로 잘린 뺄셈이
보통의 뺄셈과 같습니다. `add_le_add`와 `Finset.sum_le_sum`이 상계들을
합칩니다.

## 5. \(\Lambda\ge2\)인 경우: `indepNum_le_of_two_le`

**주장.** \(G\)가 연결이고 \(L\ge2\)이며 모든 \(u\)에 대해
\(\lambda(u)\le L\)이면, 모든 \(v\)에 대해 \(\alpha\le1+E(v)(L-1)\)입니다.

**증명.**

1. \(1\le L-1\)이고 \(\lambda(u)\mathbin{\dot-}1\le L-1\)이므로 각 합의 항은
   \(\max(1,\lambda(u)\mathbin{\dot-}1)\le L-1\)을 만족합니다. 항은
   \(\lvert\mathcal E_v\setminus\{v\}\rvert=E(v)-1\)개입니다
   (`Finset.card_erase_of_mem`). 따라서 합은 많아야 \((E(v)-1)(L-1)\)입니다
   (`hsum`, `Finset.sum_le_card_nsmul`).
2. \(\max(1,\lambda(v))\le L\)입니다(`hroot`).
3. \(v\in\mathcal E_v\)이므로 \(E(v)\ge1\)입니다(`hE`).
4. §4와 합치면 \(\alpha\le L+(E(v)-1)(L-1)\)입니다. \(E(v)=e+1\),
   \(L=m+1\)을 대입하면 \(\alpha\le(m+1)+em=1+(e+1)m\)이 되고, 이것이
   주장입니다. `hring`과 `omega`가 마무리합니다.

## 6. 정리: `conjecture96`

`distEven G`의 상의 최솟값을 `minDistEven`, `indepNeighborsCard G`의 상의
최댓값을 `maxL`이라 씁니다. 꼭짓점 타입이 비어 있지 않으므로 두 상 모두
비어 있지 않습니다.

1. `hl`: 모든 \(u\)에 대해 \(\lambda(u)\le\) `maxL`입니다
   (`Finset.le_max'`).
2. `distEven G v = minDistEven`인 \(v\)가 있습니다(`Finset.min'_mem`,
   `Finset.mem_image`).
3. `hL1`: \(v\)에서 §2.3에 의해 `maxL` \(\ge1\)입니다.
4. `key`: \(\mathbb N\)에서 \(\alpha\le1+\) `minDistEven` \(\cdot\)
   (`maxL` \(-1\))입니다.
   - `maxL` \(<2\)이면 모든 \(\lambda(u)\le1\)입니다. §3에 의해
     \(\alpha\le1\)이고, 이는 우변 이하입니다.
   - `maxL` \(\ge2\)이면 최소점 \(v\)에서 \(L=\) `maxL`로 §5를 적용합니다.
5. `hcast`: `maxL` \(\ge1\)이므로 자연수 `maxL - 1`을 \(\mathbb R\)로 올린
   값은 실수 `(maxL : ℝ) - 1`과 같습니다(`Nat.cast_sub`). 따라서 `key`를
   \(\mathbb R\)로 올린 것이 정확히 upstream 부등식입니다.

## 7. 경계와 등호 사례 점검

- **\(n=1\).** `[Nontrivial α]`가 이 경우를 제외합니다. 원문 행은 여기서
  거짓입니다(\(1\le0\)). §4의 루트별 상계는 여전히 성립합니다:
  \(1\le\max(1,0)+0\).
- **\(K_2\)와 \(n\ge2\)인 모든 \(K_n\).** \(\alpha=1\)이고 \(\Lambda=1\)이므로
  우변은 1입니다. §3을 거쳐 등호가 성립합니다.
- **별 그래프 \(K_{1,m}\), \(m\ge2\).** 중심 \(c\)는 \(E(c)=1\),
  \(\lambda(c)=m\)이고, 각 잎은 \(E=m\), \(\lambda=1\)입니다. 또
  \(\alpha=m=1+1\cdot(m-1)\)이므로 §5를 거쳐 등호가 성립합니다. 루트 \(c\)에
  대한 §4에서 \(I\)는 잎 전체이고 모두 홀수 거리에 있습니다. 공통 부모는
  \(c\notin I\)이며, \(c\) 위의 올은 원소가 \(m=\lambda(c)\)개입니다
  (단계 4.5).
- **수치 검사.** [`verify_wowii96.py`](verify_wowii96.py)는 꼭짓점이 10개
  이하인 모든 연결 그래프에서 두 부등식을 다시 검사합니다.
  [README](README.ko.md#수치-교차-검증)를 참고하세요.
