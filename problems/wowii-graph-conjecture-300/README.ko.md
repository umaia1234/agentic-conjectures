[English](README.md) | **한국어**

# WOWII 그래프 추측 300

E. DeLaViña의 *Written on the Wall II*(WOWII, Graffiti.pc 프로그램이 만든 추측
목록)에 실린 추측 300은 2007년 3월 1일 날짜로 올라 있습니다. 이 추측은 연결
그래프의 전체 지배수에 상계를 줍니다. 그 상계는 위수에, 여그래프의 국소 독립수가
가장 작은 꼭짓점의 개수를 더한 값의 절반입니다. **이 추측이 거짓이라는 사실은
새롭지 않습니다.** Kuberwastaken/c5-k4 저장소의 전사본 감사(2026-08-12)는 WOWII
페이지가 이제 이 추측을 거짓으로 표시한다고 보고합니다. 이 감사는 2026년 7월
26일 자 페이지 메모를 인용합니다. William Weishuhn(CU Boulder)이 위반 폭이
임의로 큰 그래프 족을 찾았고, 검증에는 Codex의 도움을 받았다는 내용입니다.
우리는 그 메모를 읽을 수 없었고 그 그래프 족도 볼 수 없었습니다. 이 프로젝트의
이전 탐색 실행은 그 메모를 모르는 채로 아래의 꼭짓점 15개짜리 반례를 찾았습니다.
이 디렉터리는 Lean 반박, 무한 그래프 족이 모든 \(t\ge1\)에 대해 상계를
\(t/2\)만큼 어긴다는 Lean 증명, 그리고 꼭짓점 12개짜리 반례에 대한 Lean 증명을
더합니다. 전수 계산에 따르면 12가 반례의 가장 작은 위수입니다. 우리는 이전의
형식 증명을 찾지 못했습니다. 2026-10-25(UTC)에 수행한 검색은 Formal Conjectures,
GitHub, MathDB, Zenodo, OpenAlex, arXiv, 추적 사이트 AFTD, trureturing, c5-k4,
그리고 Wayback Machine을 대상으로 했습니다. 우리가 찾은 출처 가운데 해결을
보고하는 것은 c5-k4 감사뿐입니다. 사각지대가 하나 있습니다. 페이지 자체에 접속할
수 없고(2026-10-25 확인), 마지막 보관본은 7월 26일 자입니다. 새로움을 주장하지
않습니다. 이 작업은 아직 사람이 검토하지 않았으며, 페이지 소유자, Formal
Conjectures, MathDB를 포함해 어디에도 제출하지 않았습니다. 자세한 내용은
[선행 연구와 상태](#선행-연구와-상태)에 있습니다.

## 추측

300번 행은 목록의 "Upper bounds for Total Domination" 절에 있습니다. 마지막
캡처인 2026-07-26 캡처까지, 우리가 읽은 목록의 모든 Wayback 캡처에서 이 행의
상태는 `O`(미해결)입니다. 원문 행은 다음과 같습니다.

> If G is a simple connected graph such that n(G)> 2, then γ<sub>t</sub>(G) ≤ (1/2)*[n(G) + frequency of λ<sub>min</sub>(Ḡ)]

위 문장은
[2026-07-26 캡처](https://web.archive.org/web/20260726061534/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/all.html)에
나온 그대로입니다. 목록의 원본 주소는
<http://cms.dt.uh.edu/faculty/delavinae/research/wowII/>이며, 2026-10-25에 확인했을 때
접속되지 않았습니다. HTML 원문은 γ를 Symbol 글꼴의 문자 `g`로 씁니다. 마지막 G
위의 막대는 CSS 스타일 `text-decoration: overline`으로 그립니다. 이 행은 목록의
정의 파일
`wowIIdefs.js`([2026-07-23 캡처](https://web.archive.org/web/20260723161838/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/wowIIdefs.js))의
94, 3, 4, 31번 항목을 링크합니다. 그 내용을 풀어 쓰면 다음과 같습니다.

- **전체 지배수**(total domination number) \(\gamma_t(G)\): 모든 꼭짓점이
  \(D\)의 어떤 꼭짓점과 인접하게 되는 꼭짓점 집합 \(D\) 가운데 가장 작은 것의
  크기입니다.
- **위수** \(n(G)\): 꼭짓점의 개수입니다.
- **국소 독립수** \(\lambda(v)\): \(v\)의 이웃들이 유도하는 부분그래프의
  독립수입니다. \(\lambda_{\min}\)은 모든 꼭짓점에 걸친 국소 독립수의
  최솟값입니다.
- **여그래프** \(\bar G\): 같은 꼭짓점들 위의 그래프로, 두 꼭짓점은 \(G\)에서
  인접하지 않을 때 정확히 인접합니다.

### 읽기

- **빈도.** 목록에는 "frequency of"에 대한 별도 정의가 없습니다. 목록이 빈도를
  정의하는 곳(18번과 62번 항목, 차수 1의 빈도와 차수 \(k\)의 빈도)에서 빈도는 그
  값을 갖는 꼭짓점의 개수를 뜻합니다. 따라서 \(\lambda_{\min}(\bar G)\)의 빈도는
  다음과 같습니다.
  \[
  f(G)=\bigl|\{v:\lambda_{\bar G}(v)=\min_u\lambda_{\bar G}(u)\}\bigr|,
  \]
  여기서 \(\lambda_{\bar G}(v)\)는 \(\bar G\)에서 계산한 \(v\)의 국소
  독립수입니다.
- **여그래프.** 막대는 모든 캡처의 HTML에 들어 있고, 31번 정의도 링크되어
  있습니다. 날짜가 같고 참으로 표시된 자매 추측 301은 같은 꼴이되 "frequency of
  λ<sub>max</sub>(Ḡ)"를 씁니다. DeLaViña, Liu, Pepper, Waller, West는 이를 *Some
  conjectures of Graffiti.pc on total domination*(Congr. Numer. 185 (2007)
  81–95)의 정리 10으로 증명하는데, 빈도 대신
  \(A=\{v:\text{the local independence of }v\text{ in }\bar G\text{ is maximum}\}\)를
  써서 \(\gamma_t\le\omega+|A|\)로 나타냅니다. 우리는 300도 같은 방식으로
  읽습니다.
- **올림·내림 없음.** 이 행에는 CEIL도 FLOOR도 없으므로(목록은 이들을 쓸 때는
  명시합니다) 상계는 실수입니다.

따라서 추측은 \(n(G)\ge3\)인 모든 연결 그래프 \(G\)가 다음을 만족한다는
것입니다.
\[
\gamma_t(G)\ \le\ \tfrac12\bigl(n(G)+f(G)\bigr).
\]
\(\bar G\)의 독립집합은 \(G\)의 클릭이고, \(\bar G\)에서 \(v\)의 이웃은 닫힌
이웃 \(N_G[v]\) 바깥의 꼭짓점들입니다. 그러므로
\(\lambda_{\bar G}(v)=\omega(G-N_G[v])\)이며, 이는 \(G\)에서 \(v\)와 그 이웃들을
지우고 남은 그래프의 클릭 수입니다.

## 결과

**정리(Lean).** 이 추측은 거짓입니다. 아래 그래프 \(G_1\)은 꼭짓점이 15개이고
\(\gamma_t(G_1)=10\), \(f(G_1)=4\)이며, \(10>\tfrac12(15+4)=9.5\)입니다.

\(G_1\)은 꼭짓점 0, 1, 2, 3 위의 \(K_4\)와, 꼭짓점 0에 달린 펜던트 꼭짓점 4에서
출발해 만듭니다. 그다음 이 다섯 *허브* \(h\) 각각에 경로 \(h-(h+5)-(h+10)\)을
붙이며, \(h+5\)를 *중간* 꼭짓점, \(h+10\)을 *잎*이라 합니다. 즉 \(G_1\)은
\(K_4\)에 펜던트 꼭짓점 하나를 더한 그래프의 2-코로나입니다. 변은 다음
17개입니다.

```text
0-1 0-2 0-3 0-4 0-5 1-2 1-3 1-6 2-3 2-7 3-8 4-9 5-10 6-11 7-12 8-13 9-14
```

graph6 문자열은 `N~aA@?OA?G?O?O?G?A?`입니다. 여그래프에서의 국소 독립수는 다음
값을 가집니다.

| 꼭짓점 | 0–3 (\(K_4\)의 허브) | 4 (펜던트 허브) | 5–8 (이들의 중간 꼭짓점) | 9 (4에 달린 중간 꼭짓점) | 10–14 (잎) |
| --- | ---: | ---: | ---: | ---: | ---: |
| \(\lambda_{\bar G}(v)=\omega(G-N_G[v])\) | 2 | 3 | 3 | 4 | 4 |

따라서 \(\lambda_{\min}(\bar G)=2\)이고 이 값은 꼭짓점 네 개에서 나타나며,
상계는 \(\tfrac12(15+4)=9.5<10\)입니다.

**그래프 족.** \(t\ge0\)에 대해 \(G_t\)를, \(K_4\)와 그 \(K_4\)의 한 꼭짓점에 단
펜던트 꼭짓점 \(t\)개로 이루어진 그래프의 2-코로나라고 합시다. 꼭짓점은
\(n=3(t+4)\)개이고 \(\gamma_t(G_t)=2(t+4)\), \(f(G_t)=4\)이므로 다음이
성립합니다.
\[
2\gamma_t(G_t)=n(G_t)+f(G_t)+t .
\]
\(t\ge1\)이면 언제나 반례이며, 위반 폭 \(t/2\)는 한없이 커집니다. \(t=2\)부터는
위반 폭이 1 이상이므로 상계를 올림해도 성립하지 않습니다. \(G_2\)는 꼭짓점이
18개이고 \(\gamma_t=12\)이며 \(\lceil(18+4)/2\rceil=11\)입니다. \(t=0\)인
경우(꼭짓점 12개, \(\gamma_t=8\))는 등호가 성립합니다. Lean은 이 모든 것을 모든
\(t\)에 대해 증명합니다.

막대가 없으면, 즉 \(\lambda\)를 \(G\) 자체에서 계산하면, 국소 독립수가 가장 작은
꼭짓점은 잎이고(\(\lambda=1\)) 잎은 \(t+4\)개이며, 모든 \(G_t\)에서 등호가
성립합니다. 그 읽기에 대해서는 아무것도 주장하지 않습니다.

**정리(Lean).** 아래 그래프 \(H\)는 꼭짓점이 12개이고 \(\gamma_t(H)=7\),
\(f(H)=1\)이며, \(7>\tfrac12(12+1)=6.5\)입니다. 이 그래프는 삼각형
\(\{8,9,11\}\)과 \(\{4,5,10\}\), 그 둘 사이의 경로 \(11-3-10\), 꼭짓점 11에 달린
잎 0, 그리고 경로 \(8-6-1\)과 \(9-7-2\)로 이루어집니다. 변은 다음 13개입니다.

```text
4-5 1-6 2-7 6-8 7-9 8-9 3-10 4-10 5-10 0-11 3-11 8-11 9-11
```

graph6 문자열은 `K??I@?A?WwQE`입니다. 닫힌 이웃 \(\{3,10,11\}\)이 두 삼각형과
모두 만나는 꼭짓점은 3뿐이므로 \(\lambda_{\bar G}(3)=2\)이고, 나머지 꼭짓점 열한
개에서는 \(\lambda_{\bar G}(v)=3\)입니다.

**가장 작은 반례(계산).** 꼭짓점이 11개 이하인 연결 그래프 중 상계를 어기는 것은
없으므로, 반례의 가장 작은 위수는 12입니다. 꼭짓점이 12개인 반례는 동형을
무시하면 정확히 열 개이며, \(H\)도 그중 하나입니다. 열 개 모두 \(\gamma_t=7\),
\(f=1\)이므로 상계를 1/2만큼 어깁니다. 꼭짓점이 13개인 반례는 열 개입니다. 그중
여섯 개는 \(\gamma_t=8\), \(f=1\)이므로 상계를 1만큼 어기며, 올림한 상계에 대한
가장 작은 반례입니다. 꼭짓점이 14개인 반례는 989개입니다. 이 부분은 Lean이
아니라 계산입니다([수치 교차 검증](#수치-교차-검증) 참고).

## 증명 아이디어

1. **\(\gamma_t(G_t)=2(t+4)\).** 잎의 유일한 이웃은 그 중간 꼭짓점이므로, 모든
   전체 지배집합은 모든 중간 꼭짓점을 포함합니다. 중간 꼭짓점도 집합 안에 이웃이
   있어야 하는데, 그 이웃은 자신의 허브와 잎입니다. 따라서 집합은 허브–중간–잎
   경로 \(t+4\)개 각각과 적어도 두 꼭짓점에서 만납니다. 허브와 중간 꼭짓점들은
   그 크기의 전체 지배집합을 이룹니다.
2. **\(K_4\)의 네 허브에서 \(\lambda_{\bar G}=2\).** \(N_G[h]\)는 \(K_4\)의 네
   허브를 모두 포함하고, \(h\)가 펜던트 허브들이 달린 꼭짓점이면 펜던트 허브도
   모두 포함합니다. 따라서 \(N_G[h]\) 바깥의 어떤 두 허브도 인접하지 않으며,
   \(G-N_G[h]\)의 모든 변은 중간 꼭짓점을 포함합니다. 두 중간 꼭짓점은 결코
   인접하지 않으므로 클릭의 꼭짓점은 많아야 두 개입니다. \(N_G[h]\) 바깥에 있는
   중간 꼭짓점과 그 잎은 꼭짓점 두 개짜리 클릭을 이룹니다.
3. **나머지 모든 꼭짓점에서 \(\lambda_{\bar G}\ge3\).** \(N_G[v]\)는 \(K_4\)의
   허브를 많아야 하나 포함하므로, 그중 적어도 세 개가 \(G-N_G[v]\)에 놓이고
   이들은 서로 인접합니다.

그러므로 \(\lambda_{\min}(\bar G_t)=2\)이고 그 빈도는 정확히 4입니다.

꼭짓점 12개짜리 그래프 \(H\)의 경우, 전체 지배집합은 잎 0, 1, 2의 유일한 이웃인
11, 6, 7을 포함합니다. 또한 6의 이웃(1 또는 8), 7의 이웃(2 또는 9), 5의 이웃
\(w\)(4 또는 10), 그리고 \(\{3,4,5,10\}\)에 속하는 \(w\)의 이웃을 포함합니다. 이
일곱 꼭짓점은 서로 다르고 \(\{4,6,7,8,9,10,11\}\)은 전체 지배집합이므로
\(\gamma_t(H)=7\)입니다. \(H\)에는 \(K_4\)가 없으므로 모든 꼭짓점에서
\(\lambda_{\bar G}\le3\)입니다. \(v\ne3\)이면 \(N_H[v]\) 바깥의 삼각형에서
\(\lambda_{\bar G}(v)=3\)을 얻습니다. \(H-N_H[3]\)은 변이 있는 숲이므로
\(\lambda_{\bar G}(3)=2\)입니다.

[DETAILS.ko.md](DETAILS.ko.md)는 모든 단계와 \(\lambda_{\bar G}\)의 정확한 값을
자세히 적습니다.

## Lean 형식 증명

[`AgenticConjectures/WowiiGraphConjecture300.lean`](../../AgenticConjectures/WowiiGraphConjecture300.lean)은
mathlib이 빌드되어 있으면 약 7초 만에 컴파일됩니다. `sorry`, 추가 공리,
`native_decide`를 쓰지 않으며, 꼭짓점 15개와 12개짜리 그래프에 대한 유한 검사는
`decide +kernel`로 실행합니다. `#print axioms`는 등록된 모든 정리에 대해
`propext`, `Classical.choice`, `Quot.sound`만 보여 줍니다.

| 선언 | 내용 |
| --- | --- |
| `statement`, `not_statement` | `Prop`으로 쓴 추측과, 꼭짓점 15개짜리 그래프에서 얻는 그 부정. |
| `not_statement_graph12`, `graph12_violates` | 꼭짓점 12개짜리 그래프 \(H\)에서 다시 얻는 부정과, \(H\)에 대한 엄격한 부등식 \(\tfrac12(12+1)<7\). |
| `graph12`, `graph12_connected`, `card_graph12`, `totalDominationNumber_graph12` | 위의 변 목록 `edges12`를 쓴 `Fin 12` 위의 \(H\), 그 연결성, \(n=12\), \(\gamma_t=7\). |
| `indepNeighborsCard_compl_graph12`, `localIndependenceMin_compl_graph12`, `localIndependenceMinFreq_compl_graph12` | \(H\)에서 \(\lambda_{\bar G}\)의 모든 값(꼭짓점 3에서 2, 나머지에서 3). 따라서 \(\lambda_{\min}(\bar G)=2\)이고 빈도는 1. |
| `family`, `family_connected`, `card_family` | `Fin 3 × Fin (t + 4)` 위의 \(G_t\), 그 연결성, 꼭짓점 \(3(t+4)\)개. |
| `totalDominationNumber_family` | \(\gamma_t(G_t)=2(t+4)\). |
| `indepNeighborsCard_compl_family_hub`, `three_le_indepNeighborsCard_compl_family` | \(K_4\)의 허브에서 \(\lambda_{\bar G}=2\), 나머지에서 \(\ge3\). |
| `localIndependenceMin_compl_family`, `localIndependenceMinFreq_compl_family` | \(\lambda_{\min}(\bar G_t)=2\), 빈도는 4. |
| `family_gap`, `family_violates`, `family_violates_ceil` | \(2\gamma_t=n+f+t\). \(t\ge1\)이면 상계가, \(t\ge2\)이면 그 올림이 성립하지 않음. |
| `counterexample_adj_iff` | 꼭짓점 `(l, i)`에 번호 \(5l+i\)를 붙이면 `family 1`은 위의 꼭짓점 15개짜리 그래프임. |
| `counterexample_connected`, `card_counterexample`, `totalDominationNumber_counterexample`, `localIndependenceMin_compl_counterexample`, `localIndependenceMinFreq_compl_counterexample` | 연결성, \(n=15\), \(\gamma_t=10\), 빈도 4인 \(\lambda_{\min}(\bar G)=2\). |
| `indepNeighborsCard_compl_counterexample` | 꼭짓점 15개짜리 그래프에서 \(\lambda_{\bar G}\)의 모든 값. 일반 보조정리와 독립적으로, `decide +kernel`로 확인한 클릭 인증서와 색칠 인증서에서 얻음. |
| `card_le_indepNeighborsCard`, `indepNeighborsCard_le` | 독립집합에서 얻는 국소 독립수의 하계와, 색칠에서 얻는 상계. |

## 명제 충실성

Formal Conjectures에는 추측 300의 명제가 없으므로 `statement`는 우리가 쓴
것입니다. 이 명제는 그곳으로 옮길 수 있도록 Formal
Conjectures(google-deepmind/formal-conjectures, 커밋 `49ba26b`, Apache-2.0)의
형식을 따릅니다.

```lean
def statement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 2 < Fintype.card V →
    (totalDominationNumber G : ℝ) ≤
      (1 / 2) * ((Fintype.card V : ℝ) + (localIndependenceMinFreq Gᶜ : ℝ))
```

- **정의.** `IsTotalDominating`, `IsTotalNDominatingSet`,
  `totalDominationNumber`는
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Domination.lean`(75–91행)에서,
  `indepNeighborsCard`는 `.../SimpleGraph/Independence.lean`(40행)에서,
  `localIndependenceMin`은
  `FormalConjectures/WrittenOnTheWallII/GraphConjecture145.lean`(61행)에서 항
  그대로 옮겼습니다. 원본과 다른 점은 세 가지이며 모두 모듈 docstring에 나열되어
  있습니다. 정의들은 이 모듈의 이름공간에 있습니다. 그래서 필드 표기
  `G.IsTotalDominating D`는 `IsTotalDominating G D`로 씁니다. 그리고
  `localIndependenceMin`은 `[Nontrivial α]` 대신 `[Nonempty α]`를 가정합니다. 그
  본문에는 꼭짓점 집합이 비어 있지 않다는 것만 필요합니다.
- **원래 정의와의 대응.** `totalDominationNumber G`는 모든 꼭짓점이 그 안에
  이웃을 갖는 꼭짓점 집합 \(D\)들의 크기의 하한입니다. 꼭짓점이 두 개 이상인
  연결 그래프에는 그런 집합이 있으므로 이 값은 \(\gamma_t(G)\)입니다.
  `indepNeighborsCard G v`는 \(v\)의 이웃들이 유도하는 부분그래프의 독립수, 즉
  \(\lambda(v)\)입니다. `Gᶜ`에 적용하면 \(\lambda_{\bar G}(v)\)입니다.
  `localIndependenceMin Gᶜ`는 모든 꼭짓점에 대한 그 최솟값입니다.
- **빈도.** `localIndependenceMinFreq Gᶜ`는 우리가 정의한 것으로,
  `indepNeighborsCard Gᶜ v = localIndependenceMin Gᶜ`인 꼭짓점 \(v\)의
  개수입니다.
- **명제.** 바인더와 가정은 Formal Conjectures의 `GraphConjecture309.lean`에
  있는, \(\gamma_t\)에 대한 또 다른 WOWII 상계 `conjecture309Statement`의 것과
  같습니다. 즉 모든 유한 꼭짓점 타입, 모든 단순 그래프, `G.Connected`, 그리고
  \(n(G)>2\)를 나타내는 `2 < Fintype.card V`입니다. 상계는 \(\mathbb R\)에서
  비교하며, 올림·내림도 자연수 뺄셈도 없습니다. 바인더 `[DecidableEq V]`와
  `[DecidableRel G.Adj]`는 결론에 나타나지 않으므로 어떤 그래프도 배제하지
  않습니다. `conjecture309Statement`에서처럼 `V : Type`은 universe 0에 있으며,
  반례들의 꼭짓점 타입 `Fin 3 × Fin 5`와 `Fin 12`도 여기에 속합니다.
- **툴체인.** 이 저장소는 Lean과 mathlib v4.30.0으로 빌드하고, `49ba26b`의
  Formal Conjectures는 Lean v4.33.1로 고정되어 있습니다. 옮겨 온 정의는 여기서
  수정 없이 컴파일됩니다. 이 반박을 v4.33.1에서 컴파일해 보지는 않았습니다.

## 수치 교차 검증

인증서는 Lean 증명입니다. 독립적인 프로그램 두 개가 이를 뒷받침합니다.

- [`check_wowii300.py`](check_wowii300.py)는 Python 표준 라이브러리로 모든 것을
  정의에서부터 다시 계산합니다. \(\gamma_t\)는 꼭짓점 부분집합을 크기 순으로
  탐색해 구하고, \(\lambda_{\bar G}\)는 두 번 구합니다. 한 번은 여그래프에서의
  각 이웃 집합 안에서 \(\bar G\)의 가장 큰 독립집합으로, 또 한 번은
  \(G-N_G[v]\)의 가장 큰 클릭으로 구합니다. 기본 실행에서는 graph6 문자열이 위의
  그래프인지와 \(\gamma_t(G_1)=10\)인지 확인하고, \(t=0,\dots,4\)에 대해
  \(G_t\)를 두 읽기 모두로 확인하며, 꼭짓점 12개짜리 반례 열 개(첫 번째가
  \(H\))와 상계를 1만큼 어기는 꼭짓점 13개짜리 반례 여섯 개를 확인합니다. 약
  1초가 걸립니다.
- [`sweep_wowii300.c`](sweep_wowii300.c)는 전수 탐색용 비트마스크 C
  프로그램입니다. `geng`에서 graph6 입력을 받아 `check_wowii300.py --graph6`와
  같은 요약 행을 출력합니다.
- [`closure_wowii300.sh`](closure_wowii300.sh)는 `geng`가 모든 그래프를 나열하지
  못하는 위수에서, 꼭짓점이 \(n\)개이고 \(\gamma_t\ge k\)인 연결 그래프를 모두
  나열합니다. 고립점이 없는 생성 부분그래프의 전체 지배집합은 모두 원래 그래프의
  전체 지배집합이기도 하므로, 변을 지워도 \(\gamma_t\)는 결코 작아지지 않습니다.
  따라서 \(\gamma_t\ge k\)인 연결 그래프는 자신의 생성 트리 중 하나(이 트리도
  \(\gamma_t\ge k\)입니다)에서 출발해, \(\gamma_t\ge k\)인 그래프들만 거치며
  변을 하나씩 더해 얻을 수 있습니다. 스크립트는 트리(`gentreeg`)에서 시작해
  가능한 모든 방법으로 변을 하나 더하고(`addedgeg`), \(\gamma_t\ge k\)인
  그래프만 남기고 동형 사본을 지우는(`labelg`) 과정을 남는 것이 없을 때까지
  반복합니다.

두 프로그램은 \(2\gamma_t<n\)이면 국소 독립수 계산을 건너뜁니다. \(f\ge1\)이므로
위반이 일어나려면 \(2\gamma_t\ge n+2\), 즉
\(\gamma_t\ge\lceil n/2\rceil+1\)이어야 하기 때문입니다. 꼭짓점 11개까지는 모든
연결 그래프를 확인했고, 꼭짓점 12개에서 14개까지는
\(\gamma_t\ge\lceil n/2\rceil+1\)인 모든 연결 그래프를 확인했습니다.

| 위수 \(n\) | 확인한 그래프 수 | \(2\gamma_t\ge n+2\) | 등호 \(2\gamma_t=n+f\) | 위반 |
| ---: | ---: | ---: | ---: | ---: |
| 3–9 | 273,191 (모든 연결 그래프) | 7 | 8 | 0 |
| 10 | 11,716,571 (모든 연결 그래프) | 76 | 1 | 0 |
| 11 | 1,006,700,565 (모든 연결 그래프) | 11 | 74 | 0 |
| 12 | 889 (\(\gamma_t\ge7\)) | 889 | 10 | 10 |
| 13 | 406 (\(\gamma_t\ge8\)) | 406 | 5 | 10 |
| 14 | 39,316 (\(\gamma_t\ge8\)) | 39,316 | 663 | 989 |

꼭짓점 12개에서 14개까지의 등호 열은 확인한 그래프만 셉니다. 꼭짓점 13개에서는
\(\gamma_t=7\), \(f=1\)인 그래프도 등호를 이루겠지만, 그런 그래프는 나열하지
않았습니다.

**따라서 가장 작은 반례는 꼭짓점이 12개입니다.** \(n=11\)까지의 그래프 수는 OEIS
A001349와 일치합니다. \(n\le10\)에서는 두 프로그램의 출력이 똑같습니다. 두
프로그램의 \(\gamma_t\) 분포는 각각 \(n\le10\)과 \(n\le9\)에서 삼각 배열 OEIS
A332400(전체 지배수별 그래프 수)과 일치합니다. 이 비교에는 연결되지 않은
그래프도 받아들이는 사본을 썼습니다. \(n=11\)에서는 C 프로그램만 실행했으며,
20개 부분으로 나누어 모두 292초가 걸렸습니다(한 번에 네 부분씩 실행해 실제 시간
76초). Python 프로그램은 \(\gamma_t=7\)인 그래프 11개를 다시 확인했습니다.
위반에 가장 가까운 그래프는 \(f=4\)이며, 1/2 차이로 위반이 되지 않습니다.
closure 스크립트는 전수 탐색의 목록을 재현하며, 비교는 표준형 graph6 문자열의
집합으로 했습니다. 꼭짓점 9개에서 \(\gamma_t\ge5\)인 그래프 113개, 10개에서
\(\gamma_t\ge6\)인 76개, 11개에서 \(\gamma_t\ge6\)인 3,106개와
\(\gamma_t\ge7\)인 11개입니다. 이 스크립트가 꼭짓점 12개에서 14개까지 만든
목록은 C 프로그램과 Python 프로그램에서 똑같은 요약 행을 냅니다. 트리의 개수
551, 1,301, 3,159는 OEIS A000055와 일치합니다. [DETAILS.ko.md](DETAILS.ko.md)에
전체 표와 반례가 있습니다.

## 선행 연구와 상태

- **WOWII.** 우리가 읽은 `all.html`의 각 캡처, 즉 2010-07-17, 2016-10-09,
  2026-07-23(두 개), 2026-07-26 캡처에서 300번 행은 G 위에 막대가 있고 상태는
  `O`입니다.
  [2026-07-26 캡처](https://web.archive.org/web/20260726061534/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/all.html)가
  마지막입니다. 실제 사이트는 이제 응답 시간이 초과되는 HTTPS 호스트로
  리디렉션되므로(2026-10-25 확인), 그 이후의 메모는 그곳에서 읽을 수 없습니다.
- **Weishuhn(2026년 7월 26일).** Kuberwastaken/c5-k4는 커밋
  `2448b85`(2026-08-12)에서 감사 문서 `results/transcription_audit.md`를
  추가했습니다. 이 문서는 2026년 7월의 파싱 결과와, 2026-08-12에 페이지를
  실시간으로 가져온 결과를 비교합니다. 그때 가져온 `menu.htm`에는 "last update
  8/6/26"이라고 적혀 있었습니다. 상태 변경 표에는 300이 `F`로, "July 26 2026
  William Weishuhn (CU Boulder), family with arbitrarily large violation;
  Codex-assisted verification"이라는 메모와 함께 올라 있습니다. 가져온 페이지
  파일은 그 저장소에 없으며, 그 저장소의 파싱된 데이터는 여전히 300을 미해결로
  적고 있습니다. 이 결과에 관해 다른 것은 찾지 못했습니다. 논문, 프리프린트,
  저장소, 게시물 모두 없었습니다. 그래서 Weishuhn의 그래프 족이 무엇인지, 그것이
  \(G_t\)와 닮았는지 알지 못합니다. **따라서 추측 300의 반박은 새롭지
  않습니다.** 이 디렉터리가 더하는 것은 Lean 증명입니다.
- **그 밖의 검색(2026-10-25, UTC).**
  - Formal Conjectures: `main`(`1353892`, 20:20 UTC)의 트리에는
    `GraphConjecture300.lean`이 없습니다. 이슈와 풀 리퀘스트에서 "WOWII 300",
    `GraphConjecture300`, "Conjecture 300", "WrittenOnTheWallII 300"을
    검색했더니 번호가 300인 무관한 "Erdos 9" 이슈만 나왔습니다.
  - RhudeJJJJ의 Formal Conjectures 포크의 브랜치들: 300에 관한 것은 없습니다.
  - `GraphConjecture300`, "WOWII 300", `wowii_300`, `conjecture300`에 대한
    GitHub 코드 검색: 아무것도 없습니다.
  - MathDB, Zenodo, OpenAlex, arXiv: 아무것도 없습니다.
  - 추적 사이트 AFTD(`kb.json`)와 trureturing: 아무것도 없습니다.
  - 해결을 언급한 것은 c5-k4 감사뿐이었습니다.
- **2007년 논문.** 이 논문은 자매 상계인 추측 301을 정리 10으로
  증명합니다([읽기](#읽기) 참고). 300은 다루지 않습니다.

이 Lean 반박은 아직 사람이 검토하지 않았습니다. WOWII 관리자, Formal
Conjectures, MathDB, 그 밖의 어디에도 제출하지 않았으며, 외부 제출에는 어떤
것이든 사람의 승인이 필요합니다.

## 재현

저장소 루트에서:

```bash
lake build AgenticConjectures.WowiiGraphConjecture300
python3 scripts/check_axioms.py
```

이 디렉터리에서(전수 탐색에는 nauty와 C 컴파일러가 필요하며, 여기서는 nauty
2.9.3을 썼습니다):

```bash
python3 check_wowii300.py
for n in 3 4 5 6 7 8 9; do geng -cq $n; done | python3 check_wowii300.py --graph6
geng -cq 10 | python3 check_wowii300.py --graph6
mkdir -p build && cc -O2 -o build/sweep_wowii300 sweep_wowii300.c
for n in 3 4 5 6 7 8 9 10; do geng -cq $n; done | build/sweep_wowii300
for r in $(seq 0 19); do geng -cq 11 $r/20 | build/sweep_wowii300 || echo "part $r FAILED"; done
sh closure_wowii300.sh 10 6 | sort > build/closure10.txt
geng -cq 10 | build/sweep_wowii300 -p | awk -F'[ =]' '$1 == "NEAR" && $6 >= 6 {print $2}' | labelg -qg | sort | diff - build/closure10.txt
for n in 12 13 14; do sh closure_wowii300.sh $n $(( (n + 1) / 2 + 1 )) | build/sweep_wowii300 | grep "^n=$n:"; done | diff - closure_summary.txt
for n in 12 13 14; do sh closure_wowii300.sh $n $(( (n + 1) / 2 + 1 )) | python3 check_wowii300.py --graph6 | grep "^n=$n:"; done | diff - closure_summary.txt
```

모든 그래프에 대한 전수 탐색은 `OK`로 끝납니다. \(n=11\)의 행은 부분마다 한 번씩
출력됩니다. closure 실행은 요약 행을
[`closure_summary.txt`](closure_summary.txt)와 비교합니다. 꼭짓점 12개짜리
반례를 나열하려면 `sh closure_wowii300.sh 12 7 | build/sweep_wowii300`을
실행하고 `VIOLATION` 행을 읽으면 됩니다.

Apple 실리콘 컴퓨터에서 한 번에 한 부분씩 잰 시간은 다음과 같습니다. 기본 검사는
약 1초, Python으로 \(n\le9\)는 4초, \(n=10\)은 4분, C로 \(n\le10\)은 3초,
\(n=11\)의 20개 부분은 약 5분(부분들은 병렬로 실행할 수 있습니다), 꼭짓점 10개에
대한 closure 검사는 3초, 꼭짓점 12개에서 14개까지는 25초(C) 또는 약
2분(Python)입니다.

정의는
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)(Apache-2.0)에서
가져왔습니다. 그래프 목록은 nauty의 `geng`, `gentreeg`, `addedgeg`, `labelg`로
만들었습니다. B. D. McKay and A. Piperno, *Practical graph isomorphism, II*,
J. Symbolic Comput. 60 (2014) 94–112.
