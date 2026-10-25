[English](README.md) | **한국어**

# WOWII 그래프 추측 96

## 추측

E. DeLaViña의 *Written on the Wall II*(Graffiti.pc 프로그램이 만든 추측
목록)에 실린 추측 96은 2004년 4월 21일 날짜로 상태 `O`(미해결)로 올라
있습니다. 원문 행은 다음과 같습니다.

> If G is a simple connected graph, then α(G) ≤ 1 + minimum dist_even(v)*(maximum of λ(v) -1)

위 문장은 목록의
[2026-07-26 Wayback 캡처](https://web.archive.org/web/20260726061534/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/all.html)에
나온 그대로입니다. HTML 원문은 α와 λ를 Symbol 글꼴의 `a`와 `l`로 쓰고,
`even`을 `dist`의 아래첨자로 씁니다. 이 행이 연결한 정의(목록의
`wowIIdefs.js`,
[2023-09-01 캡처](https://web.archive.org/web/20230901203307/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/wowIIdefs.js))는
다음과 같습니다.

- \(\alpha(G)\)는 독립수입니다.
- \(\operatorname{dist}_{\mathrm{even}}(v)\)는 \(v\)로부터의 거리가 짝수인
  꼭짓점의 개수입니다. 거리 0도 짝수이므로 \(v\) 자신도 셉니다.
- \(\lambda(v)\)는 \(v\)의 이웃들이 유도하는 부분그래프의 독립수입니다.

최솟값과 최댓값은 모든 꼭짓점에 대해 취합니다. 기호로 쓰면 추측은

\[
\alpha(G)\le 1+\Bigl(\min_v\operatorname{dist}_{\mathrm{even}}(v)\Bigr)
\Bigl(\max_v\lambda(v)-1\Bigr)
\]

입니다.

### 형식 명제가 꼭짓점 두 개 이상을 가정하는 이유

글자 그대로 읽으면 이 행은 꼭짓점이 하나인 그래프 \(K_1\)에서
거짓입니다. \(K_1\)에서는 \(\alpha=1\),
\(\min\operatorname{dist}_{\mathrm{even}}=1\), \(\max\lambda=0\)이므로
우변이 \(1+1\cdot(0-1)=0<1\)이 됩니다.

그래서 Formal Conjectures의 명제는 꼭짓점이 두 개 이상이라는 가정
`[Nontrivial α]`를 추가하고, docstring에 그 이유를 적어 두었습니다. 우리
정리는 정확히 이 명제입니다. 꼭짓점이 두 개 이상인 모든 연결 그래프에서
부등식을 증명하며, \(K_1\)에 대해서는 위의 반례 외에 아무것도 주장하지
않습니다. 같은 \(K_1\) 반례는 다른 프로젝트가 먼저 형식화했습니다
([선행 연구와 상태](#선행-연구와-상태) 참고).

## 결과

**정리.** \(G\)가 꼭짓점이 두 개 이상인 유한 단순 연결 그래프이면

\[
\alpha(G)\le 1+\Bigl(\min_v\operatorname{dist}_{\mathrm{even}}(v)\Bigr)
\Bigl(\max_v\lambda(v)-1\Bigr)
\]

입니다.

이 상계는 등호가 성립하는 경우가 있습니다.

- \(m\ge1\)인 모든 별 그래프 \(K_{1,m}\)에서 등호가 성립합니다. 중심에서
  \(\operatorname{dist}_{\mathrm{even}}=1\)이고 \(\max\lambda=\alpha=m\)입니다.
- \(n\ge2\)인 모든 완전 그래프 \(K_n\)에서도 \(\alpha=\max\lambda=1\)이므로
  등호가 성립합니다.

증명은 \(\operatorname{dist}_{\mathrm{even}}\)을 최소로 하는 꼭짓점뿐 아니라
모든 루트 \(v\)에 대한 상계를 줍니다. (\(K_1\)을 포함한) 모든 연결
그래프와 모든 꼭짓점 \(v\)에 대해

\[
\alpha(G)\le\max\bigl(1,\lambda(v)\bigr)
+\sum_{\substack{u\ne v\\ d(v,u)\text{ even}}}\max\bigl(1,\lambda(u)-1\bigr)
\tag{루트별 상계}
\]

가 성립합니다.

\(\Lambda=\max_u\lambda(u)\ge2\)이면 각 항을 \(\Lambda\)로 누를 수 있습니다.
그러면 우변은
\(\Lambda+(\operatorname{dist}_{\mathrm{even}}(v)-1)(\Lambda-1)
=1+\operatorname{dist}_{\mathrm{even}}(v)(\Lambda-1)\)이 됩니다.

## 증명 아이디어

\(\Lambda=\max_u\lambda(u)\), \(E(v)=\operatorname{dist}_{\mathrm{even}}(v)\)로
쓰고, \(d\)는 그래프 거리입니다.

1. 꼭짓점이 두 개 이상이면 모든 꼭짓점에 이웃이 있습니다. 따라서 모든
   \(u\)에 대해 \(\lambda(u)\ge1\)이고 \(\Lambda\ge1\)입니다.
2. \(\Lambda=1\)이고 서로 이웃하지 않는 두 꼭짓점이 있다고 합시다. 그러면
   어떤 꼭짓점 \(x\)에 대해 거리가 정확히 2인 꼭짓점 \(w\)와 둘의 공통 이웃
   \(y\)가 있습니다. \(\{x,w\}\)는 \(y\)의 이웃 안에서 독립이므로
   \(\lambda(y)\ge2\)가 되어 모순입니다. 따라서 \(G\)는 완전 그래프이고,
   \(\alpha=1\)은 우변과 같습니다.
3. \(\Lambda\ge2\)라고 합시다. 루트 \(v\)와 최대 독립집합 \(I\)를 고정합니다.
   \(x\in I\)는 \(d(v,x)\)가 짝수이면 자기 자신으로 보내고, 홀수이면 BFS
   부모, 즉 \(v\)에 한 걸음 더 가까운 이웃으로 보냅니다. 상은 모두 \(v\)로부터
   짝수 거리에 있습니다. 이제 각 상의 올(fibre), 즉 그 상으로 보내지는
   원소들의 집합 크기로 \(\lvert I\rvert\)를 셉니다.
   - \(u\in I\) 위의 올은 \(\{u\}\)입니다. 올에 다른 원소가 있다면 그것은
     \(u\)와 이웃한 \(I\)의 원소가 되기 때문입니다.
   - \(u\notin I\) 위의 올은 \(u\)의 이웃으로 이루어진 독립집합입니다.
     따라서 원소가 많아야 \(\lambda(u)\)개입니다.
   - \(u\notin I\)이고 \(u\ne v\)이면 더 잘할 수 있습니다. \(u\)의 부모는
     \(v\)로부터 거리 \(d(v,u)-1\)에 있고, 올은 거리 \(d(v,u)+1\)에 있습니다.
     그래서 부모는 올의 어떤 꼭짓점과도 이웃하지 않고, 부모를 추가해도
     독립집합입니다. 따라서 올의 원소는 많아야 \(\lambda(u)-1\)개입니다.

   짝수 거리에 있는 \(E(v)\)개의 꼭짓점에 대해 더하면 루트별 상계를
   얻습니다. 그 상계는 많아야
   \(\Lambda+(E(v)-1)(\Lambda-1)=1+E(v)(\Lambda-1)\)입니다. \(E(v)\)가 최소인
   \(v\)를 택하면 정리가 증명됩니다.

[DETAILS.ko.md](DETAILS.ko.md)에 각 단계와 그 단계를 증명하는 Lean
보조정리를 적었습니다.

## Lean 형식 증명

[`AgenticConjectures/WowiiGraphConjecture96.lean`](../../AgenticConjectures/WowiiGraphConjecture96.lean)이
upstream 정리를 증명합니다. `sorry`, 추가 공리, `native_decide`를 쓰지
않으며, `#print axioms`는 `propext`, `Classical.choice`, `Quot.sound`만
보여 줍니다.

| 선언 | 내용 |
| --- | --- |
| `conjecture96` | `[Nontrivial α]`와 `G.Connected` 아래의 upstream 명제 원문 그대로. |
| `statement`, `statement_holds` | 같은 명제를 모든 유한 꼭짓점 타입에 대해 양화한 것과 그 증명. |
| `indepNum_le_perRoot` | 모든 연결 그래프와 모든 루트에 대한 루트별 상계. |
| `indepNum_le_of_two_le` | 모든 \(\lambda(u)\le L\)이고 \(L\ge2\)일 때 \(\alpha\le1+E(v)(L-1)\). |
| `indepNum_le_one` | 모든 \(\lambda(u)\le1\)일 때 \(\alpha\le1\). |
| `one_le_indepNeighborsCard` | 꼭짓점이 두 개 이상일 때 \(\lambda(u)\ge1\). |
| `exists_parent`, `exists_dist_two` | BFS 부모의 존재와 거리가 정확히 2인 꼭짓점의 존재. |
| `card_le_indepNeighborsCard`, `two_le_indepNeighborsCard` | 이웃으로 이루어진 독립집합이 \(\lambda\)의 하계를 줌. |

## 명제 충실성

- **정의.** `distEven`과 `indepNeighborsCard`는 커밋 `c094b97`의
  FormalConjecturesForMathlib에서 항 그대로 옮겼습니다. 원래 위치는
  `Combinatorics/SimpleGraph/VertexDistance.lean`의 396행과
  `Combinatorics/SimpleGraph/Independence.lean`의 40행이며, 같은 section
  변수를 씁니다. 다른 점은 이름공간뿐입니다. `SimpleGraph`가 아니라
  `AgenticConjectures.WowiiGraphConjecture96`에 있습니다.
- **원문 정의와의 대응.** `distEven G v`는 `Even (G.dist v w)`인 `w`를
  세므로 `v` 자신도 포함합니다. `indepNeighborsCard G v`는 열린 이웃
  `G.neighborSet v`가 유도하는 부분그래프의 독립수입니다. mathlib의
  `G.dist`는 도달할 수 없는 쌍에 대해 0이지만, \(G\)가 연결이므로 보통의
  거리와 같습니다.
- **명제.** `conjecture96`의 본문은 upstream 정리를 글자 그대로 옮긴
  것입니다. `@[category research open, AMS 5]` 속성과
  `module`/`public`/`@[expose]` 키워드만 빼고, `FormalConjecturesUtil`
  대신 `Mathlib`을 import합니다.
- **툴체인.** 이 저장소는 Lean과 mathlib `v4.30.0`으로 빌드하고, `c094b97`의
  Formal Conjectures는 `v4.33.1`(mathlib `0df444a`)을 고정합니다. 명제가 쓰는
  그래프 선언(`indepNum`, `IsNIndepSet`, `IsIndepSet`, `dist`, `edist`,
  `Walk`, `Walk.length`, `Reachable`, `Connected`, `induce`, `neighborSet`)은
  두 판에서 글자 그대로 같습니다. `SimpleGraph`의 `symm` 필드는
  `Symmetric Adj`에서 그와 동치인 `Std.Symm Adj`로 바뀌었고,
  `SimpleGraph.comap`은 증명 필드만 바뀌었습니다. 따라서 명제의 뜻은 두
  판에서 같지만, 증명은 `v4.30.0`에서만 컴파일했습니다.
- **꼭짓점 두 개 이상.** `[Nontrivial α]`는 위에서 설명한 upstream의
  의도적인 제한입니다. 이 가정 덕분에 `Finset.univ.image …`가 비어 있지
  않으므로, `min'`과 `max'`는 모든 꼭짓점에 대한 최솟값과 최댓값입니다.
- **뺄셈.** 부등식은 \(\mathbb R\)에서 진술되므로 \(\max\lambda-1\)은 원문과
  같이 부호 있는 뺄셈입니다. 증명은 \(\max\lambda\ge1\)을 보이므로, 이는
  증명 내부에서 쓰는 자연수 뺄셈과 같습니다. 루트별 상계의
  \(\lambda(u)-1\)은 \(\max(1,\cdot)\) 안의 자연수 뺄셈이어서 절단이 결과에
  영향을 주지 않습니다.
- **기계적 검사.**
  [`upstream_statement_check.lean`](upstream_statement_check.lean)은 두 정의를
  upstream 이름공간 `SimpleGraph`에 다시 선언하고, upstream 정리를 그
  이름공간 `WrittenOnTheWallII.GraphConjecture96`에서 다시 진술한 뒤 우리
  `conjecture96`으로 닫습니다. elaboration이 upstream 상수를 우리 상수로
  펼쳐야 하므로, 어긋남이 있으면 이 파일이 실패합니다. 출력은 표준 공리
  세 개입니다. 이 파일은 라이브러리에서 import하지 않습니다.

## 수치 교차 검증

인증서는 Lean 증명입니다. [`verify_wowii96.py`](verify_wowii96.py)는 추측과
루트별 상계를 Python 표준 라이브러리만으로 무차별 대입하여 독립적으로 다시
검사합니다.

| 입력 | 그래프 수 | (그래프, 루트) 쌍 | 추측 등호 | 루트별 등호 | 시간 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 기본(CI) 모드: \(n=2,\dots,6\)의 모든 레이블 그래프와 별 그래프 \(K_{1,m}\), \(m\le12\) | 27,487 | 164,120 | 9,455 | 45,622 | 0.7초 |
| `geng -c`, \(n=2,\dots,9\) | 273,192 | 2,445,436 | 14,917 | 73,458 | 22초 |
| `geng -c`, \(n=10\), 세 부분으로 나눔 | 11,716,571 | 117,165,710 | 279,788 | 1,188,438 | 실제 9.1분, CPU 23.2분 |

- 어느 실행에서도 위반은 없었고, 최소 여유는 모두 0이었습니다.
- 차수별 레이블 그래프 수는 OEIS A001187과 일치하고, `geng` 총수는
  A001349와 일치합니다.
- 기본 모드는 별 그래프에서의 등호와 원문 행의 \(K_1\) 반례도 확인합니다.
- 두 번째 구현인 C 프로그램 [`check_wowii96.c`](check_wowii96.c)도 두
  `geng` 입력에서 같은 그래프 수, 쌍 수, 등호 개수를 냅니다. 루트별 등호
  개수는 \(n\le9\)에서 73,458, \(n=10\)에서 1,188,438입니다. 이 프로그램은
  Python 스크립트와 코드를 공유하지 않습니다. 자체 graph6 파서를 쓰고,
  독립수를 분기로 구합니다. 실행 시간은 \(n\le9\)에서 0.2초, \(n=10\)에서
  6초이며, `--selftest`는 \(K_1\), 별 그래프, Petersen 그래프를 포함한 작은
  그래프에서 손으로 계산한 불변량을 확인합니다.

## 선행 연구와 상태

- **WOWII.** 목록의
  [2026-07-26 캡처](https://web.archive.org/web/20260726061534/http://cms.dt.uh.edu/faculty/delavinae/research/wowII/all.html)에서
  96번 행의 상태는 `O`입니다. 해결된 추측 목록 두 곳
  ([resolved.htm](https://web.archive.org/web/20260723211227/http://cms.uhd.edu/faculty/delavinae/research/wowII/resolved.htm)과
  [resolvedT.htm](https://web.archive.org/web/20260723211215/http://cms.uhd.edu/faculty/delavinae/research/wowII/resolvedT.htm),
  2026-07-23 캡처) 어디에도 나오지 않습니다.
- **Formal Conjectures.** `conjecture96`은
  [google-deepmind/formal-conjectures#3796](https://github.com/google-deepmind/formal-conjectures/pull/3796)으로
  추가되었고 2026-10-23에 병합되었습니다. `c094b97`과 `main` `37f0808`
  (2026-10-24)에서 `research open`으로 표시되어 있고 `sorry`로 닫혀
  있습니다. 그 저장소의 이슈와 풀 리퀘스트에서 `conjecture96`과
  `GraphConjecture96`을 검색한 결과는 없었습니다(2026-10-25 UTC).
- **txmy/ultra-mathematician.**
  [txmy/ultra-mathematician](https://github.com/txmy/ultra-mathematician/tree/d52f81ad64dfc77e9a89dee8ae97db983ac6d5f7/runs/run-2026-07-25-001/tasks/audit-wowii-96-final)의
  2026-07-25 실행은 원문 행에 대한 \(K_1\) 반례를 형식화했습니다. 그 감사
  문서는 당시 위 풀 리퀘스트에 있던 `[Nontrivial α]` 판이 증명되지 않았다고
  적고 있습니다. 꼭짓점이 두 개 이상인 그래프는 다루지 않습니다.
- **Kuberwastaken/c5-k4.** 이 저장소는 추측 96을 그래프 하나에서만
  계산하고, 그 그래프에서 성립한다고 기록합니다.
- **문헌.** arXiv, Zenodo/OpenAlex, GitHub 코드에서 `GraphConjecture96`,
  `dist_even`, "Written on the Wall"을 검색했으나 증명을 찾지
  못했습니다(2026-10-25 UTC).

증명을 찾지 못했다는 사실이 새로움을 입증하지는 않으며, 새로움을 주장하지도
않습니다. 이 증명과 형식화는 아직 사람이 검토하지 않았습니다. AI 모델이
만들었으며, Lean 커널과 수치 교차 검증으로만 확인했습니다. Formal Conjectures,
WOWII 관리자, 그 밖의 어디에도 제출하지 않았으며, 외부 제출에는 사람의
승인이 필요합니다.

## 재현

저장소 루트에서:

```bash
lake build AgenticConjectures.WowiiGraphConjecture96
lake env lean problems/wowii-graph-conjecture-96/upstream_statement_check.lean
python3 scripts/check_axioms.py
```

mathlib이 빌드되어 있으면 모듈 컴파일은 약 4초, upstream 검사는 약 4초가
걸립니다.

이 디렉터리에서(`geng` 실행에는 nauty, `check_wowii96.c`에는 C 컴파일러가
필요합니다):

```bash
python3 verify_wowii96.py
for n in 2 3 4 5 6 7 8 9; do geng -cq $n; done | python3 verify_wowii96.py --graph6
for k in 0 1 2; do geng -cq 10 $k/3 | python3 verify_wowii96.py --graph6; done
cc -O2 -o /tmp/check_wowii96 check_wowii96.c && /tmp/check_wowii96 --selftest
for n in 2 3 4 5 6 7 8 9; do geng -cq $n; done | /tmp/check_wowii96
geng -cq 10 | /tmp/check_wowii96
```

[upstream 스냅샷](upstream/README.md)에 Formal Conjectures 원본을 그대로
보존했습니다.
