[English](DETAILS.md) | **한국어**

# 수학적 세부 사항: 유한 마그마에서의 등식 677과 등식 255

이 문서는 이 디렉터리의 탐색이 사용하는 모든 환원, 절(clause), 전파 규칙의
정당성을 설명한다. Lean 이름은
[`Etp677Implies255Finite.lean`](../../AgenticConjectures/Etp677Implies255Finite.lean)을
가리키며, 인용한 사실은 모두 그 파일에서 `sorry` 없이 증명되어 있다.

표기: $(M,\diamond)$는 마그마이고 $L_y(x)=y\diamond x$이다.

- E677: 모든 $x,y$에 대해 $x=y\diamond(x\diamond((y\diamond x)\diamond y))$.
- E255: 모든 $x$에 대해 $x=((x\diamond x)\diamond x)\diamond x$. "$x$에서의
  E255"는 하나의 고정된 $x$에 대한 이 등식을 뜻한다.
- *반례 모델*이란 E677을 만족하지만 E255를 만족하지 않는 유한 마그마이다.

## 1. 유한 E677 마그마의 성질

$M$이 유한하고 E677을 만족한다고 하자.

| | 성질 | Lean |
|---|---|---|
| F1 | 모든 $L_y$는 전단사이고 $L_y^{-1}(x)=x\diamond((y\diamond x)\diamond y)$ | `leftMul_surjective`, `leftMul_bijective` |
| F2 | $y\diamond c=x$이면 $x\diamond((y\diamond x)\diamond y)=c$ | `inv_form` |
| F3 | $y\diamond c=x$이고 $x\diamond b=c$이면 $(y\diamond x)\diamond y=b$ | `inv_form₂` |
| F4 | $y\diamond x=x$이면 $y=(x\diamond x)\diamond x$ | `fixer_unique` |
| F5 | $x$에서 E255가 성립하는 것은 어떤 $y$에 대해 $y\diamond x=x$인 것과 동치 | `eq255_at_iff_exists_fixer` |
| F6 | $x$에서 E255가 실패하면 모든 $y,z$에 대해 $y\diamond x\ne x$, $x\diamond(z\diamond x)\ne z$, $x\diamond(y\diamond y)\ne y$ | `fixer_free_of_not255`, `ne_of_not255_v`, `ne_of_not255_vii` |

F1은 유한성(전사이면 단사)을 사용한다. F4–F6은 ETP 블루프린트의 등식 677
장에 있는 Lemma 13.1–13.2이다.

## 2. 한 원소로 생성되는 반례 모델로의 환원

$M$이 반례 모델이고 $x$에서 E255가 실패하면, $x$가 생성하는 부분마그마
$\langle x\rangle$은 E677을 만족하고 원소가 $|M|$개 이하이며 $x$로 생성되고,
그 안에서도 $x$에서 E255가 실패한다(`exists_generated_countermodel`; 동치
형태는 `not_statement_iff`). 따라서

$$
\text{원소가 } N \text{개 이하인 반례 모델이 없다}
\iff
\begin{array}{l}\text{모든 } n\le N \text{에 대해, 한 원소 } g \text{로 생성되고 } g \text{에서 E255가}\\
\text{실패하는 } n \text{원소 E677 마그마가 없다.}\end{array}
$$

왼쪽이 `noCountermodelUpTo N`이다. 아래의 모든 탐색은 크기 $n$을 고정해서
돌아가므로 모든 $n\le N$에 대해 실행해야 한다.

## 3. 표준 라벨링

$(M,g)$를 $g$로 생성되는 크기 $n$의 마그마라 하자. $g$에 라벨 $0$을 붙인다.
$0,\dots,k$까지 라벨이 붙었을 때($k<n-1$) 집합 $\{0,\dots,k\}$는
$\diamond$에 대해 닫혀 있지 않다($g$를 포함하는 닫힌 집합은 $M$ 전체이므로).
따라서 $\{0,\dots,k\}^2$의 어떤 쌍은 곱에 아직 라벨이 없다. 행 우선 순서로
그런 첫 쌍을 골라 그 곱에 라벨 $k+1$을 붙인다. 라벨을 붙인 마그마의 곱셈표
$T$는 다음 성질을 가진다.

> (C) 모든 $k\le n-2$에 대해 $\{0,\dots,k\}^2$의 어떤 쌍은 $T$ 값이
> $k$보다 크고, 그런 쌍 가운데 행 우선 순서로 첫 번째 쌍의 값은 정확히
> $k+1$이다.

(C)를 만족하는 표는 모두 $0$으로 생성되며, 라벨링은 단계마다 강제되므로
(C)를 만족하는 표와 $g$로 생성되는 점 붙은 마그마 $(M,g)$의 동형류는 일대일로
대응한다. 부정적 결과에는 모든 $(M,g)$가 (C)를 만족하는 표를 가진다는 사실만
필요하고, general 모드의 개수 세기에는 유일성도 쓰인다.

## 4. SAT 인코딩 ([`search/gen_cnf.py`](search/gen_cnf.py))

변수는 $\{0,\dots,n-1\}$ 위의 $p(x,y,v)\iff x\diamond y=v$, 보조 변수
$q(x,y,b)$, $r(x,y,b)$, 그리고 (C)를 위한 순서 변수이다. 절은 다음과 같다.

1. 모든 칸은 정확히 하나의 값을 가진다.
2. 모든 행은 순열이다(F1).
3. $y\diamond x=a\wedge a\diamond y=b\Rightarrow q(x,y,b)$.
4. $q(x,y,b)\wedge x\diamond b=c\Rightarrow y\diamond c=x$ (E677).
5. $q(x,y,b)\wedge y\diamond c=x\Rightarrow x\diamond b=c$ (F2).
6. $y\diamond c=x\wedge x\diamond b=c\Rightarrow r(x,y,b)$.
7. $y\diamond x=a\wedge r(x,y,b)\Rightarrow a\diamond y=b$ (F3).
8. anti-E255 모드에서만: $y\diamond 0\ne 0$, 그리고
   $v\diamond 0=w\Rightarrow 0\diamond w\ne v$ ($0$에서의 F6).
9. (C): 각 $k$마다 $\{0,\dots,k\}^2$의 어떤 쌍의 값이 $k$보다 크다는 절이
   하나 있고, 변수 $e_t$("행 우선 순서에서 위치 $t$보다 앞선 어떤 쌍의 값이
   $k$보다 크다")는 $\text{value}(t)\ge k+2\Rightarrow e_t$와
   $e_t\Rightarrow e_{t-1}\vee\text{value}(t-1)>k$를 만족하며 $e_0$은
   거짓이다.

$g$로 생성되고 $g$에서 E255가 실패하는 크기 $n$의 E677 마그마가 있다면, 그
마그마의 (C) 표에 $q(x,y,b):=[(y\diamond x)\diamond y=b]$,
$r(x,y,b):=[\exists c\; y\diamond c=x\wedge x\diamond b=c]$와 의도한 $e_t$를
더한 할당은 모든 절을 만족한다. 따라서 크기 $n$의 anti 모드 CNF가 UNSAT이면
그런 마그마는 없다. 반대로 절 1–4가 표에 E677을 강제하므로, general
모드(절 8 제외)에서 모델의 $p$ 부분은 E677을 만족하는 (C) 표와 정확히
일치한다. [`search/enum_sat.py`](search/enum_sat.py)는 $p$에 대한 차단 절로
이를 모두 나열한다.

## 5. 전수 DFS ([`search/dfs677.cpp`](search/dfs677.cpp))

이 프로그램은 정의역을 가진 부분 곱셈표를 채워 나간다. 지금까지 만든 가장
큰 라벨을 $k$라 하자. 할당된 칸과 값은 항상 $\{0,\dots,k\}$ 안에 있다.
분기는 $k+1$ 이하의 값만 쓰고(값 $k+1$은 다음 라벨을 만든다), 전파로 생기는
할당은 행, 열, 값을 모두 이미 할당된 칸에서 가져오기 때문이다.

- **정적 단계** ($k<n-1$): $\{0,\dots,k\}^2$에서 행 우선 순서로 첫 번째
  미할당 칸을 골라, 정의역 중 $k+1$ 이하인 값으로 분기한다.
  $\{0,\dots,k\}^2$가 모두 할당되었다면 $\{0,\dots,k\}$가 닫혀 있으므로 그
  가지는 버린다. (C)를 만족하는 표 $T$의 경로에서 $\{0,\dots,k\}^2$의 앞선
  칸들은 $k$ 이하의 값을 가지므로, (C)에 의해 분기 칸의 값은 $k+1$ 이하이고
  $T$는 잘려 나가지 않는다.
- **동적 단계** ($k=n-1$): 정의역이 가장 작은 칸에서 분기한다.
- **전파**: E677 사슬 $a=y\diamond x$, $b=a\diamond y$, $c=x\diamond b$,
  $y\diamond c=x$를 F1–F3을 써서 $c'=L_y^{-1}(x)$, $b'=L_x^{-1}(c')$와 함께
  앞뒤로 전파한다. 행은 순열이고(F1; 모든 라벨이 생긴 뒤에는 hidden single
  포함), $x$의 고정자는 유일하며 $(x\diamond x)\diamond x$와 같다(F4).
  anti 모드에서는 F6의 세 부등식이 $0$에서 성립한다. 각 규칙은 제약을
  만족하는 (C) 표가 가질 수 없는 값만 제거한다.
- 완성된 표는 개수에 넣기 전에 E677(그리고 anti 모드에서는 $0$에서 E255가
  실패함)을 다시 검사한다.
- **분할**: 탐색은 결정적이다. `split P p depth d`를 주면 깊이 $d$의 노드에
  DFS 순서로 번호를 매기고, 부분 $p$는 번호가 $p \pmod P$와 합동인 노드만
  탐색한다. $P$개의 부분이 트리 전체를 덮는다. `split2`는 한 부분을 더 깊은
  수준에서 같은 방식으로 다시 나눈다.

DFS와 SAT 인코딩은 위의 수학만 공유하고 코드는 공유하지 않는다. $n\le 10$에서
둘 다 anti 모드 해가 없다고 보고하며, $n\le 9$에서 general 모드 표가
일치한다.

## 6. 군 위의 평행이동 불변 마그마

$G$를 유한군, $f:G\to G$라 하자. 연산 $x\diamond y=x\,f(x^{-1}y)$에서는
$G$의 모든 왼쪽 평행이동이 자기동형사상이 된다(`tinv_translate`). Lean에서
다음을 증명했다.

- E677은 모든 $x$에 대해 $x=f\bigl(x\,f(x^{-1}u)\bigr)$인 것과 동치이다.
  여기서 $u=f(x)\,f(f(x)^{-1})$이다(`tinv_eq677_iff`).
- E677이 성립하면 E255는 $f$가 고정점을 갖는 것과 동치이다
  (`tinv_eq255_iff`).
- 고정점 없는 해는 명제를 반증한다(`not_statement_of_tinv`).
- 고정점 없는 해는 모두 전단사이고 $f(z\,f(z^{-1}))\ne z$,
  $f(y\,f(e))\ne y$를 만족한다(`tinv_cnf_constraints`).

**CNF** ([`tinv/tinv_cnf.py`](tinv/tinv_cnf.py)). 변수는 $F(z,v)\iff
f(z)=v$이고, 보조 변수 $U(x,u)$("$u=f(x)f(f(x)^{-1})$")와 $R(x,u)$가 있다.
절은 다음과 같다. $f$는 고정점 없는 순열이다. $U$는 정의에 의해 함의된다.
$c=x^{-1}u$일 때 $U(x,u)\wedge f(c)=d\Rightarrow f(xd)=x$(함수 방정식),
$U(x,u)\wedge f(xd)=x\Rightarrow f(c)=d$(단사성),
$f(c)=d\wedge f(xd)=x\Rightarrow R(x,u)$와
$f(x)=a\wedge R(x,u)\Rightarrow f(a^{-1})=a^{-1}u$(F3과 같은 단사성 논증),
그리고 `tinv_cnf_constraints`의 두 부등식. 고정점 없는 해에 $U$, $R$의 의도한
값을 주면 모든 절을 만족한다.

**대칭 깨기.** $\varphi\in\operatorname{Aut}(G)$에 대해 켤레
$\varphi\circ f\circ\varphi^{-1}$도 해이고(`tinv_conj_solution`), 이것이
고정점을 갖는 것은 $f$가 고정점을 갖는 것과 동치이다
(`tinv_conj_fixed_iff`). 켤레의 $e$에서의 값은 $\varphi(f(e))$이므로
$a=f(e)$가 자신의 $\operatorname{Aut}(G)$-궤도에서 (우리의 번호로) 가장 작은
원소라고 가정할 수 있다. 다시 $a$의 안정자로 켤레를 취하면 $f(e)=a$는
유지되고 $f(a)$는 $\operatorname{Stab}(a)$-궤도 안에서 움직이므로
$b=f(a)$가 그 궤도의 가장 작은 원소라고 가정할 수 있다. 각 경우는 단위 절
$f(e)=a$, $f(a)=b$를 더한다($f$에 고정점이 없으므로 $a=e$나 $b=a$인 경우는
뺀다). GAP에서 가져오는 것은 $\operatorname{Aut}(G)$의 *생성원*뿐이다.
[`tinv/export_cases.py`](tinv/export_cases.py)는 각 생성원이 내보낸
케일리 표의 자기동형사상인지 확인하고, 궤도와 안정자 생성원(Schreier 보조
정리)을 직접 계산한다. GAP이 생성원을 덜 돌려주더라도 경우 분할이 약해질
뿐 건전성은 깨지지 않는다. [`tinv/test_sb.py`](tinv/test_sb.py)는 general
모드에서 위수 19 이하의 모든 군(50개)에 대해, 경우별 해들의
$\operatorname{Aut}(G)$-켤레가 정확히 전체 해 집합임을 확인한다.

## 7. 무엇을 신뢰하는가

- **DRAT 상한($n\le 10$)**: `gen_cnf.py`와 §2–§4의 논증(쓰인 사실은 Lean으로
  검사됨), 그리고 `drat-trim`. 솔버는 신뢰하지 않는다.
- **DFS 상한($n\le 10$)**: C++ 프로그램과 §5의 논증이며 인증서는 없다.
  $n\le10$에서 독립적인 두 번째 방법이다. $n=11$ 실행은 부분 트리 27개 중
  3개가 끝나지 않은 채 중단되었으므로 아무것도 주장하지 않는다.
- **평행이동 불변 탐색**: CaDiCaL의 UNSAT 답(증명은 보관하지 않음), GAP
  SmallGroups 라이브러리의 군 표(각각 `tinv_cnf.py`가 군인지 확인함), 그리고
  §6의 경우 분할.
