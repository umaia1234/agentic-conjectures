[English](DETAILS.md) | **한국어**

# CRIM 멜드, 홀짝 자기켤레 분할, 미제르 규칙: 증명 상세

여기서 다루는 추측들은 Ina Bašić, Eric Gottlieb, Matjaž Krnc의 *CRIM: A Natural Game on Integer
Partitions*([arXiv:2606.16828](https://arxiv.org/abs/2606.16828)) 5절에 실린 것입니다.

3–5절의 정리는 모두 [`CrimPselfMeld.lean`](../../AgenticConjectures/CrimPselfMeld.lean)에서
커널로 검증됩니다(`sorry`, 추가 공리, `native_decide` 없음). 본문은 같은 증명을 종이 위에서
다시 적고, 단계마다 해당하는 Lean 선언의 이름을 붙입니다. 두 증명 모두 Zijian Zeng의 경계 단어에
의한 $\mathcal P$-위치 분류(심사 전 프리프린트, 2절)에 기대며, 이 분류는
[crim-hook-stacks](../crim-hook-stacks/DETAILS.ko.md#7-경계-단어-분류로부터-conjmain)가
형식화했습니다. 5절은 미제르 $\mathcal P$-위치의 분류와 논문의 conj:hookswap의 한 방향을
증명하며, 다른 방향은 증명하지 못했습니다. 6절은 계산을 설명하며, 계산은 증거일 뿐입니다. 이 작업은 사람이 검토하지 않았고, 새로움은 주장하지 않으며, 어디에도 제출하지 않았습니다.

## 1. 정의와 명제

CRIM의 위치는 $\lambda_1\ge\dots\ge\lambda_r\ge1$인 정수 분할 $\lambda=[\lambda_1,\dots,\lambda_r]$이며
$[\,]$도 포함합니다. $\ell(\lambda)=r$로 쓰고, $i>r$이면 $\lambda_i=0$으로 둡니다. 한 수는 영
도형에서 행 하나나 열 하나를 지우고 남은 조각을 다시 붙입니다. 정상 규칙을 따르므로 $[\,]$은
$\mathcal P$-위치("지는 위치")이고, 어떤 위치가 $\mathcal P$일 필요충분조건은 모든 수가
$\mathcal N$-위치로 가는 것입니다. Lean 정의(`IsPartition`, `part`, `moves`, `IsP`)는
crim-hook-stacks의 것입니다([그 문서의 §1.1](../crim-hook-stacks/DETAILS.ko.md#11-해석)).

논문은 다음 개념을 씁니다.

- **멜드**(§2.1, TeX 334행): $\mu=[\mu_1,\dots,\mu_k]$와 $\lambda=[\lambda_1,\dots,\lambda_m]$에
  대해
  \[
  \mu\diamond\lambda=[\mu_1+\lambda_1,\dots,\mu_1+\lambda_m,\mu_1,\mu_2,\dots,\mu_k].
  \]
  논문은 $\diamond$가 결합법칙을 만족하고 항등원이 $[\,]$임을 언급합니다.
- **두꺼운 훅**(§2.2, 356–357행): $r>a\ge2$, $c>b\ge2$인 $\Gamma^{a,b}_{r,c}=[c^a,b^{r-a}]$.
- **훅**: $\Gamma_{r,c}=[c,1^{r-1}]$. 그 켤레는 $\Gamma_{c,r}$입니다.
- **켤레**: $\lambda'_k$는 $k$ 이상인 부분의 개수입니다.
- **홀짝 자기켤레**(1141행): 모든 $k$에 대해 $\lambda_k\equiv\lambda'_k\pmod 2$.
- **더피 길이와 스택**(1095–1105행): $d(\lambda)$는 $d\le\lambda_d$인 가장 큰 $d$입니다.
  $\mu=[\mu_1,\dots,\mu_k]$와 $d=d(\lambda)$에 대해, $1\le i\le k$에서 $\lambda_{d+i}=d$이고
  $\lambda_d\ge d+\mu_1$일 때 스택 $\lambda\lhd\mu$가 정의되며,
  \[
  \lambda\lhd\mu=[\lambda_1,\dots,\lambda_d,\lambda_{d+1}+\mu_1,\dots,\lambda_{d+k}+\mu_k,
  \lambda_{d+k+1},\dots,\lambda_r]
  \]
  입니다. 논문은 스택 연산이 "is associative and can be extended to multiple partitions"라고
  덧붙입니다.
- **미제르 그런디 값과 콘웨이 쌍**(§2, 422–424행): $G^-$는 스프라그–그런디 값 $\mathrm{sg}$와
  같은 방식으로 정의하되 끝 위치의 값을 $1$로 두며,
  $\mathrm{cp}(\lambda)=(\mathrm{sg}(\lambda),G^-(\lambda))$입니다.

추측(1071–1073행, 1143–1146행):

> A meld of losing thick hooks is losing.
>
> **conj:pself.** A parity self-conjugate partition is in $\mathcal N$ if and only if it is the
> stack of odd self-conjugate hooks and $[1]$.

### 1.1 해석

| 항목 | 해석 | Lean |
|---|---|---|
| 위치, 수, 지는 위치 | crim-hook-stacks와 같음; 정상 규칙, $[\,]$은 $\mathcal P$ | `IsPartition`, `moves`, `IsP` |
| 멜드 | 논문의 공식; $\mu=[\,]$이면 $\mu_1=0$ | `meld` |
| 두꺼운 훅 | $r>a\ge2$, $c>b\ge2$인 $[c^a,b^{r-a}]$ | `thickHook`, `ThickParams`, `IsThickHook` |
| 지는 두꺼운 훅들의 멜드 | $\mathcal P$인 두꺼운 훅들의 유한 멜드, 괄호 묶기는 임의; 조각 하나와 빈 멜드 $[\,]$ 포함 | `Melds`, `melds_iff` |
| 멜드 추측 | 그런 멜드는 모두 $\mathcal P$ | `meldConjecture` |
| $\lambda'_k$ | $k$ 이상인 부분의 개수 | `conjPart` |
| 홀짝 자기켤레 | 모든 $k\ge1$에서 $\lambda_k\equiv\lambda'_k\pmod2$, 끝을 넘으면 양쪽 모두 $0$ | `ParitySelfConj` |
| 홀수 자기켤레 훅 | $r$이 홀수인 $\Gamma_{r,r}$ | `hook r r`, `Odd r` |
| 홀수 자기켤레 훅들과 $[1]$의 스택 | $\Gamma_{r_1,r_1}\lhd(\Gamma_{r_2,r_2}\lhd(\cdots\lhd(\Gamma_{r_j,r_j}\lhd[1])))$, $j\ge0$, $r_i$ 홀수, 모든 스택이 정의됨; 괄호 묶기는 결과에 영향 없음 | `OddHookStack`; `HookTree`, `exists_hookTree_iff` |
| 스택 | 논문의 일반적인 더피 길이 정의 | `stack` (crim-hook-stacks) |
| conj:pself | 모든 홀짝 자기켤레 분할 $\lambda$에 대해: $\lambda\in\mathcal N$ $\iff$ $\lambda$가 그런 스택 | `pselfConjecture` |
| 미제르 규칙 | $[\,]$에서 둘 차례인 사람이 이기므로 $[\,]$은 미제르 $\mathcal N$-위치 | `IsMP`, `isMP_iff` |
| 콘웨이 쌍 $(0,1)$ | $\lambda\in\mathcal P$이고 $G^-(\lambda)=1$; $G^-$는 $[\,]$에서 $1$, 그 밖에서는 옵션들의 값의 mex | `IsP`, `IsMV1`, `isMV1_iff` |
| 짝수×짝수 훅 | $r,c\ge2$가 짝수인 $\Gamma_{r,c}$ | `EEHook` |
| conj:hookswap | 비어 있지 않은 모든 분할 $\lambda$에 대해: $\mathrm{cp}(\lambda)=(0,1)$ $\iff$ $\lambda$가 짝수×짝수 훅 | `hookswapConjecture`(증명되지 않음) |

결정이 필요했던 점은 다음과 같습니다.

- **빈 멜드.** $[\,]$은 두꺼운 훅을 하나도 쓰지 않은 멜드입니다. $[\,]$은 $\mathcal P$이므로
  `Melds`에 넣어도 달라지는 것이 없습니다.
- **멜드의 괄호 묶기.** `Melds S`는 이항 멜드에 대한 닫힘이므로 모든 괄호 묶기를 포함합니다.
  `melds_iff`는 `meld_assoc`를 써서 이 집합이 오른쪽 결합 멜드
  $H_1\diamond(H_2\diamond(\cdots\diamond H_n))$(`meldAll`) 전체와 같음을 보입니다.
- **"for every $k$".** 모든 $k\ge1$로 읽고, $k$가 크면 $\lambda_k=\lambda'_k=0$입니다.
  $k\le\min(\ell(\lambda),\lambda_1)$에서만 비교하는 약한 해석에서는 conj:pself가 이미 $[3]$에서
  거짓입니다. $[3]$은 $\mathcal N$이지만 스택이 아닙니다.
- **"odd self-conjugate hooks".** 자기켤레인 훅은 $\Gamma_{r,r}$이고 크기 $2r-1$은 모두
  홀수이므로, "odd"는 $r$을 가리켜야 합니다. 논문의 관찰(Observation, 1123–1134행)도
  $\Gamma_{2m+1,2m'+1}$을 "odd hooks"라고 부릅니다.
- **순서와 결합.** 논문의 정의에 따르면 $\lambda\lhd\mu$와 $\mu\lhd\lambda$가 둘 다 정의되는
  일은 없고, 관찰은 "a stack of odd hooks, with last hook being $[1]$"이라고 씁니다. 따라서
  $[1]$이 마지막에 옵니다. `OddHookStack`은 오른쪽으로 결합하며 중간의 모든 스택이 정의되어야
  합니다. 논문은 결합법칙을 주장하며, 따름정리 4.11이 여기서 필요한 부분을 증명합니다. 중간의
  모든 스택이 정의되어야 한다는 조건 아래 어떤 괄호 묶기도 오른쪽 결합과 같은 분할을 주므로,
  conj:pself는 모든 괄호 묶기에서 성립합니다(`pselfConjecture_anyBracketing`). $n\le50$에서는
  6절의 계산도 같은 결과를 줍니다.
- **조각 하나.** $j=0$을 허용하므로 $[1]$ 자체도 스택입니다. $[1]$은 홀짝 자기켤레이고
  $\mathcal N$에 속하므로, 이를 빼면 추측이 거짓이 됩니다.
- **$[\,]$에서의 conj:hookswap.** 논문 스스로 $\mathrm{cp}([\,])=(0,1)$이라고 하므로 쓰인 그대로의
  명제는 $[\,]$에서 거짓입니다. 그래서 `hookswapConjecture`는 $\lambda\ne[\,]$을 요구합니다
  (참고 5.6).

## 2. 사용하는 분류

이 절은 crim-hook-stacks의 정의 몇 가지와 정리 하나를 다시 적습니다.

**런 쌍.** $\lambda\ne[\,]$의 서로 다른 부분을 $v_1>\dots>v_k>0$이라 하고, $v_i$가 $a_i$번
나타난다고 합시다. $v_{k+1}=0$으로 두고 $b_i=v_i-v_{i+1}$이라 하면, $\lambda$의 런 쌍은
$(a_1,b_1),\dots,(a_k,b_k)$이며 모든 성분이 양수입니다(`ValidPairs`). 거꾸로 `ofPairs p`는
$b_i+\dots+b_k$가 $a_i$번 나타나는 분할이고, 모든 분할은 어떤 유효한 $p$에 대해 `ofPairs p`입니다
(`exists_ofPairs`). 경계 길이는 `plen p` $=\sum_i(a_i+b_i)=\ell(\lambda)+\lambda_1$입니다
(`plen_eq`, `length_add_part_one_ofPairs`).

**통계량 $M$.** 쌍 $(a,b)$는 $a=1$이고 $b$가 홀수이면 *A-좋음*, $a$가 홀수이고 $b=1$이면
*B-좋음*이라 합니다. 어느 쪽이든 $a+b$는 짝수입니다. $L$(`endL`)은 A-좋은 쌍으로 이루어진 가장
긴 접두부의 길이, $R$(`endR`)은 B-좋은 쌍으로 이루어진 가장 긴 접미부의 길이이고,
$M=\min(k,L+R)$(`endM`)입니다. 쌍대 $\delta$(`pdual`)는 리스트를 뒤집고 각 쌍의 두 성분을
바꿉니다. $\delta$는 $L$과 $R$을 맞바꿉니다(`endL_pdual`).

**정리 2.1** (Zeng; `isP_ofPairs_iff`). 유효한 $p$에 대해 `ofPairs p`가 $\mathcal P$-위치일
필요충분조건은 `plen p`와 `endM p`가 모두 짝수인 것입니다.

## 3. 멜드 추측

**보조정리 3.1** (`meld_assoc`, `meld_nil_left`, `meld_nil_right`, `melds_iff`). 멜드는
항등원이 $[\,]$인 결합 연산이며, `Melds S`는 $S$의 원소로 이루어진 유한 리스트의 오른쪽 결합
멜드 전체와 같습니다.

*증명.* $(\mu\diamond\nu)_1=\nu_1+\mu_1$(`part_one_meld`)이므로 결합법칙의 양변은 모두
$\nu_1+\mu_1$만큼 올린 $\lambda$, $\mu_1$만큼 올린 $\nu$, 그리고 $\mu$를 차례로 이어 붙인
것입니다. `melds_iff`는 `Melds`에 대한 귀납법으로 보입니다. 오른쪽 결합 멜드 두 개를 멜드하면
두 리스트를 이어 붙인 리스트의 오른쪽 결합 멜드가 됩니다(`meldAll_append`). $\square$

**보조정리 3.2** (`meld_ofPairs`). $B$가 유효하면
$\texttt{ofPairs}\,B\diamond\texttt{ofPairs}\,A=\texttt{ofPairs}\,(A\mathbin{+\!\!+}B)$입니다.

*증명.* `ofPairs (A ++ B)`는 `ofPairs A`의 모든 부분을 $B$의 $b$-성분의 합만큼 올린 뒤
`ofPairs B`를 이어 붙인 것입니다(`ofPairs_append`). 그 합은 `ofPairs B`의 첫 부분입니다
(`part_one_ofPairs`). $\square$

즉 분할의 멜드는 런 쌍을 이어 붙이는 연산이며, 순서는 멜드를 오른쪽부터 읽은 순서입니다.
$\mu\diamond\lambda$에서는 $\lambda$의 쌍이 먼저 옵니다.

**보조정리 3.3** (`validPairs_thickPairs`, `ofPairs_thickPairs`, `plen_thickPairs`,
`endL_thickPairs`, `endR_thickPairs`). 두꺼운 훅 $\Gamma^{a,b}_{r,c}$의 런 쌍은
$(a,c-b),(r-a,b)$입니다. 경계 길이는 $r+c$이고 $L=R=0$입니다.

*증명.* 행은 길이 $c$인 것이 $a$개, 길이 $b$인 것이 $r-a$개이고 $c>b>0$입니다. 첫 쌍은
$a\ge2$이므로 A-좋지 않고, 마지막 쌍은 $b\ge2$이므로 B-좋지 않습니다. $\square$

**따름정리 3.4** (`isP_thickHook_iff`). $\Gamma^{a,b}_{r,c}\in\mathcal P$일 필요충분조건은
$r+c$가 짝수인 것입니다. 이는 논문 `thm:thick-hook`의 $\mathcal P/\mathcal N$ 부분입니다.

**보조정리 3.5** (`endL_append_eq_zero`, `endR_append_eq_zero`). $L(A)=L(B)=0$이면
$L(A\mathbin{+\!\!+}B)=0$이고, $R(A)=R(B)=0$이면 $R(A\mathbin{+\!\!+}B)=0$입니다.

*증명.* $A=[\,]$이면 첫 주장은 $L(B)=0$입니다. 그렇지 않으면 $A$의 첫 쌍은 A-좋지 않고, 이것이
$A\mathbin{+\!\!+}B$의 첫 쌍입니다. 둘째 주장은 이어 붙이기의 순서를 뒤집고 $L$과 $R$을
맞바꾸는 $\delta$로부터 따라 나옵니다. $\square$

**정리 3.6** (`exists_pairs_of_melds`, `meldConjecture_holds`). 지는 두꺼운 훅들의 멜드는 모두
$\mathcal P$-위치입니다.

*증명.* `Melds`에 대한 귀납법으로, 모든 원소가 `plen p`가 짝수이고 $L(p)=R(p)=0$인 어떤 유효한
$p$에 대해 `ofPairs p`임을 보입니다. $[\,]$에는 $p=[\,]$를 씁니다. 지는 두꺼운 훅에서는
보조정리 3.3이 $L=R=0$을 주고, 정리 2.1이 경계 길이가 짝수임을 줍니다. 멜드에서는 보조정리
3.2가 쌍 리스트를 이어 붙이고, 경계 길이는 더해지며(`plen_append`), 보조정리 3.5가 $L=R=0$을
유지합니다. 마지막으로 $M=0$은 짝수이므로 정리 2.1에 의해 $\mathcal P$입니다. $\square$

`isP_meldAll`은 리스트의 오른쪽 결합 멜드에 대해 같은 정리를 다시 적은 것입니다.

## 4. conj:pself

유효한 $p$와 런 쌍의 수 $k=|p|$에 대해 분할 $\lambda=$ `ofPairs p`를 고정합니다. 행은 $1$부터
세고, $i>\ell(\lambda)$이면 $\lambda_i=0$입니다.

**보조정리 4.1** (`countP_ofPairs`). $\lambda'_{j+1}$은 `ofPairs (pdual p)`의 $j+1$번째
행입니다. 즉 $\delta$는 켤레를 취하는 연산입니다.

*증명.* $p$에 대한 귀납법입니다. $p=(a,b)::q$이고 $B$가 `ofPairs q`의 가장 큰 부분이라
합시다. 그러면 `ofPairs p`는 `ofPairs q` 위에 길이 $b+B$인 행 $a$개를 얹은 것이고,
$\delta p=\delta q\mathbin{+\!\!+}[(b,a)]$이므로 `ofPairs (pdual p)`는 `ofPairs (pdual q)`의
모든 행을 $a$만큼 늘린 뒤 길이 $a$인 행 $b$개를 붙인 것입니다(`ofPairs_append`). 뒤쪽의 새 행
$b$개 앞에는 $B$개의 행이 있습니다. 따라서 주장의 양변은 $j<b+B$이면 똑같이 $a$만큼 커지고,
그렇지 않으면 $0$입니다. $\square$

따라서 $\lambda$가 홀짝 자기켤레일 필요충분조건은 $\lambda$와 $\lambda'=$ `ofPairs (pdual p)`의
홀짝 수열 $(\lambda_i\bmod 2)_{i\ge1}$이 같은 것입니다(`parity_eq_of_paritySelfConj`).

**보조정리 4.2** (`endL_drops`). $1\le i\le L$에서 차이 $\lambda_i-\lambda_{i+1}$은 홀수이고,
$i=L+1$에서의 차이는 짝수입니다.

*증명.* $p$에 대한 귀납법입니다. A-좋은 첫 쌍은 차이가 홀수인 행 하나이며, 이때 $L$은 나머지로
넘어갑니다. 첫 쌍이 A-좋지 않으면 $a\ge2$(첫 차이가 $0$)이거나, $a=1$이고 차이가
짝수입니다. $\square$

따라서 $L$은 $\lambda$의 홀짝 수열에만 의존합니다(`endL_le_of_parity`).

**보조정리 4.3** (`endL_eq_endR_of_paritySelfConj`, `even_plen_of_paritySelfConj`).
$\lambda$가 홀짝 자기켤레이면 $L=R$이고 $\ell(\lambda)+\lambda_1$은 짝수입니다.

*증명.* $R(p)=L(\delta p)$는 홀짝 수열이 같은 $\lambda'$의 $L$이므로, 보조정리 4.2에 의해
$L=R$입니다. 홀짝 자기켤레성의 $k=1$ 경우는 $\lambda_1\equiv\lambda'_1=\ell(\lambda)$입니다.
$\square$

**$L+R<k$인 경우.** 이때 $M=L+R=2L$은 짝수이고 경계 길이도 짝수이므로, 정리 2.1에 의해
$\lambda\in\mathcal P$입니다. 따라서 홀짝 자기켤레인 $\mathcal N$-위치는 $L+R\ge k$를
만족합니다.

**보조정리 4.4** (`forall_good_of_le`). $L+R\ge k$이면 모든 런 쌍이 A-좋거나 B-좋으므로, 모든
성분 $a_i,b_i$가 홀수입니다.

*증명.* 가장 긴 A-좋은 접두부와 가장 긴 B-좋은 접미부가 겹치거나 맞닿습니다. Lean에서는
A-좋은 접두부 뒤의 부분에 있는 쌍이 모두 B-좋음을 보입니다(`forall_bGood_of_endR_eq`).
$\square$

**보조정리 4.5** (`map_fst_eq_of_parity`, `pdual_eq_self_of_parity`). $p$와 $q$의 $b$-성분이
모두 홀수이고 `ofPairs p`와 `ofPairs q`의 홀짝 수열이 같으면, $p$와 $q$의 $a$-성분은 같습니다.
따라서 $p$의 모든 성분이 홀수이고 $\lambda$가 홀짝 자기켤레이면 $\delta p=p$, 즉 $\lambda$는
자기켤레입니다.

*증명.* 같은 길이의 행 $a_1$개로 이루어진 블록 안에서는 홀짝이 일정하고, $b_1$이 홀수이므로
블록이 끝나면 홀짝이 바뀝니다. 따라서 $a_1$은 홀짝이 처음 바뀌는 위치이며, 나머지는 귀납법으로
보입니다. 뒷부분은 이를 $p$와 $\delta p$에 적용합니다. $\delta p$의 $b$-성분은 $p$의
$a$-성분이므로 홀수입니다. $\delta p$의 $a$-성분은 $p$의 $b$-성분을 뒤집은 것이고 그 반대도
마찬가지이므로, $a$-성분이 같으면 $\delta p=p$입니다. $\square$

**스택의 모양.** 리스트 $os=[o_1,\dots,o_j]$에 대해 `spPairs os`를
\[
(1,o_1),\dots,(1,o_j),(1,1),(o_j,1),\dots,(o_1,1)
\]
로 둡니다. 모든 $o_i$가 홀수이면 이 리스트는 유효하고 자기쌍대이며(`validPairs_spPairs`,
`pdual_spPairs`), 앞의 $j+1$개 쌍은 A-좋고 뒤의 $j+1$개 쌍은 B-좋으므로
$M=k=2j+1$입니다(`endM_spPairs`).

**보조정리 4.6** (`eq_spPairs`). $|p|=2n+1$이고 $\delta p=p$이며 $p$의 앞 $n+1$개 쌍이
A-좋으면, 모든 $o_i$가 홀수인 어떤 $os$에 대해 $p=$ `spPairs os`입니다.

*증명.* $n$에 대한 귀납법입니다. $n=0$이면 $p=[(a,b)]$에서 $(b,a)=(a,b)$이고 $a=1$이므로
$p=[(1,1)]$입니다. $n+1$이면 $p=x\,q\,y$로 씁니다. 자기쌍대성에서 $y$는 $x$의 두 성분을 바꾼
것이고 $\delta q=q$입니다. 첫 쌍 $x=(1,o)$는 A-좋으므로 $o$는 홀수이고 $y=(o,1)$입니다. $q$의
앞 $n+1$개 쌍은 A-좋으므로 귀납 가정에 의해 $q=$ `spPairs os`이고,
$p=$ `spPairs (o :: os)`입니다(`spPairs_cons`). $\square$

**명제 4.7** (`oddHookStack_of_paritySelfConj`). 홀짝 자기켤레인 $\mathcal N$-위치의 런 쌍은
모든 $o_i$가 홀수인 `spPairs os`입니다.

*증명.* 보조정리 4.3과 $L+R<k$인 경우에 의해 $L=R$이고, 경계 길이는 짝수이며, $L+R\ge k$입니다.
그러면 $M=k$이고, $\lambda\in\mathcal N$이므로 $k$는 홀수, 곧 $k=2n+1$이며 $L=R\ge n+1$입니다.
보조정리 4.4와 4.5가 $\delta p=p$를 주고, 보조정리 4.6을 적용합니다. $\square$

**보조정리 4.8** (`oddHookStack_iff`). 분할이 홀수 자기켤레 훅들과 $[1]$의 스택
(`OddHookStack`)일 필요충분조건은 모든 $o_i$가 홀수인 어떤 $os$에 대해
`ofPairs (spPairs os)`인 것입니다.

*증명.* crim-hook-stacks의 `stack_hook`에 따르면 $\Gamma_{r,r}\lhd\mu$는
$\ell(\mu)\le r-1$이고 $\mu_1\le r-1$일 때 정의되며, 그 값은
$[r,1+\mu_1,\dots,1+\mu_m,1^{r-1-m}]$입니다. $\mu=$ `ofPairs (spPairs os)`라 합시다. $\mu$는
자기켤레이므로 $\ell(\mu)=\mu_1=N$이고, $N$은 홀수입니다(`odd_pairsBSum_spPairs`). 따라서
$r$이 홀수일 때 스택은 $N\le r-1$이면 정의되며, 이때 $o=r-1-N$은 홀수이므로 $o\ge1$이고
$\Gamma_{r,r}\lhd\mu=[o+N+1,(\mu_i+1)_i,1^o]$의 런 쌍은 `spPairs (o :: os)`입니다
(`ofPairs_spPairs_cons`). 거꾸로 `spPairs (o :: os)`는 홀수 $r=o+N+1$에서 이렇게 나옵니다.
스택 또는 $os$에 대한 귀납법으로 마칩니다. $\square$

**정리 4.9** (`paritySelfConj_and_not_isP_iff`, `pselfConjecture_holds`). 모든 분할
$\lambda$에 대해, $\lambda$가 홀짝 자기켤레이면서 $\mathcal N$에 속할 필요충분조건은
$\lambda$가 홀수 자기켤레 훅들과 $[1]$의 스택인 것입니다. 특히 conj:pself가 성립합니다.

*증명.* ($\Rightarrow$) 명제 4.7과 보조정리 4.8. ($\Leftarrow$) 보조정리 4.8에 의해 런 쌍은
`spPairs os`입니다. 자기쌍대성과 보조정리 4.1에서 $\lambda'=\lambda$이므로
(`conjPart_of_oddHookStack`) $\lambda$는 홀짝 자기켤레입니다. 모든 쌍에서 $a+b$가 짝수이므로
경계 길이는 짝수이고, $M=2j+1$은 홀수이므로 정리 2.1에 의해 $\lambda\in\mathcal N$입니다
(`not_isP_ofPairs_spPairs`). $\square$

특히 홀짝 자기켤레인 $\mathcal N$-위치는 모두 자기켤레입니다.

**보조정리 4.10** (`stack_hook_assoc`). $c\ge1$이고 $\mu$가 공집합이 아닌 분할, $\nu$가 분할이면
$(\Gamma_{r,c}\lhd\mu)\lhd\nu$가 정의되는 것과 $\Gamma_{r,c}\lhd(\mu\lhd\nu)$가 정의되는 것은
동치이고, 이때 둘은 같습니다.

*증명.* $d=d(\mu)$라 하면 $d\ge1$이고, $m=\ell(\mu)$라 합니다. $\mu\lhd\nu$가 정의되면 그
길이와 첫 행은 $\mu$와 같으므로(`stack_facts`), $\Gamma_{r,c}\lhd\mu$가 정의되지 않으면 오른쪽도
정의되지 않습니다. 그렇지 않으면 $x=\Gamma_{r,c}\lhd\mu$의 더피 길이는 $d+1$이고
(`durfee_hookStack`), $x_{d+1}=\mu_d+1$이며, $i\ge1$에 대해 $x$의 $d+1+i$번째 행은
$d+i\le r-1$이면 $\mu_{d+i}+1$, 아니면 $0$입니다. 또 $d+i>r-1\ge m$이면 $\mu_{d+i}=0$입니다.
따라서 $x_{d+1+i}=d+1$과 $\mu_{d+i}=d$가 동치이고, $x_{d+1}\ge d+1+\nu_1$과
$\mu_d\ge d+\nu_1$이 동치이므로, $x\lhd\nu$가 정의되는 것과 $\mu\lhd\nu$가 정의되는 것은
동치입니다. 둘 다 정의되면, $x$의 $d+1+i$번째 행에 $\nu_i$를 더하는 것은 $\mu$의 $d+i$번째 행에
$\nu_i$를 더한 뒤 $\Gamma_{r,c}$ 아래에 쌓는 것과 같습니다(`hookStack_stack_eq`). $\square$

**따름정리 4.11** (`HookTree.eval_eq_nest`, `exists_hookTree_iff`,
`pselfConjecture_anyBracketing`). 모든 $r_i\ge1$에 대해
$\Gamma_{r_1,r_1}\lhd\cdots\lhd\Gamma_{r_j,r_j}$의 괄호를 어떻게 묶든, 중간의 모든 스택이
정의되어야 한다는 조건 아래 그 결과가 정의되는 것과 오른쪽 결합 스택이 정의되는 것은 동치이고,
이때 둘은 같습니다. 따라서 conj:pself는 홀수 자기켤레 훅들과 $[1]$의 스택을 어떻게 괄호로
묶어도 성립합니다.

*증명.* 괄호 묶기는 잎을 왼쪽부터 읽으면 훅들이 되는 이진 트리 `HookTree`입니다. 오른쪽 결합을
`nest`라 쓰면, 오른쪽 결합으로 쌓은 훅들의 스택은 모두 공집합이 아닌 분할입니다
(`nest_isPartition`). 보조정리 4.10을 훅마다 한 번씩 적용하면 안쪽의 스택을 오른쪽 결합 밖으로
옮길 수 있습니다: $(H_1\lhd(\cdots\lhd H_i))\lhd y=H_1\lhd(\cdots\lhd(H_i\lhd y))$이고,
정의되는 조건도 같습니다(`nest_assoc`). 트리에 대한 귀납법을 쓰면, 노드 $t\lhd u$에서 두 부분
트리는 귀납 가정에 의해 오른쪽 결합이고, `nest_assoc`이 $t\lhd u$를 하나의 오른쪽 결합으로
바꿉니다. $\square$

## 5. 미제르 규칙

미제르 규칙에서는 마지막 수를 두는 사람이 집니다. 따라서 $[\,]$은 $\mathcal N$-위치이고(둘 차례인
사람은 수를 둘 수 없으므로 이깁니다), 비어 있지 않은 위치가 $\mathcal P$-위치일 필요충분조건은
어떤 수도 $\mathcal P$-위치로 가지 않는 것입니다(`isMP`, `IsMP`, `isMP_iff`). 쌍 리스트 $p$에
대해 정리 2.1의 Zeng 조건 "`plen p`와 `endM p`가 모두 짝수"를 $Z$라 하고, $L+R\ge k$, 곧
$M=k$이면(`cover_iff`) $p$가 *덮였다*($C$)고 합니다. 보조정리 4.4에 따라 덮인 리스트의 모든 쌍은
좋습니다. 보조정리 4.2로 말하면, $L$은 맨 위에서부터 차이가 홀수인 행이 이어지는 수, $R$은
$\lambda'$에 대한 같은 수, $k$는 서로 다른 부분 크기의 수입니다. "$Z$와 $C$ 중 정확히 하나가
성립한다"를 $\mathrm{MisP}(p)$로 씁니다(`MisP`). 아래에서는
[crim-hook-stacks](../crim-hook-stacks/DETAILS.ko.md)의 7절을 씁니다. 그 보조정리 7.1은 쌍 리스트
위의 수(`PMove`)를 나열하고, 보조정리 7.2–7.4는 Zeng 증명의 단계입니다.

**정리 5.1** (`misereP_iff`, `misereP_iff_isP`). 유효한 $p$에 대해 `ofPairs p`가 미제르
$\mathcal P$-위치일 필요충분조건은 $\mathrm{MisP}(p)$입니다. 정리 2.1에 따라 이는 "`ofPairs p`가
정상 규칙의 $\mathcal P$-위치이다"와 "$p$가 덮였다" 중 정확히 하나가 성립하는 것과 같습니다.

이 프로젝트의 이전 탐색 실행이 이 규칙을 제안했습니다. 예를 들어 쌍이 $(1,1)$과 $(1,3)$인
$[1]$과 $[3]$은 $M=1$로 덮였으므로 미제르 $\mathcal P$-위치입니다. 쌍이 $(1,1),(1,1)$인 $[2,1]$은
`plen`이 짝수이고 $M=2$로 덮였으므로 미제르 $\mathcal N$-위치입니다($[1]$로 갈 수 있습니다). 빈
리스트는 $Z$와 $C$를 모두 만족하므로, 마땅히 $[\,]$은 미제르 $\mathcal N$-위치입니다.

**보조정리 5.2** (`even_plen_of_cover`, `even_plen_of_misP`, `ne_nil_of_misP`). 덮인 리스트의
`plen`은 짝수입니다. 따라서 $\mathrm{MisP}(p)$이면 `plen p`가 짝수이고, $\mathrm{MisP}([\,])$는
성립하지 않습니다.

*증명.* `plen`이 홀수인 리스트는 보조정리 7.4의 증명에서처럼 코어가 비어 있지 않은 $P\,C\,S$로
쪼개지므로(`exists_split`) $L+R=|P|+|S|<k$입니다. $\square$

**보조정리 5.3** (`length_eq_of_even`, `misP_iff_of_move`). `PMove p q`이고 `plen p`와 `plen q`가
모두 짝수이면, $q$의 쌍은 $p$보다 하나 적고, `endM p = endM q + 1`이며,
$\mathrm{MisP}(p)\iff\neg\,\mathrm{MisP}(q)$입니다.

*증명.* 보조정리 7.2의 증명에 따라 이 수는 A-좋은 첫 쌍이나 B-좋은 마지막 쌍을 없애고 $M$을 1
줄입니다(`endM_eq_of_even`). 따라서 $Z$는 뒤집히고, $M=k$는 $p$와 $q$에서 함께 성립하거나 함께
성립하지 않으므로 $C$는 유지됩니다(`misP_iff_of_succ`). $\square$

**보조정리 5.4** (`not_misP_move`). $\mathrm{MisP}(p)$이고 `PMove p q`이면 $\mathrm{MisP}(q)$는
성립하지 않습니다.

*증명.* 보조정리 5.2에 따라 `plen p`는 짝수입니다. `plen q`가 홀수이면 보조정리 5.2를 $q$에
적용하고, 그렇지 않으면 보조정리 5.3을 적용합니다. $\square$

**보조정리 5.5** (`exists_misP_move`). $p$가 유효하고 비어 있지 않으며 $\mathrm{MisP}(p)$가
성립하지 않으면, 어떤 수는 $\mathrm{MisP}(q)$인 $q$로 갑니다.

*증명.* `plen p`가 짝수라고 합시다. $M=0$이면 $Z$가 성립하고, $p\ne[\,]$이므로 $C$는 성립하지
않습니다. 따라서 $M\ge1$이고, `plen`을 짝수로 유지하면서 끝 쌍 하나를 없앨 수 있으며(`exists_peel`,
보조정리 7.3과 같음), 보조정리 5.3이 $\mathrm{MisP}(q)$를 줍니다.

`plen p`가 홀수라고 합시다. $p=P\,C\,S$로 두고 보조정리 7.4의 증명을 따릅니다(`mgood_of_odd`).
거기서 고르는 수는 모두 $Z$에 이릅니다. 대부분의 경우 새 리스트에는 여전히 비어 있지 않은 코어가
있으므로 덮이지 않았고, $\mathrm{MisP}$가 성립합니다(`misP_of_split`). 덮인 리스트에 이르는 세
경우는 그 거울상(`misP_pdual`, `MGood.of_pdual`)과 함께 다음과 같이 바꿉니다.

- $L+R$가 홀수, $P=[\,]$, $C=[(1,b)]$이고 $b$가 짝수이면 $R$은 홀수입니다. 정상 규칙의 증명은
  1을 하나 지워 $(1,b-1)\,S$에 이르는데, 이 리스트는 $M=R+1$(짝수)로 덮였습니다. 대신
  $(1,b)$의 0을 지웁니다(`zeroFirst`). 그러면 $S$가 남고, $S$는 `plen`이 짝수이며 $M=R$(홀수)로
  덮였습니다(`mgood_core_one_odd`, `misP_of_good`).
- $L+R$가 짝수이고 $C=[(1,b)]$, $b$가 짝수인 경우. 정상 규칙의 증명은 0을 지워 $M=L+R$(짝수)인
  덮인 리스트에 이릅니다. 대신 1을 하나 지웁니다. 쌍 $(1,b-1)$은 A-좋으므로 $P\,(1,b-1)\,S$는
  $k=L+R+1$(홀수)로 덮였습니다(`mgood_core_one_even`).
- $L+R$가 짝수, $|C|\ge2$이고 코어의 첫 쌍이 $(1,b)$인 경우. 정상 규칙에서처럼 "$(1,b)$의 0
  지우기"와 "1 하나 지우기"를 비교합니다. 둘 다 `plen`이 짝수인 리스트에 이르고, 두 번째 리스트는
  쌍이 하나 더 많으며 $M$도 1 큽니다(`endM_prefix_barrier`). `misP_iff_of_succ`에 따라 두 리스트
  중 정확히 하나가 $\mathrm{MisP}$를 만족합니다(`mgood_core_long`). $\square$

*정리 5.1의 증명* (`misere_classification`). 유효한 리스트 위의 술어 $G$가 "$G(p)$일
필요충분조건은 $p\ne[\,]$이고 어떤 수도 $G(q)$인 $q$로 가지 않는 것"을 만족한다고 합시다.
`plen p`에 대한 강한 귀납법으로 $G(p)\iff\mathrm{MisP}(p)$를 보입니다. $\mathrm{MisP}(p)$이면
보조정리 5.2에 따라 $p\ne[\,]$이고, 보조정리 5.4에 따라 어떤 수도 $\mathrm{MisP}$로 가지 않습니다.
그렇지 않으면 $p=[\,]$이거나, 보조정리 5.5가 $\mathrm{MisP}$로 가는 수를 줍니다. 보조정리 7.1과
`ofPairs_ne_nil_iff`에 따라 술어 $G(p)=$ `IsMP (ofPairs p)`가 이 조건을 만족하므로
(`isMP_ofPairs_iff_forall`) `misereP_iff`를 얻습니다. 정리 2.1이 $Z$를 "정상 규칙의
$\mathcal P$"로 바꿉니다(`misereP_iff_isP`). $\square$

6절의 프로그램도 미제르 CRIM을 정확히 풀어, 크기 50 이하의 모든 분할에서 이 분류를 확인합니다
(미제르 $\mathcal P$-위치 365,204개). 논문은 미제르 규칙에 대해 콘웨이 쌍을 통해서만 묻고, 우리는
이 분류의 이전 진술을 찾지 못했습니다.

### 콘웨이 쌍과 conj:hookswap

한 수로 갈 수 있는 위치를 옵션이라고 합시다. 크기에 대한 귀납법으로, $G^-(\lambda)=0$일
필요충분조건은 $\lambda$가 미제르 $\mathcal P$-위치인 것입니다. $G^-([\,])=1$이고, 비어 있지 않은
위치의 $G^-$가 $0$일 필요충분조건은 $G^-=0$인 옵션이 없는 것이기 때문입니다. 따라서
$\mathrm{cp}(\lambda)=(0,1)$일 필요충분조건은 $\lambda$가 정상 규칙의 $\mathcal P$-위치(`IsP`)이고
$G^-(\lambda)=1$(`IsMV1`)인 것입니다. `isMV1_iff`에 따르면 $G^-(\lambda)=1$일 필요충분조건은
$\lambda=[\,]$이거나, $\lambda$의 어떤 옵션이 미제르 $\mathcal P$-위치이고 $G^-=1$인 옵션이 없는
것입니다. 논문의 추측(1058–1060행)은 다음과 같습니다.

> **conj:hookswap.** A partition $\lambda$ has Conway pair $(0,1)$ if and only if $\lambda$ is
> an even-by-even hook.

짝수×짝수 훅은 $r$와 $c$가 양의 짝수인 $\Gamma_{r,c}$입니다(`EEHook`).

**참고 5.6** (`nil_conwayPair`). 논문이 `thm:cgpairrow`의 증명에서 쓰듯 $[\,]$의 콘웨이 쌍은
$(0,1)$이고, $[\,]$은 훅이 아닙니다. 따라서 이 명제에는 $\lambda\ne[\,]$이 필요하며,
`hookswapConjecture`는 비어 있지 않은 분할에 대한 형태입니다. 이는 반박이 아니라 문구의 경계
사례입니다.

**보조정리 5.7** (`misere_column`, `misere_hook`). $r,c\ge1$이면 $\Gamma_{r,c}$가 미제르
$\mathcal P$-위치일 필요충분조건은 $r$와 $c$가 홀수인 것이고, $G^-(\Gamma_{r,c})=1$일
필요충분조건은 $r$와 $c$가 짝수인 것입니다.

이는 논문의 `thm:cgpairshooks`(862–870행)의 미제르 부분을 값 $0$과 $1$로 제한한 것입니다.

*증명.* 열 $1^n$의 옵션은 $[\,]$과 $1^{n-1}$입니다(`mem_moves_column`). $n$에 대한 귀납법으로,
$1^n$이 미제르 $\mathcal P$일 필요충분조건은 $n$이 홀수인 것이고, $n\ge1$이면 옵션 $[\,]$의 값이
$1$이므로 $G^-(1^n)=1$일 필요충분조건은 $n=0$인 것입니다(`misere_column`). $\Gamma_{r,1}=1^r$이므로
이것으로 $c=1$인 경우가 끝납니다.

$c\ge2$이면 $r+c$에 대한 귀납법을 씁니다. $\Gamma_{r,c}$의 옵션은 $1^{r-1}$,
$\Gamma_{r-1,c}$($r\ge2$일 때), $[c-1]=\Gamma_{1,c-1}$, $\Gamma_{r,c-1}$입니다
(`mem_moves_hookStack`). $r$이 짝수이면 $1^{r-1}$이, $c$가 짝수이면 $[c-1]$이 미제르
$\mathcal P$이고, $r$와 $c$가 홀수이면 미제르 $\mathcal P$인 옵션이 없습니다. 이로써 첫 번째
주장이 나옵니다. $r$와 $c$가 짝수이면 $[c-1]$이 미제르 $\mathcal P$이고, 각 옵션은 $r'$나 $c'$가
홀수인 훅 $\Gamma_{r',c'}$이므로($r\ge2$이므로 $1^{r-1}=\Gamma_{r-1,1}$) 값이 $1$인 옵션이
없습니다. 나머지 경우에는 $G^-(\Gamma_{r,c})\ne1$입니다. $r$이 홀수이고 $c$가 짝수이면 옵션
$[\,]$($r=1$일 때)이나 $\Gamma_{r-1,c}$의 값이 $1$이고, $r$이 짝수이고 $c$가 홀수이면
$\Gamma_{r,c-1}$의 값이 $1$이며, 둘 다 홀수이면 $G^-(\Gamma_{r,c})=0$입니다. $\square$

**정리 5.8** (`conwayPair_hook_iff`, `conwayPair_of_eeHook`, `hookswapConjecture_iff`).
$r,c\ge1$이면 $\Gamma_{r,c}$의 콘웨이 쌍이 $(0,1)$일 필요충분조건은 $r$와 $c$가 짝수인
것입니다. 따라서 모든 짝수×짝수 훅의 콘웨이 쌍은 $(0,1)$이고, 비어 있지 않은 분할에 대한
conj:hookswap은 $(\Rightarrow)$ 방향과 동치입니다.

*증명.* 훅이 정상 규칙의 $\mathcal P$-위치일 필요충분조건은 $r,c\ge2$이고
$r\equiv c\pmod 2$인 것입니다(crim-hook-stacks의 `isP_hook_iff`). 이를 보조정리 5.7과
합칩니다. $\square$

**명제 5.9** (`not_isMP_of_isMV1`, `covered_of_conwayPair`). $p$가 유효하고 `ofPairs p`의 콘웨이
쌍이 $(0,1)$이면, $p$는 덮였고 $k$는 짝수입니다.

*증명.* $G^-=1$이므로 $G^-=0$인 옵션이 있고, 따라서 `ofPairs p`는 미제르 $\mathcal P$가
아닙니다. 이 위치는 정상 규칙의 $\mathcal P$이므로 정리 5.1에 따라 덮였습니다. 그러면 $M=k$이고,
정리 2.1에 따라 $M$은 짝수입니다. $\square$

$(\Rightarrow)$ 방향은 증명하지 못했습니다. 명제 5.9에 따라 이 방향은 $k$가 짝수이고 모든 쌍이
좋은(보조정리 4.4) 덮인 리스트에 관한 것입니다. 짝수×짝수 훅 $\Gamma_{r,c}$의 쌍은
$(1,c-1),(r-1,1)$이므로 $k=2$이고, $k=2$인 경우가 자연스러운 첫 단계일 것입니다. 증명을 끝낼 만큼
$G^-=1$인 위치를 설명하는 규칙은 찾지 못했습니다. 6절의 프로그램은 크기 50 이하의 모든 분할에서
비어 있지 않은 경우의 명제를 확인합니다.

## 6. 계산

[`pself_meld_check.py`](programs/pself_meld_check.py)는 분할을 튜플로 다루며, Zeng의 규칙과
비교할 때를 빼면 런 쌍 부호화를 쓰지 않습니다.

- 크기 $\le N$인 모든 분할을 크기 순으로 나열하고, 수를 직접 만들며(행 하나를 지우거나, 열 하나를
  지우고 $0$이 된 부분을 버림), 게임 재귀로 정상 규칙과 미제르 규칙의 결과를 계산합니다. 수는
  크기를 줄입니다.
- 정상 규칙의 결과를 모든 곳에서 Zeng의 규칙과 비교하고, `--misere`를 주면 미제르 규칙의 결과를
  5절의 분류와 비교합니다.
- `--hookswap`을 주면 mex 재귀로 모든 분할의 콘웨이 쌍을 계산하고($\mathrm{cp}([\,])=(0,1)$),
  이를 두 결과와 대조한 뒤, 비어 있지 않은 분할에 대해 conj:hookswap을 확인합니다.
- 크기 $\le N$인 모든 두꺼운 훅을 나열해 `thm:thick-hook`의 $\mathcal P/\mathcal N$ 부분을
  확인하고, 지는 것들을 크기 $N$까지 멜드(양쪽 순서)로 닫은 뒤 결과가 모두 $\mathcal P$인지
  확인합니다. 크기 $\le6$인 분할의 모든 세 쌍에서 결합법칙과 항등원도 확인합니다.
- 논문의 해석과 1.1절의 약한 해석 각각에서 홀짝 자기켤레인 $\mathcal N$-위치를 계산하고, "스택"의
  12가지 해석과 비교합니다. 훅 $\Gamma_{r,r}$은 $r$이 홀수인 것만 또는 모든 $r$; $[1]$을 마지막
  조각으로 요구하거나 요구하지 않음; 오른쪽 결합($h\lhd x$), 왼쪽 결합($x\lhd h$), 임의의 괄호
  묶기($x\lhd y$)입니다.
  중간의 모든 스택은 일반적인 더피 길이 정의를 쓰며 정의되어야 합니다.

$N=50$의 결과([로그](logs/pself_meld_check_n50.log), 26초, 약 470 MB):

| 확인 항목 | 결과 |
|---|---|
| 분할, $\mathcal P$-위치 | 1,295,971개와 365,327개; Zeng의 규칙이 모두 일치 |
| 두꺼운 훅 | 1,714개, 그중 $\mathcal P$ 844개; `thm:thick-hook`과 일치 |
| 지는 두꺼운 훅들의 멜드 | 1,732개(조각이 둘 이상인 것 888개), 모두 $\mathcal P$ |
| 결합법칙과 항등원 | 세 쌍 27,000개 |
| 홀짝 자기켤레 | 분할 3,559개, 그중 $\mathcal N$ 56개 |
| 미제르 | 미제르 $\mathcal P$-위치 365,204개, 덮인 분할 23,447개; 분류 성립 |
| conj:hookswap | $\mathrm{cp}([\,])=(0,1)$; 콘웨이 쌍이 $(0,1)$인 비어 있지 않은 분할 300개가 짝수×짝수 훅 300개와 정확히 같음 |

| "스택"의 해석 | 스택 수 | 결과 |
|---|---|---|
| $r$ 홀수, $[1]$ 마지막; 오른쪽, 왼쪽, 임의 결합 | 각각 56 | 홀짝 자기켤레인 $\mathcal N$-위치 56개와 정확히 일치 |
| $r$ 홀수, $[1]$ 요구 안 함 | 116 | 여분의 스택 60개, 첫 번째는 $[3,1,1]=\Gamma_{3,3}$ |
| 모든 $r$, $[1]$ 마지막 | 581 | 여분의 스택 525개, 첫 번째는 $[2,2]=\Gamma_{2,2}\lhd[1]$ |
| 모든 $r$, $[1]$ 요구 안 함 | 1,212 | 여분의 스택 1,156개, 첫 번째는 $[2,1]=\Gamma_{2,2}$ |

약한 홀짝 해석에서는 홀짝 자기켤레인 $\mathcal N$-위치가 834개이며, 그중 778개는 12가지 해석
어느 것에서도 스택이 아닙니다. `--max-n 35`로 실행하면 약 1초 걸리며, 이것이 CI 항목입니다.

## 7. 관련 연구와 감사

[README](README.ko.md#관련-연구와-감사)를 참고하세요. 요약하면, 두 추측은 Bašić, Gottlieb,
Krnc의 것이고, 두 증명은 Zijian Zeng의 분류(심사 전 프리프린트)의 따름정리이며 그 분류는
crim-hook-stacks에서 형식화되었습니다. 미제르 증명은 Zeng 증명의 수 분석을 다시 씁니다.
conj:hookswap의 $(\Leftarrow)$ 방향은 논문의 `thm:cgpairshooks`에서 나옵니다. 이 프로젝트의 이전
탐색 실행이 두 경로와 미제르 가설을 찾았고, 멜드 논증의 첫 Lean 초안을 썼으며, 비어 있지 않은
분할에 대한 conj:hookswap을 크기 50까지 확인했습니다.
