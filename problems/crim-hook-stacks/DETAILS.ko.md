[English](DETAILS.md) | **한국어**

# CRIM의 지는 훅 쌓기: 증명 상세

두 추측은 Ina Bašić, Eric Gottlieb, Matjaž Krnc의 *CRIM: A Natural Game on Integer Partitions*
([arXiv:2606.16828](https://arxiv.org/abs/2606.16828))에서 나왔습니다.

2–7절의 모든 내용은 [`CrimHookStacks.lean`](../../AgenticConjectures/CrimHookStacks.lean)에서
커널로 검증됩니다(`sorry`, 추가 공리, `native_decide` 없음). 본문은 같은 증명을 종이 위에서
제시하고 각 단계에 해당하는 Lean 선언의 이름을 적습니다. 3–5절은 conj:bloby를 conj:main으로
환원하고, 7절은 Zijian Zeng의 경계 단어 분류를 형식화해 conj:main을 증명합니다. 8절은 계산을
설명하며, 계산은 증거일 뿐입니다. 이 작업은 사람이 검토하지 않았으며, 새로움은 주장하지
않습니다.

## 1. 게임, 스택, 두 추측

열–행 비편향 병합(Column–Row Impartial Merge, CRIM)의 위치는 빈 분할 $[\,]$을 포함한 정수 분할
$\lambda=[\lambda_1,\dots,\lambda_r]$ ($\lambda_1\ge\dots\ge\lambda_r\ge1$)입니다.
$\ell(\lambda)=r$로 쓰고, $i>r$이면 $\lambda_i=0$으로 둡니다. 한 수는 영 도형에서 행 하나나 열 하나를
지우고 남은 조각을 다시 붙입니다.

- 행 $i$를 지우면 부분 $\lambda_i$가 없어집니다.
- 열 $j$ ($1\le j\le\lambda_1$)를 지우면 $j$ 이상인 부분이 모두 1씩 줄고, 0이 된 부분은 버립니다.

정상 규칙(normal play)을 따르므로 $[\,]$은 $\mathcal P$-위치이고, 어떤 위치가 $\mathcal P$인 것은
모든 수가 $\mathcal N$-위치로 갈 때와 같습니다. 모든 수는 $|\lambda|+\ell(\lambda)$를 줄이므로 이
재귀는 잘 정의됩니다.

논문(arXiv:2606.16828v1)은 다음 개념을 씁니다.

- **랭크**(§2.1): $\operatorname{rank}\lambda=|\ell(\lambda)-\lambda_1|$, 즉 다이슨 랭크입니다.
- **훅**: $r,c\ge1$에 대해 $\Gamma_{r,c}=[c,1^{r-1}]$입니다. 행 $[c]$ ($r=1$)와 열 $[1^r]$ ($c=1$)도
  훅입니다.
- **더피 길이**: $d(\lambda)$는 $d\le\lambda_d$를 만족하는 가장 큰 $d$입니다.
- **스택**: $\mu=[\mu_1,\dots,\mu_k]$이고 $d=d(\lambda)$일 때, $1\le i\le k$에 대해
  $\lambda_{d+i}=d$이고 $\lambda_d\ge d+\mu_1$이면 스택 $\lambda\lhd\mu$가 정의되며
  $$\lambda\lhd\mu=[\lambda_1,\dots,\lambda_d,\lambda_{d+1}+\mu_1,\dots,\lambda_{d+k}+\mu_k,
  \lambda_{d+k+1},\dots,\lambda_r]$$
  입니다.

> **conj:main.** 모든 $\mathcal P$-위치는 랭크가 짝수이다.
>
> **conj:bloby.** $\lambda$와 $\Gamma_{r,c}$가 지는 위치이고 $\lambda^*=\Gamma_{r,c}\lhd\lambda$가
> 정의되면 $\lambda^*\in\mathcal P$이다.

### 1.1 해석

| 항목 | 해석 | Lean |
|---|---|---|
| 위치 | 양의 자연수로 이루어진 약감소 리스트 | `IsPartition` |
| $\lambda_i$ | 1부터 센 첨자, 끝을 넘으면 $0$ (`part l 0`은 쓰지 않음) | `part` |
| 수 | 행은 `List.eraseIdx`, 열은 $1\le j\le\lambda_1$인 `delCol l j` | `moves` |
| 지는 위치 | $\mathcal P$-위치, 정상 규칙, $[\,]$은 $\mathcal P$ | `isP`, `IsP` |
| 랭크 | $\lvert\ell(\lambda)-\lambda_1\rvert$ | `rank` |
| 더피 길이 | $d\le\lambda_d$인 가장 큰 $d\le\ell(\lambda)$ (더 큰 $d$는 어차피 조건을 만족하지 않음) | `durfee` |
| 스택 | 논문의 정의를 항 하나하나 그대로; $\mu=[\,]$이면 $\mu_1=0$ | `stack` |
| 훅 | $r,c\ge1$; 행과 열 포함 | `hook` |
| conj:main | $\mathcal P$에 속하는 모든 분할의 랭크가 짝수 | `mainConjecture` |
| conj:bloby | 모든 분할 $\lambda$와 모든 $r,c\ge1$에 대해 | `statement` |

경계 경우가 둘 있습니다. $\lambda=[\,]$도 허용하며 자명합니다: $\Gamma_{r,c}\lhd[\,]=\Gamma_{r,c}$.
행이나 열에 대해서는 $\lambda=[\,]$일 때만 스택이 정의되고(명제 3.1), 행과 열은 결코
$\mathcal P$가 아니므로(보조정리 2.2) 새로운 경우를 더하지 않습니다.

## 2. 작은 분류

**보조정리 2.1** (`not_isP_single`, `not_isP_replicate_one`, `two_le_of_isP`). $c,r\ge1$인 행 $[c]$와
열 $[1^r]$은 $\mathcal N$입니다. 그 행을 지우거나 열 1을 지우면 $[\,]$에 도달하기 때문입니다. 따라서
비어 있지 않은 $\mathcal P$-위치는 $\ell(\lambda)\ge2$이고 $\lambda_1\ge2$입니다.

**보조정리 2.2** (논문의 `lem:hook`; `isP_hook_iff`). $r,c\ge1$일 때 $\Gamma_{r,c}\in\mathcal P$일
필요충분조건은 $r,c\ge2$이고 $r\equiv c\pmod 2$인 것입니다.

*증명.* $r+c$에 대한 귀납법입니다. $r=1$이거나 $c=1$이면 이 훅은 행이거나 열입니다. $r,c\ge2$라
합시다. $\Gamma_{r,c}$에서 가능한 수는 열 $[1^{r-1}]$ (행 1), 행 $[c-1]$ (열 1),
$\Gamma_{r-1,c}$ (다리의 행), $\Gamma_{r,c-1}$ (팔의 열)로 갑니다. 앞의 둘은 비어 있지 않으므로
$\mathcal N$입니다. $r\equiv c$이면 $\Gamma_{r-1,c}$와 $\Gamma_{r,c-1}$은 모두 홀짝이 맞지 않아
귀납 가정에 의해 $\mathcal N$이므로 $\Gamma_{r,c}\in\mathcal P$입니다. $r\not\equiv c$이면
$r\ge3$일 때 $\Gamma_{r-1,c}\in\mathcal P$이고, $r=2$일 때는 $c\ge3$이 홀수이므로
$\Gamma_{2,c-1}\in\mathcal P$입니다. $\square$

**보조정리 2.3** (논문의 `thm:2parts`; `isP_pair_iff`). $a\ge b\ge1$일 때 $[a,b]\in\mathcal P$일
필요충분조건은 $a$가 짝수인 것입니다.

*증명.* $a+b$에 대한 귀납법입니다. 가능한 수는 $[a]$, $[b]$, $[a-1,b-1]$ ($j\le b$인 열; $b=1$이면
이것은 행 $[a-1]$), 그리고 $a>b$이면 $[a-1,b]$ ($j>b$인 열)로 갑니다. $a$가 짝수이면 이들은 모두
$\mathcal N$입니다(행이거나, 첫 부분이 홀수인 두 부분 분할). $a$가 홀수이면, $a>b$일 때는
$[a-1,b]$로 가는 수가 이기고, $a=b$일 때는 $[a-1,a-1]$로 가는 수가 이깁니다($a=1$이면 이것은
$[\,]$). $\square$

**보조정리 2.4** (두 열; `isP_twoCol_iff`). $a\ge1$, $b\ge0$일 때 $[2^a,1^b]\in\mathcal P$일
필요충분조건은 $a+b$가 짝수인 것입니다.

*증명.* $a+b$에 대한 귀납법입니다(보조정리 2.3의 켤레이지만 직접 증명합니다). 가능한 수는
$[2^{a-1},1^b]$, $[2^a,1^{b-1}]$ ($b\ge1$일 때), 그리고 열 $[1^a]$, $[1^{a+b}]$로 갑니다. $a+b$가
짝수이면 이들은 모두 $\mathcal N$입니다(귀납 가정에 의해, 또는 $a=1$일 때
$[2^{a-1},1^b]=[1^b]$가 비어 있지 않은 열이기 때문). $a+b$가 홀수이면, $b\ge1$일 때
$[2^a,1^{b-1}]$이 $\mathcal P$이고, $b=0$이고 $a\ge3$일 때 $[2^{a-1}]$이 $\mathcal P$이며, $[2]$는
행입니다. $\square$

**보조정리 2.5** (`rank_even_iff`). $\operatorname{rank}\lambda$가 짝수일 필요충분조건은
$\ell(\lambda)\equiv\lambda_1\pmod2$입니다.

## 3. 훅 스택으로의 환원

$r\ge1$, $c\ge1$, $k=\ell(\mu)$에 대해
$$H(r,c,\mu)=[c,\,1+\mu_1,\,\dots,\,1+\mu_k,\,1^{r-1-k}]$$
로 둡니다(Lean: `hookStack r c μ = c :: (pad μ (r - 1)).map (· + 1)`, 여기서 `pad`는 뒤에 0을
붙입니다).

**명제 3.1** (`stack_hook`). $c\ge1$이라 합시다. 스택 $\Gamma_{r,c}\lhd\mu$가 정의될 필요충분조건은
$\ell(\mu)\le r-1$이고 $\mu_1\le c-1$인 것이며, 이때 $\Gamma_{r,c}\lhd\mu=H(r,c,\mu)$입니다.

*증명.* $\lambda=\Gamma_{r,c}$이면 $\lambda_1=c\ge1$이고 $\lambda_2\le1$이므로 $d(\lambda)=1$입니다
(`durfee_hook`). 첫 조건은 $1\le i\le k$에 대해 $\lambda_{1+i}=1$이라는 것인데,
$\lambda_{1+i}=1$인 것은 정확히 $i\le r-1$일 때이므로 이는 $k\le r-1$과 같습니다. 둘째 조건은
$c\ge1+\mu_1$입니다. 그러면 공식은
$[c,1+\mu_1,\dots,1+\mu_k,\lambda_{k+2},\dots,\lambda_r]=H(r,c,\mu)$가 됩니다. $\square$

행($r=1$)이면 조건이 $k=0$을, 열($c=1$)이면 $\mu_1=0$을 강제하므로, 두 경우 모두 $\mu=[\,]$입니다.
또한 $H(r,c,[\,])=\Gamma_{r,c}$입니다(`hookStack_nil`).

## 4. 훅 스택에서의 수

$k=\ell(\mu)\le r-1$, $\mu_1\le c-1$, $c\ge2$, $X=H(r,c,\mu)$라 합시다. $X$의 행 $2,\dots,k+1$을
*안쪽 행*, 행 $k+2,\dots,r$을 *다리 행*이라 부르고, $1\le j\le\mu_1$인 열 $j+1$을 *안쪽 열*,
$\mu_1<j<c$인 열 $j+1$을 *팔 열*이라 부릅니다. $\mu\setminus i$는 $\mu$에서 $i$번째 부분을 뺀 것,
$\mu-j$는 $\mu$에서 열 $j$를 지운 것입니다.

**보조정리 4.1** (`mem_moves_hookStack`; 구성 요소는 `eraseIdx_hookStack_zero`,
`eraseIdx_hookStack_succ`, `delCol_hookStack_one`, `delCol_hookStack_succ`, `delCol_eq_self`).
$X$의 모든 수는 다음 중 하나입니다.

| | 수 | 결과 |
|---|---|---|
| R1 | 행 1 | $[1+\mu_1,\dots,1+\mu_k,1^{r-1-k}]$; 여기서 열 1을 지우면 $\mu$ |
| Rin | 안쪽 행 $i+1$, $1\le i\le k$ | $H(r-1,c,\mu\setminus i)$ |
| Rleg | 다리 행 | $H(r-1,c,\mu)$ |
| C1 | 열 1 | $[c-1,\mu_1,\dots,\mu_k]$; 여기서 행 1을 지우면 $\mu$ |
| Cin | 안쪽 열 $j+1$, $1\le j\le\mu_1$ | $H(r,c-1,\mu-j)$ |
| Carm | 팔 열 | $H(r,c-1,\mu)$ |

거꾸로(`hookStack_eraseIdx_mem_moves`, `hookStack_delCol_mem_moves`), $1\le i\le r-1$이면
$H(r,c,\nu)$의 행 $i+1$을 지워 $H(r-1,c,\nu\setminus i)$에 도달하고, $1\le j\le c-1$이면 열 $j+1$을
지워 $H(r,c-1,\nu-j)$에 도달합니다. 여기서 $i>\ell(\nu)$이면 $\nu\setminus i=\nu$, $j>\nu_1$이면
$\nu-j=\nu$입니다. 아래에서 쓰는 응수는 이것들입니다.

## 5. 주정리

**정의 5.1** (`PChain`, `LocalEvenRank`). $\omega=\mu$이거나, 수 $\mu\to\nu\to\nu'$가 있어
$\nu'\in\mathcal P$이고 $\omega$가 $\nu'$에서 P-사슬로 도달 가능하면, $\omega$는 $\mu$에서
*P-사슬로 도달 가능*하다고 합니다. $\mu$에서 P-사슬로 도달 가능한 모든 분할($\mu$ 포함)의 랭크가
짝수이면 $\mu$가 $\mathrm{LER}(\mu)$를 만족한다고 합니다.

**정리 5.2** (`isP_hookStack`, `isP_hookStack_aux`로 증명). $\mu\in\mathcal P$가
$\mathrm{LER}(\mu)$를 만족하고, $r,c\ge2$, $r\equiv c\pmod2$, $\ell(\mu)\le r-1$,
$\mu_1\le c-1$이라 합시다. 그러면 $H(r,c,\mu)\in\mathcal P$입니다.

*증명.* 모든 $\mu$에 대해 동시에 $r+c$에 대한 강한 귀납법을 씁니다. $\mu=[\,]$이면 보조정리 2.2에
의해 $H(r,c,\mu)=\Gamma_{r,c}\in\mathcal P$입니다. 그렇지 않으면 $k=\ell(\mu)\ge2$이고
$\mu_1\ge2$이며(보조정리 2.1), $\mathrm{LER}(\mu)$와 보조정리 2.5에 의해 $k\equiv\mu_1\pmod2$입니다.
$X=H(r,c,\mu)$에서의 모든 수에 대해, 보조정리 4.1의 경우에 따라 $\mathcal P$-위치로 가는 응수를
줍니다. 아래에서 귀납 가정을 쓸 때마다 $r+c$는 2만큼 줄어듭니다. 그 부가 조건($r',c'\ge2$,
$r'\equiv c'$, $\ell\le r'-1$, 첫 부분 $\le c'-1$)은 $k\le r-1$, $\mu_1\le c-1$, $k,\mu_1\ge2$,
$\ell(\nu')\le\ell(\nu)$, $\nu'_1\le\nu_1\le\mu_1$에서 나오며, 열을 지운 뒤에는
$\nu'_1+1\le\nu_1$입니다(`part_one_delCol_lt`).

- **R1.** 응수: 열 1. 이렇게 하면 $\mu\in\mathcal P$에 도달합니다.
- **C1.** 응수: 행 1. 이렇게 하면 $\mu\in\mathcal P$에 도달합니다.
- **Rin.** 현재 위치는 $Y=H(r-1,c,\nu)$이고 $\nu=\mu\setminus i$는 $\mu$에서의 수이므로
  $\nu\in\mathcal N$입니다.
  - $r=3$. 이때 $k=2$이고 $1\le a\le\mu_1\le c-1$인 $\nu=[a]$이므로 $Y=[c,1+a]$입니다. 응수: 열 1,
    그러면 $[c-1,a]$에 도달합니다. $c\equiv r$이 홀수이므로 $c-1$은 짝수이고, 보조정리 2.3에 의해
    $[c-1,a]\in\mathcal P$입니다.
  - $r\ge4$. $\nu'\in\mathcal P$인 수 $\nu\to\nu'$를 하나 고릅니다. $\nu'$는 $\mu$에서 P-사슬로
    도달 가능하므로 $\mathrm{LER}(\nu')$가 성립합니다. $\nu'=\nu\setminus i'$이면 $Y$의 대응하는
    행으로 응수하여 $H(r-2,c,\nu')$에 도달합니다. $\nu'=\nu-j'$이면 $Y$의 열 $j'+1$로 응수하여
    $H(r-1,c-1,\nu')$에 도달합니다. 둘 다 귀납 가정에 의해 $\mathcal P$입니다.
- **Rleg.** 현재 위치는 $Y=H(r-1,c,\mu)$이고 $r\ge k+2$입니다.
  - $r\ge k+3$. 응수: 다른 다리 행, 그러면 $H(r-2,c,\mu)$에 도달합니다.
  - $r=k+2$이고 $c\ge\mu_1+2$. 응수: 마지막 열 $c$ ($Y$의 팔 열), 그러면 $H(r-1,c-1,\mu)$에
    도달합니다.
  - $r=k+2$이고 $c=\mu_1+1$. $r\equiv c$에서 $k\not\equiv\mu_1$이 나오므로 $\mu$의 랭크가
    홀수입니다. 이는 $\mathrm{LER}(\mu)$에 모순이므로 이 경우는 일어나지 않습니다.
- **Cin.** 현재 위치는 $Y=H(r,c-1,\nu)$이고 $\nu=\mu-j$이므로 $\nu\in\mathcal N$입니다.
  - $c=3$. 이때 $\mu_1=2$이므로 $\nu_1=1$이고(`part_one_delCol_eq`), $1\le a\le k\le r-1$인
    $\nu=[1^a]$입니다. 응수: 행 1, 그러면 $[2^a,1^{r-1-a}]$에 도달합니다. $r\equiv c$가 홀수이므로
    $a+(r-1-a)=r-1$은 짝수이고, 보조정리 2.4에 의해 이 위치는 $\mathcal P$입니다.
  - $c\ge4$. $\nu\to\nu'\in\mathcal P$를 고르면 $\mathrm{LER}(\nu')$가 성립합니다.
    $\nu'=\nu-j'$이면 열 $j'+1$로 응수하여 $H(r,c-2,\nu')$에 도달합니다.
    $\nu'=\nu\setminus i'$이면 대응하는 행으로 응수하여 $H(r-1,c-1,\nu')$에 도달합니다. 둘 다 귀납
    가정에 의해 $\mathcal P$입니다.
- **Carm.** 현재 위치는 $Y=H(r,c-1,\mu)$이고 $c\ge\mu_1+2$입니다.
  - $c\ge\mu_1+3$. 응수: 다른 팔 열, 그러면 $H(r,c-2,\mu)$에 도달합니다.
  - $c=\mu_1+2$이고 $r\ge k+2$. 응수: 다리 행, 그러면 $H(r-1,c-1,\mu)$에 도달합니다.
  - $c=\mu_1+2$이고 $r=k+1$. $r\equiv c$에서 $k\not\equiv\mu_1$, 즉 랭크가 홀수이므로
    $\mathrm{LER}(\mu)$에 모순입니다.

모든 수에 $\mathcal P$-위치로 가는 응수가 있으므로 $X\in\mathcal P$입니다. $\square$

두 모서리 경우만이 $\operatorname{rank}\mu$의 홀짝 자체가 쓰이는 곳입니다. $r=3$과 $c=3$에서 특별한
응수가 필요한 것은, 거기서는 $H(r-2,c,\nu')$나 $H(r,c-2,\nu')$가 행이나 열을 하나만 가지게 되기
때문입니다.

**따름정리 5.3** (`isP_stack_of_localEvenRank`). $\lambda\in\mathcal P$가 $\mathrm{LER}(\lambda)$를
만족하고, $r,c\ge1$, $\Gamma_{r,c}\in\mathcal P$이며 $\Gamma_{r,c}\lhd\lambda$가 정의되면
$\Gamma_{r,c}\lhd\lambda\in\mathcal P$입니다. (보조정리 2.2, 명제 3.1, 정리 5.2.)

**따름정리 5.4** (`statement_of_mainConjecture`). conj:main은 conj:bloby를 함의합니다.
$\mathcal P$-위치에서 P-사슬로 도달 가능한 분할은 모두 $\mathcal P$-위치이므로(`PChain.isP`,
`PChain.isPartition`), conj:main은 모든 $\mathcal P$-위치에 대해 $\mathrm{LER}$를 줍니다
(`localEvenRank_of_mainConjecture`).

## 6. conj:main이 얼마나 필요한가

7절에서 conj:main을 증명하므로 conj:bloby는 더 이상 이 절에 의존하지 않습니다. 이 절은 환원이
conj:main을 얼마나 적게 쓰는지 기록합니다. 따름정리 5.3은 $\lambda$에서 시작하는 P-사슬 위에서만 conj:main을 필요로 합니다. 어떤 수도 크기
$|\lambda|$, 행의 수 $\ell(\lambda)$, 가장 큰 부분 $\lambda_1$을 늘리지 않으므로, P-사슬도 이들을
늘리지 않습니다(`PChain.le_of_moves`). 이로부터 세 가지 결과가 나옵니다.

1. **크기 제한형** (`statement_of_mainConjecture_le`). 크기가 $N$ 이하인 모든 $\mathcal P$-위치의
   랭크가 짝수이면, $|\lambda|\le N$인 모든 $\lambda$와 크기에 상관없는 모든 훅에 대해 conj:bloby가
   성립합니다. 8절의 계산은 크기 $110$ 이하의 모든 분할에서 conj:main을 확인하므로,
   $|\lambda|\le110$인 모든 $\lambda$와 모든 훅 $\Gamma_{r,c}$에 대해 conj:bloby가 성립합니다. 이는
   무한한 족이지만, 그 유한한 입력은 Lean 증명이 아니라 계산입니다.
2. **두 행 또는 두 열, 무조건** (`statement_of_length_le_two`, `statement_of_part_one_le_two`).
   $\ell\le2$인 $\mathcal P$-위치는 $[\,]$이거나 $a$가 짝수인 $[a,b]$이므로(보조정리 2.1, 2.3)
   랭크 $|2-a|$가 짝수입니다(`even_rank_of_length_le_two`). $\lambda_1\le2$인 $\mathcal P$-위치는
   $[\,]$이거나 $a\ge1$이고 $a+b$가 짝수인 $[2^a,1^b]$이며(보조정리 2.1, 2.4), 랭크는
   $|a+b-2|$입니다(`even_rank_of_part_one_le_two`). 이 부류들은 P-사슬에 대해 닫혀 있으므로,
   $\ell(\lambda)\le2$ 또는 $\lambda_1\le2$인 모든 $\lambda$와 모든 훅에 대해 conj:bloby가
   성립합니다.
3. **수에 대해 닫힌 다른 부류.** 같은 논증은 수에 대해 닫혀 있고 그 안의 $\mathcal P$-위치가 모두
   짝수 랭크인 임의의 분할 부류에 적용됩니다. Mehat의 아티팩트(Zenodo
   [10.5281/zenodo.22070744](https://doi.org/10.5281/zenodo.22070744))는 부분이 여섯 개 이하인
   $\mathcal P$-위치와, 켤레를 통해 가장 큰 부분이 6 이하인 $\mathcal P$-위치를 분류하고, 이들이
   모두 짝수 랭크라고 밝힙니다. 따름정리 5.3과 합치면 $\ell(\lambda)\le6$ 또는 $\lambda_1\le6$일 때
   conj:bloby가 나옵니다. 우리는 그 아티팩트를 다시 검증하지 않았으므로, 이것은 이 디렉터리의
   결과가 아니라 그 아티팩트의 주장에서 나오는 귀결입니다.

## 7. 경계 단어 분류로부터 conj:main

Zijian Zeng의 프리프린트(9절 참고)는 모든 $\mathcal P$-위치의 분류를 제시하고 그로부터 conj:main을
이끌어 냅니다. 이 절은 그 분류를 Lean으로 형식화한 것입니다. 논증은 Zeng의 것입니다: 런 쌍
부호화, 통계량 $M$, 짝수 후속 위치 보조정리, 홀수 단어 지배 보조정리의 경우 분석. Lean 증명과
경우의 배치는 우리가 했습니다. 아래의 쌍대 $\delta$를 써서, 서로 거울상인 두 경우 중 하나만
증명하고 다른 하나는 그대로 얻습니다. 이 절의 보조 정리는 Lean 이름공간 `RunPairs`에 있습니다.

**런 쌍.** $\lambda\ne[\,]$의 서로 다른 부분을 $v_1>\dots>v_k>0$이라 하고, $v_i$가 $a_i$번
나타난다고 합시다. $v_{k+1}=0$으로 두고 $b_i=v_i-v_{i+1}$이라 하면, $\lambda$의 *런 쌍*은
$(a_1,b_1),\dots,(a_k,b_k)$이며 모든 성분이 양수입니다(`ValidPairs`). 영 도형의 경계를 오른쪽
위 모서리에서 왼쪽 아래 모서리까지 따라가며 아래로 한 칸 가면 $0$, 왼쪽으로 한 칸 가면 $1$을
적으면 경계 단어 $0^{a_1}1^{b_1}\cdots0^{a_k}1^{b_k}$를 얻습니다. 거꾸로 `ofPairs p`는
$b_i+\dots+b_k$가 $a_i$번 나타나는 분할입니다. 유효한 $p$에 대해 이것은 분할이고
(`isPartition_ofPairs`), 모든 분할은 어떤 유효한 $p$에 대해 `ofPairs p`이며(`exists_ofPairs`),
단어의 길이는 $\sum_i(a_i+b_i)=\ell(\lambda)+\lambda_1$입니다(`plen`,
`length_add_part_one_ofPairs`).

**보조정리 7.1** (`mem_moves_ofPairs`). `ofPairs p`에서 CRIM 수로 갈 수 있는 위치는 정확히
`PMove p q`인 $q$에 대한 `ofPairs q`이며, `PMove`는 다음 여섯 경우로 이루어집니다.

| `PMove` | 쌍 | CRIM 수 |
|---|---|---|
| `zeroDec` | $a_i\ge2$이면 $a_i\mapsto a_i-1$ | 길이가 두 번 이상 나타나는 행을 지움 |
| `zeroFirst` | $(1,b_1)$을 지움 | 길이 $v_1$인 유일한 행을 지움 |
| `zeroMerge` | $(a_{i-1},b_{i-1}),(1,b_i)\mapsto(a_{i-1},b_{i-1}+b_i)$ | 길이 $v_i$ ($i\ge2$)인 유일한 행을 지움 |
| `oneDec` | $b_i\ge2$이면 $b_i\mapsto b_i-1$ | $v_{i+1}<j\le v_i$인 열 $j$를 지움 |
| `oneLast` | $(a_k,1)$을 지움 | $v_k=1$일 때 열 1을 지움 |
| `oneMerge` | $(a_i,1),(a_{i+1},b_{i+1})\mapsto(a_i+a_{i+1},b_{i+1})$ | $v_i=v_{i+1}+1$일 때 열 $v_i$를 지움 |

단어로 보면 각 경우는 글자 하나를 지운 뒤 앞쪽의 1과 뒤쪽의 0을 떼어 냅니다. 모든 경우는
`plen`을 줄이고(`PMove.plen_lt`) 쌍의 유효성을 유지합니다(`PMove.validPairs`). 이것과
`isP_iff`를 합치면 `isP_ofPairs_iff_forall`을 얻습니다. 즉 `ofPairs p`가 $\mathcal P$-위치일
필요충분조건은 $p$에서 어떤 `PMove`로도 `ofPairs q`가 $\mathcal P$-위치인 $q$에 가지 못하는
것입니다.

**통계량 $M$.** 쌍 $(a,b)$는 $a=1$이고 $b$가 홀수이면 *A-좋음*, $a$가 홀수이고 $b=1$이면
*B-좋음*이라 합니다. 어느 쪽이든 $a+b$는 짝수입니다. A-좋은 쌍으로 이루어진 가장 긴 접두부의
길이를 $L$ (`endL`), B-좋은 쌍으로 이루어진 가장 긴 접미부의 길이를 $R$ (`endR`)이라 하고
$M=\min(k,L+R)$ (`endM`)로 둡니다. 예를 들어 $[4,2,2,2]$는 쌍이 $(1,2),(3,2)$이고 단어 길이가
$8$, $M=0$이며, $[3,2,1]$은 쌍이 $(1,1),(1,1),(1,1)$이고 $M=3$입니다. 쌍대 $\delta$
(`pdual`)는 리스트를 뒤집고 각 쌍의 두 성분을 바꿉니다. 분할로 보면 켤레이지만 증명은 이 사실을
쓰지 않습니다. $\delta$는 수를 수로 보내고(`PMove.pdual`), $L$과 $R$을 맞바꾸며, 길이와 $M$을
보존합니다(`plen_pdual`, `endM_pdual`).

**보조정리 7.2** (짝수 후속 위치; `endM_eq_of_even`). `plen p`와 `plen q`가 짝수이고
`PMove p q`이면 `endM p = endM q + 1`입니다.

*증명.* 수는 글자 하나를 지웁니다. 예외는 글자 $1+b_1$개를 지우는 `zeroFirst`와 $a_k+1$개를
지우는 `oneLast`입니다. 따라서 길이가 짝수로 남는 것은 첫 쌍이 A-좋을 때의 `zeroFirst`와 마지막
쌍이 B-좋을 때의 `oneLast`뿐입니다. A-좋은 첫 쌍이나 B-좋은 마지막 쌍을 지우면 $M$은 정확히
1 줄어듭니다(`endM_cons_aGood`, `endM_append_bGood`). $\square$

**보조정리 7.3** (`goodMove_of_even`). `plen p`가 짝수이고 `endM p`가 홀수이면, `plen q`와
`endM q`가 모두 짝수인 $q$로 가는 수가 있습니다.

*증명.* $M\ge1$이므로 $L\ge1$이거나 $R\ge1$입니다. 그쪽 끝의 쌍을 지웁니다. 길이는 짝수로 남고,
보조정리 7.2에 의해 새 $M$은 짝수입니다. 쌍대성에 의해 $L\ge1$인 경우만 다루면
충분합니다(`goodMove_of_endL`). $\square$

**보조정리 7.4** (홀수 단어 지배; `goodMove_of_odd`). $p$가 유효하고 `plen p`가 홀수이면,
`plen q`와 `endM q`가 모두 짝수인 $q$로 가는 수가 있습니다.

*증명.* 좋은 쌍은 길이가 짝수이므로, 모든 쌍이 A-좋은 접두부나 B-좋은 접미부에 들어 있다면
`plen p`는 짝수일 것입니다. 따라서 $p=P\,C\,S$로 쓸 수 있습니다. 여기서 $P$의 쌍은 A-좋고,
$S$의 쌍은 B-좋으며, 핵심부 $C$는 비어 있지 않고 A-좋지 않은 쌍으로 시작해 B-좋지 않은 쌍으로
끝납니다(`exists_split`, `Split`). 그러면 $L=|P|$, $R=|S|$, $M=L+R$입니다(`Split.endM_eq`).
아래에서 고르는 수는 글자 하나를 지우거나 $b$가 짝수인 쌍 $(1,b)$를 지우므로 새 길이는
짝수입니다. 남은 일은 새 $M$을 짝수로 만드는 것입니다. 거울상 경우는 $\delta$로
얻습니다(`Split.pdual`, `GoodMove.of_pdual`).

*$L+R$가 홀수인 경우.*

- *A 줄이기* (`goodMove_reduceA`): $P\ne[\,]$이고, $C$가 $a$가 짝수인 단일 쌍 $(a,1)$이 아닐
  때. $P$의 마지막 쌍 $(1,b')$에서 1을 하나 지웁니다. $b'\ge3$이면 새 쌍 $(1,b'-1)$은 A-좋지도
  B-좋지도 않으며 핵심부에 합류합니다. $b'=1$이면 그 1을 지울 때 $(1,1)$이 핵심부의 첫 쌍
  $(a,b)$와 합쳐져 $(1+a,b)$가 되고, 이것은 A-좋지 않습니다. $(1+a,b)$가 새 핵심부 전체이면
  B-좋지도 않은데, $b=1$이면 $a$가 홀수여야 하기 때문입니다. 어느 쪽이든 새 $M$은 $L+R-1$입니다.
- *B 줄이기*: $S\ne[\,]$이고, $C$가 $b$가 짝수인 단일 쌍 $(1,b)$가 아닐 때. 위의 거울상입니다.
- 그 밖의 경우, $P$와 $S$가 둘 다 비어 있지는 않으므로, $P=[\,]$이고 $b$가 짝수인
  $C=[(1,b)]$이거나 그 거울상입니다. $(1,b)$에서 1을 하나 지우면 리스트는 $(1,b-1)\,S$가 되고
  모든 쌍이 좋으므로 새 $M$은 $1+R=L+R+1$입니다(`goodMove_core_one_odd`).

*$L+R$가 짝수이고 핵심부가 쌍 하나 $(a,b)$인 경우.* 이 쌍은 A-좋지도 B-좋지도 않고 $a+b$는
홀수입니다.

- $a=1$이고 $b$가 짝수 (`goodMove_core_one_even`): 그 0을 지웁니다. $P=[\,]$이면 이 수는 쌍을
  없애고 $S$를 남기며 $M=R$입니다. 그렇지 않으면 $(1,b)$가 $P$의 마지막 쌍 $(1,b')$와 합쳐져
  A-좋은 쌍 $(1,b'+b)$가 되고, 새 $M$은 $L+R$입니다.
- $a\ge3$이 홀수이고 $b$가 짝수 (`goodMove_core_odd_even`): 0을 하나 지웁니다. 새 핵심부
  $(a-1,b)$는 A-좋지도 B-좋지도 않으므로 $M=L+R$입니다.
- $a$가 짝수이고 $b$가 홀수: 위 두 경우의 거울상입니다.

*$L+R$가 짝수이고 핵심부가 쌍 두 개 이상인 경우* (`goodMove_core_long`). 핵심부의 첫 쌍을
$(a,b)$, 핵심부의 나머지를 $C_1$이라 합시다.

- $a\ge3$이거나, $a=2$이고 $b$가 짝수이면 0을 하나 지웁니다. $a=2$이고 $b\ge3$이 홀수이면 1을
  하나 지웁니다. $(a,b)=(2,1)$이면 그 1을 지우며, 그러면 다음 핵심부 쌍 $(a',b')$와 합쳐져
  $(2+a',b')$가 됩니다. 새 핵심부의 첫 쌍은 A-좋지 않고 마지막 쌍은 여전히 B-좋지 않으므로
  ($(2+a',b')$가 B-좋은 것은 $(a',b')$가 B-좋을 때뿐입니다) $M=L+R$입니다.
- $a=1$이면 $b$는 짝수입니다. 두 수를 비교합니다. 하나는 $(1,b)$의 0을 지우는 수(쌍 하나인
  경우와 같음)이고, 다른 하나는 1을 하나 지워 A-좋은 쌍 $(1,b-1)$을 만드는 수입니다. 두 수 모두
  A-좋은 블록 뒤에 $C_1S$를 남기며, 둘째 수의 블록이 쌍 하나만큼 깁니다. $C_1$은 B-좋지 않은
  쌍으로 끝나므로 두 $M$ 값은 정확히 1 차이가 나고(`endM_prefix_barrier`), 따라서 둘 중 하나는
  짝수입니다. $\square$

**정리 7.5** (`pairs_classification`). 쌍 리스트에 대한 술어 $G$가 모든 유효한 $p$에 대해
"$G(p)$가 참일 필요충분조건은 `PMove p q`인 모든 $q$에서 $G(q)$가 거짓인 것"을 만족한다고
합시다. 그러면 모든 유효한 $p$에 대해
$$G(p)\iff \texttt{plen }p\text{와 }\texttt{endM }p\text{가 모두 짝수}$$
입니다.

*증명.* `plen p`에 대한 강한 귀납법입니다. 둘 다 짝수이면, 모든 수는 홀수 길이로 가거나
보조정리 7.2에 의해 $M$이 홀수인 짝수 길이로 가므로, 귀납 가정에 의해 $G$를 만족하는 위치로 가는
수가 없습니다. 길이가 짝수이고 $M$이 홀수이면 보조정리 7.3이, 길이가 홀수이면 보조정리 7.4가
$G$를 만족하는 위치로 가는 수를 줍니다. $\square$

**따름정리 7.6** (`isP_ofPairs_iff`). 유효한 $p$에 대해 `ofPairs p`가 $\mathcal P$-위치일
필요충분조건은 $\ell+\lambda_1$과 $M$이 모두 짝수인 것입니다. (정리 7.5에
$G(p)=$ `IsP (ofPairs p)`를 넣고 `isP_ofPairs_iff_forall`을 씁니다.)

**따름정리 7.7** (`mainConjecture_holds`). conj:main이 성립합니다. $\mathcal P$-위치
$\lambda=$ `ofPairs p`는 $\ell(\lambda)+\lambda_1$이 짝수이므로 랭크가 짝수입니다(보조정리 2.5).

**따름정리 7.8** (`statement_holds`). conj:bloby가 성립합니다(따름정리 5.4와 7.7).

## 8. 계산

모든 프로그램은 [`programs/`](programs/)에 있으며 Python 표준 라이브러리나 C99만 씁니다. 이
프로그램들은 위 명제들에 대한 증거이며, Lean 증명은 어느 것도 쓰지 않습니다.

- [`crim_check.py`](programs/crim_check.py)는 행과 열의 모든 수를 시도해 $|\lambda|\le N$인 모든
  분할의 $\mathcal P/\mathcal N$을 계산하고, conj:main을 확인하며, 스택 크기가 $N$ 이하인 모든
  쌍($\mu\in\mathcal P$, $\Gamma_{r,c}\in\mathcal P$)에 대해 conj:bloby를 확인합니다. 스택은
  논문의 일반 정의(더피 길이, 조건, 공식)로 계산하고, 명제 3.1과 일치하는지도 확인합니다.
  [`logs/crim_check_py_n60.log`](logs/crim_check_py_n60.log): $N=60$, 분할 6,639,349개,
  $\mathcal P$-위치 1,870,422개, 랭크가 홀수인 것 0개. 계산한 23,194,397쌍 가운데 964,855개의
  스택이 정의되며 모두 $\mathcal P$입니다.
- [`crim_check.c`](programs/crim_check.c)는 독립적인 구현입니다. 분할을 사전식 순위로 색인하고,
  위치마다 비트 하나를 두며, 결과가 서로 다른 수만 하나씩 시도합니다. conj:bloby는 비어 있지 않은
  $X$와 $X=H(r,c,\mu)$인 세 쌍 $(r,c,\mu)$ 사이의 전단사를 통해 확인합니다.
  [`logs/crim_check_c_n110.log`](logs/crim_check_c_n110.log): $N=110$, 분할 5,465,153,652개,
  $\mathcal P$-위치 1,534,701,211개, 랭크가 홀수인 것 0개, 두 $\mathcal P$-위치로 만든 정의된 스택
  783,733,098개가 모두 $\mathcal P$; 333초. 크기별 개수는 $n\le60$인 모든 $n$에서 Python
  프로그램과 일치합니다.
- [`strategy_check.py`](programs/strategy_check.py)는 정리 5.2의 증명을 재현합니다.
  $\mu\ne[\,]$이고 $|X|\le N$인 모든 스택 $X=H(r,c,\mu)$, $X$에서의 모든 수, Rin과 Cin 경우의 모든
  $\mathcal P$-자식 $\nu'$에 대해 정해진 응수를 두고, 그 응수가 합법적이고 명시된 모양이며
  $\mathcal P$-위치에 도달하는지 확인합니다. 불가능한 경우는 한 번도 일어나서는 안 됩니다. 크기
  $N$ 이하의 모든 훅에 대해 보조정리 2.2도 확인합니다.
  [`logs/strategy_check_n60.log`](logs/strategy_check_n60.log): $N=60$, 스택 964,014개, 응수
  150,828,030개, 실패 0. 경우별 개수는 예상대로 전치에 대해 대칭입니다(예를 들어 특별한 경우
  $r=3$과 $c=3$에서 응수가 각각 2,700개).
- [`boundary_word_check.py`](programs/boundary_word_check.py)는 `crim_check.py`의 정확한
  $\mathcal P/\mathcal N$ 표를 Zeng의 경계 단어 규칙(7절)과 비교합니다.
  [`logs/boundary_word_check_n60.log`](logs/boundary_word_check_n60.log): $N=60$, 분할
  6,639,349개 전부에서 불일치 0.

$|\lambda|\le50$에서 프로그램들은 분할 1,295,971개와 $\mathcal P$-위치 365,327개를 줍니다. 논문도
같은 크기까지 conj:main을 확인했다고 보고합니다.

## 9. 관련 연구와 정오표

- **논문**(Bašić, Gottlieb, Krnc)은 `lem:hook`, `thm:2parts`, `thm:3parts`를 증명하고,
  $|\lambda|\le50$과 여러 족에 대해 conj:main을 확인하며, conj:bloby가 논문의 `prop:hooksquare`를
  함의한다고 지적합니다. 5절의 후수 전략은 이 프로젝트의 이전 탐색 실행에서 개요가 나왔고, 4–5절이
  이를 완성하고 기계로 검증했습니다. 새로움은 주장하지 않습니다.
- **`thm:3parts`의 정오.** 서술된 대로라면 이 정리는 $[\lambda_1,\lambda_2,\lambda_3]\in\mathcal P$일
  필요충분조건이 $\lambda_1,\lambda_2$가 홀수이고 $\lambda$가 훅이거나 $\lambda_3>1$인 것이라고
  말합니다. 여기에는 $[1,1,1]=\Gamma_{3,1}$이 포함되는데, 이것은 열이므로 $\mathcal N$입니다
  (`lem:hook`은 $c>1$을 요구합니다). 여기의 어떤 결과도 `thm:3parts`에 의존하지 않습니다.
- **Mehat** (Zenodo [10.5281/zenodo.22070744](https://doi.org/10.5281/zenodo.22070744),
  2026-08-23; Lean 파일은 CC0, 스크립트는 MIT): 부분이 여섯 개 이하이거나 가장 큰 부분이 6 이하인
  경우의 인증된 분류입니다. 6절을 참고하십시오. 그 코드는 여기서 쓰지 않습니다.
- **the-omega-institute/trureturing**에는 같은 논문의 다른 두 추측을 반박하는 Lean
  인증서(`CrimRectairSquareBoundaryRefutation`, `CrimGrundyRefutation`)가 있습니다. conj:main이나
  conj:bloby에 관한 것은 없습니다.
- **Zeng.** Zijian Zeng, *A Boundary-Word Classification of Losing Positions in CRIM*
  (2026-08-29 날짜, 심사 전; GitHub `ArtificialZeng/AI-Has-Taste`, 폴더
  `reproducible_source_code/BigWIN2/BW2-B02-P10`)은 완전한 분류를 제시합니다. $\lambda$를 경계
  단어 $0^{a_1}1^{b_1}\cdots0^{a_k}1^{b_k}$로 부호화하고($a_i$는 $i$번째로 큰 서로 다른 부분의
  중복도, $b_i$는 다음 부분까지의 차이), $a_i=1$이고 $b_i$가 홀수인 쌍으로 이루어진 가장 긴
  접두부의 길이를 $L$, $a_i$가 홀수이고 $b_i=1$인 쌍으로 이루어진 가장 긴 접미부의 길이를 $R$,
  $M=\min(k,L+R)$이라 하면, $\lambda\in\mathcal P$일 필요충분조건은 $\ell(\lambda)+\lambda_1$과
  $M$이 모두 짝수인 것입니다. Zeng은 이로부터 conj:main을 이끌어 내며, 프리프린트는 conj:bloby를
  언급하지 않습니다. 7절은 Zeng의 증명을 형식화해 Lean에서 conj:main을 얻고, 따름정리 5.4와 합쳐
  conj:bloby를 얻습니다. 또한 크기 60 이하의 분할 6,639,349개 전부에 대해 이 분류를 정확한
  $\mathcal P/\mathcal N$ 표와 비교해 불일치가 없음을 확인했습니다(`boundary_word_check.py`).
