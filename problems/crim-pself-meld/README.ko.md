[English](README.md) | **한국어**

# CRIM: 지는 두꺼운 훅의 멜드, 홀짝 자기켤레 분할, 미제르 규칙

Ina Bašić, Eric Gottlieb, Matjaž Krnc의 *CRIM: A Natural Game on Integer Partitions*
([arXiv:2606.16828v1](https://arxiv.org/abs/2606.16828), 2026-06-15)는 열–행 비편향
병합(Column–Row Impartial Merge, CRIM)을 연구합니다. 위치는 정수 분할 $\lambda$이고, 한 수는 영
도형에서 행 하나나 열 하나를 지우고 남은 조각을 다시 붙입니다. 정상 규칙을 따르므로 빈 분할
$[\,]$은 $\mathcal P$-위치("지는 위치")입니다. 여기서 증명하는 두 추측은 이 저자들의 것이며,
논문 5절(Future Work)에 실려 있습니다.

> A meld of losing thick hooks is losing.

> **conj:pself.** A parity self-conjugate partition is in $\mathcal N$ if and only if it is the
> stack of odd self-conjugate hooks and $[1]$.

논문은 conj:pself를 $n\le50$까지 확인했습니다. 두 추측 모두 열린 문제로 올라 있습니다
([확인한 출처](#확인한-출처) 참고).

이 디렉터리는 두 추측을 모두 Lean으로 증명합니다. 두 증명 모두 경계 단어에 의한 모든
$\mathcal P$-위치의 분류에서 짧게 따라 나오는 따름정리이며, 이 분류는 **Zijian Zeng**이 심사 전
프리프린트에서 제시하고 증명했습니다([관련 연구와 감사](#관련-연구와-감사) 참고). 자매 문제
[crim-hook-stacks](../crim-hook-stacks/README.ko.md)가 Zeng의 분류를 `isP_ofPairs_iff`로 Lean에서
형식화했고, 이 디렉터리는 그 위에 쌓습니다. 두 증명의 경로는 이 프로젝트의 이전 탐색 실행이
찾았습니다. 이 작업은 아직 사람이 검토하지 않았습니다.

이 디렉터리는 미제르 $\mathcal P$-위치의 분류도 증명합니다([미제르 규칙](#미제르-규칙)). 이 분류
규칙은 같은 탐색 실행이 제안했습니다. 논문은 미제르 규칙에 대해 콘웨이 쌍을 통해서만 묻고,
우리는 이 분류의 이전 진술을 찾지 못했습니다. 마지막으로, 논문의 conj:hookswap을 비어 있지
않은 분할에 대해 진술하고, 논문의 `thm:cgpairshooks`에서 따라 나오는 방향을 증명합니다. 반대
방향은 증명하지 못했습니다([conj:hookswap](#conjhookswap-증명되지-않음)).

## 명제

분할 $\mu=[\mu_1,\dots,\mu_k]$와 $\lambda=[\lambda_1,\dots,\lambda_m]$에 대해 논문의
*멜드*(§2.1)는 다음과 같습니다.

\[
\mu\diamond\lambda=[\mu_1+\lambda_1,\dots,\mu_1+\lambda_m,\mu_1,\dots,\mu_k].
\]

멜드는 결합법칙을 만족하고 항등원은 $[\,]$입니다. *두꺼운 훅*(§2.2)은 $r>a\ge2$, $c>b\ge2$인
$\Gamma^{a,b}_{r,c}=[c^a,b^{r-a}]$입니다.

**멜드 추측.** $H_1,\dots,H_n$($n\ge0$)이 $\mathcal P$에 속하는 두꺼운 훅이면
$H_1\diamond\cdots\diamond H_n\in\mathcal P$입니다.

모든 $k\ge1$에 대해 $\lambda_k\equiv\lambda'_k\pmod 2$이면 분할을 *홀짝 자기켤레*라고 합니다.
여기서 $\lambda'_k$는 $k$ 이상인 부분의 개수이므로, $k$가 크면 양쪽 모두 $0$입니다. 자기켤레인
훅은 $\Gamma_{r,r}=[r,1^{r-1}]$이고, $\lhd$는 더피 길이로 정의되는 논문의 스택입니다
([상세 §1](DETAILS.ko.md#1-정의와-명제)).

**conj:pself.** 홀짝 자기켤레 분할 $\lambda$가 $\mathcal N$-위치일 필요충분조건은 어떤
$j\ge0$과 홀수 $r_1,\dots,r_j$에 대해 모든 스택이 정의되면서

\[
\lambda=\Gamma_{r_1,r_1}\lhd\Gamma_{r_2,r_2}\lhd\cdots\lhd\Gamma_{r_j,r_j}\lhd[1]
\]

인 것입니다. 예를 들어 $[1]$, $[3,2,1]=\Gamma_{3,3}\lhd[1]$, $[5,2,1^3]=\Gamma_{5,5}\lhd[1]$,
$[5,4,3,2,1]=\Gamma_{5,5}\lhd\Gamma_{3,3}\lhd[1]$이 이런 스택입니다.

## 검증된 결과

Lean 모듈 [`CrimPselfMeld.lean`](../../AgenticConjectures/CrimPselfMeld.lean)은 다음을 커널로
검증하며, `sorry`, 추가 공리, `native_decide`를 쓰지 않습니다.

| 정리 | 내용 |
|---|---|
| `meldConjecture_holds` | 멜드 추측(`meldConjecture`): 지는 두꺼운 훅들의 멜드는 조각 수와 괄호 묶는 방식에 관계없이 모두 $\mathcal P$-위치입니다. |
| `isP_meldAll` | 리스트로 주어진 오른쪽 결합 멜드 $H_1\diamond(H_2\diamond(\cdots\diamond H_n))$에 대한 같은 명제. |
| `pselfConjecture_holds` | conj:pself (`pselfConjecture`). |
| `paritySelfConj_and_not_isP_iff` | 조금 더 강한 형태: 분할이 홀짝 자기켤레이면서 $\mathcal N$에 속할 필요충분조건은 홀수 자기켤레 훅들과 $[1]$의 스택인 것입니다. |
| `oddHookStack_iff` | 이런 스택은 런 쌍이 $(1,o_1),\dots,(1,o_j),(1,1),(o_j,1),\dots,(o_1,1)$(모든 $o_i$는 홀수)인 분할과 정확히 같습니다. 특히 모두 자기켤레입니다(`conjPart_of_oddHookStack`). |
| `pselfConjecture_anyBracketing` | 스택의 괄호를 어떻게 묶어도 성립하는 conj:pself. `stack_hook_assoc`에 따르면 공집합이 아닌 모든 분할 $\mu$에 대해 $(\Gamma_{r,c}\lhd\mu)\lhd\nu=\Gamma_{r,c}\lhd(\mu\lhd\nu)$이고 한쪽이 정의되는 것과 다른 쪽이 정의되는 것이 동치이므로, 어떤 괄호 묶기도 오른쪽 결합 스택과 같은 결과를 줍니다(`exists_hookTree_iff`). |
| `meld_assoc`, `melds_iff` | 멜드는 항등원이 $[\,]$인 결합 연산이므로 멜드의 괄호 묶는 방식은 상관없습니다. |
| `misereP_iff`, `misereP_iff_isP` | 미제르 규칙: 분할이 미제르 $\mathcal P$-위치일 필요충분조건은 "정상 규칙의 $\mathcal P$-위치이다"와 "덮였다" 중 정확히 하나가 성립하는 것입니다([미제르 규칙](#미제르-규칙) 참고). |
| `isP_thickHook_iff` | 두꺼운 훅이 $\mathcal P$에 속할 필요충분조건은 $r\equiv c\pmod 2$이며, 이는 논문 `thm:thick-hook`의 $\mathcal P/\mathcal N$ 부분입니다. |
| `conwayPair_of_eeHook` | conj:hookswap의 $(\Leftarrow)$ 방향: 짝수×짝수 훅은 모두 콘웨이 쌍 $(0,1)$을 가집니다. 이는 `misere_hook`에 기댑니다. 훅 $\Gamma_{r,c}$의 미제르 그런디 값이 $0$일 필요충분조건은 $r$와 $c$가 홀수인 것이고, $1$일 필요충분조건은 둘 다 짝수인 것이며, 논문의 `thm:cgpairshooks`도 그렇게 말합니다. |
| `hookswapConjecture_iff`, `covered_of_conwayPair` | 비어 있지 않은 분할에 대한 conj:hookswap(`hookswapConjecture`, 증명되지 않음)은 $(\Rightarrow)$ 방향과 동치이고, 콘웨이 쌍이 $(0,1)$인 위치는 덮였으며 서로 다른 부분 크기의 수가 짝수입니다. |
| `nil_conwayPair` | $[\,]$의 콘웨이 쌍은 $(0,1)$이지만 $[\,]$은 훅이 아니므로, conj:hookswap에는 $\lambda\ne[\,]$이 필요합니다. |

**증명의 흐름.** 분할을 경계 단어의 런 길이로 부호화합니다. 런 쌍
$(a_1,b_1),\dots,(a_k,b_k)$에서 $a_i$는 $i$번째로 큰 부분 크기를 가진 행의 수이고, $b_i$는 다음
크기까지 줄어드는 양입니다. Zeng의 분류에 따르면 $\lambda\in\mathcal P$일 필요충분조건은 경계 길이
$\ell(\lambda)+\lambda_1$과 끝 벗기기 통계량 $M=\min(k,L+R)$가 모두 짝수인 것입니다. 여기서 $L$은
맨 앞에 이어지는 $(1,\text{홀수})$ 쌍의 수, $R$은 맨 뒤에 이어지는 $(\text{홀수},1)$ 쌍의
수입니다.

- *멜드.* 멜드는 런 쌍을 이어 붙이는 연산이고, 두꺼운 훅의 런 쌍은 $a,b\ge2$인
  $(a,c-b),(r-a,b)$입니다. 따라서 두꺼운 훅들의 멜드에서는 $L=R=0$, 즉 $M=0$이고 경계 길이는
  그대로 더해집니다.
- *conj:pself.* 켤레를 취하면 런 쌍의 순서가 뒤집히고 각 쌍의 두 성분이 바뀝니다. $L$은 맨
  위에서부터 차이 $\lambda_i-\lambda_{i+1}$이 홀수인 행이 이어지는 수이므로, 홀짝 자기켤레
  분할에서는 $L=R$이고 경계 길이가 짝수입니다. $L+R<k$이면 $M=2L$이 짝수이므로
  $\lambda\in\mathcal P$입니다. 그렇지 않으면 모든 런 쌍의 성분이 홀수이고, 홀짝 자기켤레성이
  자기켤레성을 강제하며, $M=k$이고 런 쌍이 위의 모양($k=2j+1$은 홀수)이 되므로
  $\lambda\in\mathcal N$입니다. 이것들이 바로 그 스택입니다.

[DETAILS.ko.md](DETAILS.ko.md)에 두 증명을 단계마다 Lean 이름과 함께 적었습니다.

## 계산 증거

[`programs/pself_meld_check.py`](programs/pself_meld_check.py)는 독립적인 전수 검사입니다. 게임
재귀로 CRIM을 직접 풀며, Zeng의 규칙과 비교할 때를 빼면 Lean 증명이나 런 쌍 부호화를 쓰지
않습니다.

| 크기 $\le N$인 모든 분할에 대해 확인하는 것 | $N=50$ 결과([로그](logs/pself_meld_check_n50.log)) |
|---|---|
| 정확한 $\mathcal P/\mathcal N$ 표; Zeng의 규칙 | 분할 1,295,971개, $\mathcal P$ 365,327개; Zeng의 규칙이 모두 일치 |
| `thm:thick-hook`의 $\mathcal P/\mathcal N$ 부분 | 두꺼운 훅 1,714개, $\mathcal P$ 844개; 일치 |
| 멜드 추측: 지는 두꺼운 훅들의 모든 멜드 | 멜드 1,732개(조각이 둘 이상인 것 888개), 모두 $\mathcal P$ |
| 멜드는 항등원이 $[\,]$인 결합 연산 | 크기 $\le6$인 분할의 세 쌍 27,000개 모두 |
| "스택"의 12가지 해석에서의 conj:pself | 홀짝 자기켤레 분할 3,559개, 그중 $\mathcal N$ 56개; 여기서 쓰는 해석은 오른쪽 결합, 왼쪽 결합, 임의의 괄호 묶기 모두에서 정확히 일치 |
| 아래의 미제르 분류 | 미제르 $\mathcal P$-위치 365,204개, 덮인 분할 23,447개; 실패 0 |
| 비어 있지 않은 분할에 대한 conj:hookswap | $\mathrm{cp}([\,])=(0,1)$; 콘웨이 쌍이 $(0,1)$인 비어 있지 않은 분할 300개가 짝수×짝수 훅 300개와 정확히 같음 |

실행에는 26초와 약 470 MB가 듭니다. 맞지 않는 해석은 [명제의 충실성](#명제의-충실성)에
적었습니다.

## 미제르 규칙

미제르 규칙에서는 마지막 수를 두는 사람이 지므로 $[\,]$은 $\mathcal N$-위치입니다. $k$를
$\lambda$의 서로 다른 부분 크기의 수, $L$을 맨 위에서부터 차이 $\lambda_i-\lambda_{i+1}$이
홀수인 행이 이어지는 수($\lambda_{\ell+1}=0$), $R$을 $\lambda'$에 대한 같은 수라고 합시다.
$L+R\ge k$이면 $\lambda$가 *덮였다*고 합니다. 이 프로젝트의 이전 탐색 실행이 다음 규칙을
제안했고, 모듈이 이를 증명합니다(`misereP_iff`, `misereP_iff_isP`).

> $\lambda$가 미제르 $\mathcal P$-위치일 필요충분조건은 "$\lambda$가 정상 규칙의
> $\mathcal P$-위치이다"와 "$\lambda$가 덮였다" 중 정확히 하나가 성립하는 것입니다.

예를 들어 $[1]$과 $[3]$은 덮인 정상 규칙의 $\mathcal N$-위치이므로 미제르 $\mathcal P$-위치이고,
$[2,1]$은 덮였으면서 정상 규칙의 $\mathcal P$-위치이므로 미제르 $\mathcal N$-위치입니다.
증명([상세 §5](DETAILS.ko.md#5-미제르-규칙))은 두 가지 사실을 씁니다. 덮인 분할의 경계 길이는
짝수이고, 경계 길이가 짝수인 두 위치 사이의 수는 끝의 런 쌍 하나를 없앱니다. 경계 길이가 홀수인
위치에서는 Zeng 증명의 수를 다시 쓰되 세 경우를 바꿉니다. 논문은 미제르 규칙에 대해 콘웨이 쌍을
통해서만 묻고, 우리는 이 분류의 이전 진술을 찾지 못했습니다. 위의 프로그램도 크기 50 이하의 모든
분할에서 이 분류를 확인합니다.

## conj:hookswap (증명되지 않음)

논문(§2)은 미제르 그런디 값 $G^-$를 끝 위치 $[\,]$에서 값이 $1$인 스프라그–그런디 재귀로
정의하고, *콘웨이 쌍*을 $\mathrm{cp}(\lambda)=(\mathrm{sg}(\lambda),G^-(\lambda))$로 정의합니다.
따라서 $G^-(\lambda)=0$은 $\lambda$가 미제르 $\mathcal P$-위치라는 뜻이고,
$\mathrm{cp}(\lambda)=(0,1)$은 $\lambda\in\mathcal P$이고 $G^-(\lambda)=1$이라는 뜻입니다. 논문
5절의 추측은 다음과 같습니다.

> **conj:hookswap.** A partition $\lambda$ has Conway pair $(0,1)$ if and only if $\lambda$ is
> an even-by-even hook.

짝수×짝수 훅은 $r$와 $c$가 양의 짝수인 $\Gamma_{r,c}=[c,1^{r-1}]$입니다. 쓰인 그대로라면 이
명제는 $[\,]$에서 성립하지 않습니다. 논문 스스로 $\mathrm{cp}([\,])=(0,1)$을 계산하는데
$[\,]$은 훅이 아니기 때문입니다(`nil_conwayPair`). 이는 반박이 아니라 문구의 경계 사례이며,
모듈은 추측을 비어 있지 않은 분할에 대해 진술합니다(`hookswapConjecture`). 증명한 것은 다음과
같습니다.

- $(\Leftarrow)$는 모든 훅의 콘웨이 쌍을 계산하는 논문의 `thm:cgpairshooks`에서 따라 나옵니다.
  모듈은 필요한 부분을 증명합니다. 훅에서 한 수로 갈 수 있는 위치(옵션)는 네 종류이고, 이를
  써서 $r+c$에 관한 귀납법으로 $G^-(\Gamma_{r,c})=0$일 필요충분조건은 $r$와 $c$가 홀수인 것,
  $G^-(\Gamma_{r,c})=1$일 필요충분조건은 $r$와 $c$가 짝수인 것임을 보입니다(`misere_hook`). 훅의
  정상 규칙 $\mathcal P/\mathcal N$ 여부와 합치면 `conwayPair_of_eeHook`이 되므로, 추측은
  $(\Rightarrow)$ 방향과 동치입니다(`hookswapConjecture_iff`).
- $(\Rightarrow)$를 향하여: 콘웨이 쌍이 $(0,1)$인 위치는 덮였고 서로 다른 부분 크기의 수 $k$가
  짝수입니다(`covered_of_conwayPair`). 이런 위치에는 $G^-=0$인 옵션이 있으므로 미제르
  $\mathcal P$-위치가 아닌데, 미제르 규칙에 따르면 덮이지 않은 정상 규칙의 $\mathcal P$-위치는
  미제르 $\mathcal P$-위치입니다. 따라서 이 위치는 덮였고, Zeng의 규칙에서 $M=k$이며,
  $\mathcal P$에 속하므로 $M$은 짝수입니다.

$(\Rightarrow)$ 방향은 증명하지 못했습니다. 미제르 값이 $1$인 위치를 이 방향을 닫을 만큼
설명하는 규칙을 찾지 못했습니다. 위의 프로그램은 크기 50 이하의 모든 분할에서 비어 있지 않은
경우의 명제를 확인합니다.

## 재현

아래 명령은 이 디렉터리에서 실행합니다. 첫 번째는 [`status.yaml`](status.yaml)의 CI 항목이며,
실행 시간은 2026-10-25에 여러 작업이 함께 돌던 Apple silicon 머신에서 잰 것입니다.

```bash
python3 programs/pself_meld_check.py --max-n 35 --misere --hookswap
```

```bash
python3 programs/pself_meld_check.py --max-n 50 --misere --hookswap
```

각각 약 1초와 26초 걸립니다. 두 번째 명령이
[`logs/pself_meld_check_n50.log`](logs/pself_meld_check_n50.log)를, 첫 번째 명령이
[`logs/pself_meld_check_n35.log`](logs/pself_meld_check_n35.log)를 만들었습니다.

## 명제의 충실성

Formal Conjectures에 해당 명제가 없으므로 두 형식 명제(`meldConjecture`, `pselfConjecture`)는
우리가 작성한 것입니다. 각 정의를 TeX 원문과 대조했으며, [DETAILS.ko.md §1.1](DETAILS.ko.md#11-해석)에
모든 해석을 정리했습니다.

- 위치, 수, $\mathcal P$는 crim-hook-stacks의 것을 그대로 씁니다. 분할은 양의 자연수로 이루어진
  약감소 리스트(`IsPartition`)이고, `part l i`는 $\lambda_i$(1부터 세고 끝을 넘으면 $0$)이며,
  `IsP`는 $[\,]$을 지는 위치로 둔 정상 규칙의 $\mathcal P$ 여부입니다.
- `meld μ lam`은 논문의 공식 그대로이며, $\mu=[\,]$이면 $\mu_1=0$입니다. `thickHook r c a b`는
  $[c^a,b^{r-a}]$이고, `ThickParams`는 논문의 조건 $r>a\ge2$, $c>b\ge2$와 정확히 같습니다.
- "지는 두꺼운 훅들의 멜드"는 `Melds S`의 원소, 곧 지는 두꺼운 훅들을 이항 멜드로 어떤 괄호
  묶기로든 닫은 집합의 원소입니다. 두꺼운 훅 하나와 빈 멜드 $[\,]$도 포함하는데, $[\,]$은
  $\mathcal P$이므로 포함해도 잃는 것이 없습니다. `melds_iff`에 따르면 이는 유한 리스트의 오른쪽
  결합 멜드 전체와 같습니다.
- 홀짝 자기켤레성은 논문의 "for every $k$"대로 모든 $k\ge1$에서 $\lambda_k$와 $\lambda'_k$를
  비교하며, 끝을 넘으면 양쪽 모두 $0$입니다. $k\le\min(\ell(\lambda),\lambda_1)$에서만 비교하면
  conj:pself는 $[3]$에서 거짓이 됩니다.
- "홀수 자기켤레 훅"은 $r$이 홀수인 $\Gamma_{r,r}$입니다. 훅 $\Gamma_{r,c}$의 켤레는
  $\Gamma_{c,r}$이므로 자기켤레인 훅은 $\Gamma_{r,r}$이고, 이들의 크기 $2r-1$은 모두 홀수입니다.
  따라서 "홀수"는 $r$을 가리켜야 하며, 논문의 관찰(Observation)에서 "odd hooks"
  $\Gamma_{2m+1,2m'+1}$을 쓰는 방식과도 맞습니다.
- "the stack of odd self-conjugate hooks and $[1]$"은
  $\Gamma_{r_1,r_1}\lhd(\Gamma_{r_2,r_2}\lhd(\cdots\lhd(\Gamma_{r_j,r_j}\lhd[1])))$, $j\ge0$으로
  읽습니다. $[1]$이 마지막에 오고 중간의 모든 스택이 정의되어야 합니다(`OddHookStack`). 스택은
  훅 공식이 아니라 논문의 일반적인 더피 길이 정의(crim-hook-stacks의 `stack`)입니다. 논문은 이런
  스택을 괄호 없이 쓰고, 스택 연산이 결합적이라고 말하며, 관찰에서 $[1]$을 마지막에 둡니다.
  Lean 명제는 오른쪽 결합을 쓰며, `pselfConjecture_anyBracketing`이 모든 괄호 묶기에 대해
  추측을 증명하므로 이 선택은 결과에 영향을 주지 않습니다.
- 다른 해석은 $n\le50$에서 맞지 않습니다. 모든 자기켤레 훅 $\Gamma_{r,r}$을 허용하면
  $\mathcal P$인 $[2,2]=\Gamma_{2,2}\lhd[1]$에서 틀리고, $[1]$이 마지막이라는 조건을 빼면
  $\mathcal P$인 $[3,1,1]=\Gamma_{3,3}$에서 틀립니다.
- $j=0$도 허용합니다. $[1]$ 하나만으로도 스택이며, 이는 홀짝 자기켤레이고 $\mathcal N$에
  속합니다.
- conj:hookswap은 $[\,]$ 때문에 비어 있지 않은 분할에 대해 진술합니다(`hookswapConjecture`).
  `IsMV1`은 논문의 재귀에 따른 "미제르 그런디 값 $1$"입니다. 곧 $[\,]$이거나, 값이 $0$인
  옵션(미제르 $\mathcal P$-위치)이 있고 값이 $1$인 옵션이 없는 위치입니다(`isMV1_iff`).
  `EEHook`은 $r,c\ge2$가 짝수인 `hook r c`입니다. 프로그램은 mex 재귀로 콘웨이 쌍을 계산해 이
  정의들과 대조합니다.

## 관련 연구와 감사

- **논문**은 `thm:thick-hook`(두꺼운 훅의 스프라그–그런디 값)과, 멜드 추측의 동기가 된 멜드 결과
  `thm:rectairs`, `thm:ltrl`을 증명합니다. 논문의 관찰은 conj:bloby로부터 $[1]$로 끝나는 홀수
  훅들의 스택이 이기는 위치임을 이끌어 냅니다. 논문의 `thm:cgpairshooks`는 모든 훅의 콘웨이
  쌍을 계산하며, 이로부터 conj:hookswap의 $(\Leftarrow)$ 방향이 나옵니다.
- **Zijian Zeng**, *A Boundary-Word Classification of Losing Positions in CRIM* (2026-08-29 날짜,
  심사 전; GitHub `ArtificialZeng/AI-Has-Taste`, 폴더
  `reproducible_source_code/BigWIN2/BW2-B02-P10`)은 여기의 두 증명이 기대는 $\mathcal P$-위치의
  분류를 제시하고 증명합니다. 미제르 증명도 Zeng 증명의 수 분석을 다시 씁니다. 이 프리프린트는
  논문의 conj:main을 해결하며, 멜드 추측, conj:pself, 미제르 규칙은 언급하지 않습니다. 분류의 Lean
  형식화는
  [crim-hook-stacks](../crim-hook-stacks/README.ko.md)에 있습니다.
- **경로.** 이 프로젝트의 이전 탐색 실행이 두 논증과 미제르 가설을 찾았고, 오른쪽 결합 멜드에
  대한 멜드 논증의 첫 Lean 초안을 썼습니다. 또 비어 있지 않은 분할에 대한 conj:hookswap을 크기
  50까지 확인했습니다. 모듈의 멜드 부분은 그 초안의 정의(`meld`, `thickHook`, `ThickParams`,
  `thickPairs`)와 보조정리 `meld_ofPairs`를 다시 쓰고, 모든 괄호 묶기를 다룹니다. "스택"의
  해석과 그 괄호 묶기가 결과에 영향을 주지 않는다는 증명을 포함한 conj:pself 부분, 미제르
  분류의 증명, conj:hookswap 부분은 여기서 만들었습니다.
- **S. S. Mehat**, Zenodo [10.5281/zenodo.22070744](https://doi.org/10.5281/zenodo.22070744)
  (2026-08-23)는 부분이 여섯 개 이하이거나 가장 큰 부분이 6 이하인 $\mathcal P$-위치를
  분류합니다. 여기서는 쓰지 않습니다.
- **the-omega-institute/trureturing**에는 같은 논문의 다른 두 추측에 대한 Lean
  반박(`CrimRectairSquareBoundaryRefutation`, `CrimGrundyRefutation`)이 있습니다. 이 두 추측에
  관해서는 멜드 추측의 유한 범위 반례 탐색을 등록한 열린 이슈(#8292, 2026-09-16)만 있는데, 그
  실행은 어떤 경우도 평가하기 전에 멈췄고, 이슈는 추측을 열린 문제로 기록합니다.

새로움은 주장하지 않습니다. 이 작업은 사람이 검토하지 않았으며, 어디에도 제출하지 않았습니다.

## 확인한 출처

2026-10-25 16:20–16:25 UTC에 확인했습니다.

- arXiv에는 2606.16828의 v1만 있고, OpenAlex에는 이 논문을 인용한 문헌이 없습니다.
- MathDB 게시물 375374(멜드 추측)와 375373(conj:hookswap)은 해답 없이 열려 있고, MathDB에는
  conj:pself 게시물이 없습니다.
- OpenConjecture는 멜드 추측(3664), conj:pself(3666), conj:hookswap(3663)을 열린 추측으로 올려
  두었습니다.
- Formal Conjectures에는 CRIM에 관한 파일, 이슈, PR이 없습니다.
- GitHub 코드 검색("2606.16828", "Impartial Merge", "parity self-conjugate")에서는 Zeng의 저장소,
  trureturing의 파일, CRIM을 연습 문제로 내는 강의 자료, 목록 항목이 나오며, 어느 것도 두 추측을
  해결하지 않습니다. Zeng의 저장소에는 2026-09-16 이후 커밋이 없습니다. Zenodo에는 Mehat의
  아티팩트가 있고 그보다 새로운 것은 없습니다.
- 이 출처들 중 어느 것도 여기서 증명한 미제르 분류를 진술하지 않으며, conj:hookswap을 해결한
  것도 없습니다.
