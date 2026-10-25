[English](README.md) | **한국어**

# CRIM: 지는 분할을 지는 훅 아래에 쌓기

Ina Bašić, Eric Gottlieb, Matjaž Krnc의 *CRIM: A Natural Game on Integer Partitions*
([arXiv:2606.16828v1](https://arxiv.org/abs/2606.16828), 2026-06-15)는 열–행 비편향
병합(Column–Row Impartial Merge, CRIM)을 연구합니다. 위치는 정수 분할 $\lambda$이고, 한 수는 영
도형에서 행 하나나 열 하나를 지우고 남은 조각을 다시 붙입니다. 정상 규칙을 따르므로 빈 분할
$[\,]$은 $\mathcal P$-위치입니다. 논문의 쌓기 추측(TeX 라벨 `conj:bloby`)은 다음과 같습니다.

> Let $\lambda$ and $\Gamma_{r,c}$ be losing and suppose $\lambda^*=\Gamma_{r,c}\lhd\lambda$ is
> defined. Then $\lambda^*\in\mathcal P$.

여기서 $\Gamma_{r,c}=[c,1^{r-1}]$는 훅이고 $\lhd$는 더피 길이로 정의되는 논문의
스택입니다([상세](DETAILS.ko.md#1-게임-스택-두-추측)). 논문의 주 추측(`conj:main`)은 다음과
같습니다.

> Every $\mathcal P$-position is of even rank.

여기서 $\lambda=[\lambda_1,\dots,\lambda_r]$의 랭크는 $|r-\lambda_1|$입니다. 두 추측 모두 열린
문제로 올라 있습니다([확인한 출처](#확인한-출처) 참고).

이 디렉터리는 두 추측을 모두 Lean으로 증명합니다. conj:main은 경계 단어에 의한 모든
$\mathcal P$-위치의 분류에서 나오는데, 이 분류는 Zijian Zeng이 심사 전 프리프린트에서 제시하고
증명했습니다. 우리는 Zeng의 증명을 형식화했습니다. conj:bloby는 후수 전략으로 conj:main에서
나오며, 이 전략은 우리가 증명했습니다. 이 작업은 아직 사람이 검토하지 않았습니다.

## 검증된 결과

Lean 모듈 [`CrimHookStacks.lean`](../../AgenticConjectures/CrimHookStacks.lean)은 다음을 커널로
검증하며, `sorry`, 추가 공리, `native_decide`를 쓰지 않습니다.

| 정리 | 내용 |
|---|---|
| `statement_holds` | conj:bloby (`statement`). |
| `mainConjecture_holds` | conj:main (`mainConjecture`). |
| `isP_ofPairs_iff` | Zeng의 분류: 런 쌍이 $p=((a_1,b_1),\dots,(a_k,b_k))$인 분할이 $\mathcal P$-위치일 필요충분조건은 $\ell(\lambda)+\lambda_1$과 끝 벗기기 통계량 $M$이 모두 짝수인 것입니다. |
| `statement_of_mainConjecture` | conj:main은 conj:bloby를 함의합니다(`mainConjecture → statement`). |
| `isP_stack_of_localEvenRank` | 국소형. $\lambda\in\mathcal P$이고, $\lambda$에서 "수 하나, 이어서 $\mathcal P$-위치로 가는 수 하나"를 반복해 도달하는 모든 분할($\lambda$ 자신 포함)의 랭크가 짝수라 합시다. 그러면 스택이 정의되는 모든 지는 훅에 대해 $\Gamma_{r,c}\lhd\lambda\in\mathcal P$입니다. |
| `stack_hook` | 논문의 일반 스택을 훅에 적용한 것: $\Gamma_{r,c}\lhd\mu$가 정의될 필요충분조건은 $\ell(\mu)\le r-1$이고 $\mu_1\le c-1$인 것이며, 이때 스택은 $[c,1+\mu_1,\dots,1+\mu_k,1^{r-1-k}]$입니다. |
| `isP_hook_iff`, `isP_pair_iff`, `isP_twoCol_iff` | 논문의 `lem:hook`과 `thm:2parts`, 그리고 두 열의 경우: $\Gamma_{r,c}\in\mathcal P$ ⇔ $r,c\ge2$이고 $r\equiv c\pmod 2$; $[a,b]\in\mathcal P$ ⇔ $a$가 짝수; $[2^a,1^b]\in\mathcal P$ ⇔ $a+b$가 짝수. |

환원은 $\Gamma_{r,c}\lhd\lambda$ 위의 후수 전략입니다. 이 전략은 두 모서리 모양에서만
$\operatorname{rank}\lambda$의 홀짝을 쓰며, 귀납은 $\lambda$에서 도달 가능한 위치 안에서만
이루어집니다. 분류는 분할을 경계 단어의 런 길이로 부호화하고, CRIM을 이 런 쌍 위의 게임과
동일시한 뒤, 주장된 $\mathcal P$-위치들이 게임의 재귀를 만족함을 보입니다.
[DETAILS.ko.md](DETAILS.ko.md)에 두 증명을 Lean 이름과 함께 적었습니다. 모듈은 환원의 크기
제한형(`statement_of_mainConjecture_le`)과, 부분이 두 개 이하이거나 가장 큰 부분이 2 이하인 경우의
직접 증명(`statement_of_length_le_two`, `statement_of_part_one_le_two`)도 담고 있으며, 이들은
분류를 쓰지 않습니다.

## 계산 증거

모든 프로그램은 [`programs/`](programs/)에 있습니다. Lean 증명은 이 프로그램들을 쓰지 않습니다.

| 프로그램 | 확인하는 것 | 로그 | 결과 |
|---|---|---|---|
| [`crim_check.py`](programs/crim_check.py) | $\lvert\lambda\rvert\le N$인 모든 분할의 $\mathcal P/\mathcal N$; conj:main; 논문의 일반 스택 정의로 계산한, $\mathcal P$-위치 쌍 전체에 대한 conj:bloby | [`crim_check_py_n60.log`](logs/crim_check_py_n60.log) | $N=60$: 분할 6,639,349개, $\mathcal P$ 1,870,422개, 정의된 스택 964,855개, 실패 0; 61초 |
| [`crim_check.c`](programs/crim_check.c) | 같은 내용을 독립적으로 구현(순위 매긴 비트 표) | [`crim_check_c_n110.log`](logs/crim_check_c_n110.log) | $N=110$: 분할 5,465,153,652개, $\mathcal P$ 1,534,701,211개, 정의된 스택 783,733,098개, 실패 0; 333초 |
| [`strategy_check.py`](programs/strategy_check.py) | 증명의 모든 경우를 재현: 각 수, 정해진 응수, 그 모양과 $\mathcal P$ 여부 | [`strategy_check_n60.log`](logs/strategy_check_n60.log) | $N=60$: 스택 964,014개, 응수 150,828,030개, 실패 0; 291초 |
| [`boundary_word_check.py`](programs/boundary_word_check.py) | Zeng의 경계 단어 분류(아래 참고)를 정확한 표와 비교 | [`boundary_word_check_n60.log`](logs/boundary_word_check_n60.log) | $N=60$: 불일치 0; 43초 |

두 풀이 프로그램은 $n\le60$인 모든 $n$에서 분할의 수와 $\mathcal P$-위치의 수가 일치합니다.

## 재현

아래 명령은 이 디렉터리에서 실행합니다. 처음 네 개는 [`status.yaml`](status.yaml)의 CI 항목이며,
실행 시간은 2026-10-25에 여러 작업이 함께 돌던 Apple silicon 머신에서 잰 것입니다.

```bash
python3 programs/crim_check.py --max-n 45
```

```bash
mkdir -p /tmp/crim_hook_stacks_build && cc -O2 -std=c99 -o /tmp/crim_hook_stacks_build/crim_check programs/crim_check.c && /tmp/crim_hook_stacks_build/crim_check 70
```

```bash
python3 programs/strategy_check.py --max-n 40
```

```bash
python3 programs/boundary_word_check.py --max-n 45
```

각각 약 4초, 2초, 5초, 3초 걸립니다. 로그로 남긴 실행은 Python 프로그램에 `--max-n 60`, C 프로그램에
`110`을 썼습니다. C 프로그램을 110으로 실행하면 약 5.5분이 걸리고 비트 표에 약 0.7 GB가 필요합니다.

## 명제의 충실성

Formal Conjectures에 해당 명제가 없으므로 두 형식 명제(conj:bloby에 해당하는 `statement`, conj:main에
해당하는 `mainConjecture`)는 우리가 작성한 것입니다. 각 정의를 TeX 원문과 대조했으며,
[DETAILS.ko.md §1.1](DETAILS.ko.md#11-해석)에 모든 해석을 정리했습니다.

- 분할은 양의 자연수로 이루어진 약감소 리스트(`IsPartition`)이고, $[\,]$도 허용합니다.
  `part l i`는 $\lambda_i$이며, 1부터 세고 마지막 부분을 넘으면 $0$입니다.
- 행 $i$를 지우는 것은 `List.eraseIdx`입니다. $1\le j\le\lambda_1$인 열 $j$를 지우면 $j$ 이상인
  부분이 모두 1씩 줄고 0이 된 부분은 사라집니다(`delCol`).
- `isP`는 $|\lambda|+\ell(\lambda)$에 대한 정초 재귀로 정의하며, $[\,]$은 지는 위치입니다. "지는
  위치"는 $\mathcal P$-위치(`IsP`)를 뜻합니다.
- `rank`는 논문 §2.1처럼 $|\ell(\lambda)-\lambda_1|$입니다. 부호를 남긴 차 $\lambda_1-\ell(\lambda)$도
  홀짝이 같습니다.
- `durfee`는 $d\le\lambda_d$인 가장 큰 $d\le\ell(\lambda)$입니다. 그보다 큰 $d$에서는
  $\lambda_d=0$이므로 조건을 만족하지 않습니다.
- `stack`은 논문의 일반 정의를 항 하나하나 그대로 따르며, 스택이 정의되지 않으면 `none`을
  돌려줍니다. $\mu=[\,]$이면 $\mu_1=0$입니다. 훅에 대한 공식은 정의가 아니라 정리 `stack_hook`입니다.
- `statement`는 모든 분할 $\lambda$와 모든 $r,c\ge1$에 대해 말합니다. 행($r=1$)과 열($c=1$)도 훅으로
  치지만, 이들은 결코 $\mathcal P$가 아니며 $\lambda=[\,]$일 때만 스택이 정의됩니다.
  $\Gamma_{r,c}\lhd[\,]=\Gamma_{r,c}$이므로 $\lambda=[\,]$은 허용되며 자명합니다.
- 런 쌍(`ofPairs`, `PMove`, `endM`)은 증명 안에서만 쓰는 도구입니다. `statement_holds`와
  `mainConjecture_holds`는 위의 정의로 서술됩니다.

## 관련 연구와 감사

- **논문**은 `lem:hook`, `thm:2parts`, `thm:3parts`를 증명하고, $|\lambda|\le50$과 여러 족에 대해
  conj:main을 확인하며, conj:bloby가 논문의 `prop:hooksquare`를 함의한다고 지적합니다. 서술된
  대로라면 `thm:3parts`는 $\mathcal N$인 열 $[1,1,1]$도 포함합니다
  ([DETAILS §9](DETAILS.ko.md#9-관련-연구와-정오표) 참고). 여기의 어떤 결과도 `thm:3parts`에
  의존하지 않습니다.
- **전략.** 이 프로젝트의 이전 탐색 실행이 후수 전략의 개요를 만들고 $n\le40$까지 시험했습니다.
  이 디렉터리는 그것을 완성하고 Lean으로 검증합니다.
- **S. S. Mehat**, Zenodo [10.5281/zenodo.22070744](https://doi.org/10.5281/zenodo.22070744)
  (2026-08-23; Lean 파일은 CC0, 스크립트는 MIT)은 부분이 여섯 개 이하인 $\mathcal P$-위치와,
  켤레를 통해 가장 큰 부분이 6 이하인 $\mathcal P$-위치를 분류하고 이들이 모두 짝수 랭크라고
  밝힙니다. 이는 그 범위에서의 conj:main입니다. 우리는 그 아티팩트를 다시 검증하지 않았고 그
  코드를 쓰지 않습니다.
- **the-omega-institute/trureturing**에는 같은 논문의 다른 두 추측에 대한 Lean
  반박(`CrimRectairSquareBoundaryRefutation`, `CrimGrundyRefutation`)이 있습니다. conj:main이나
  conj:bloby에 관한 것은 없습니다.
- **Zijian Zeng**, *A Boundary-Word Classification of Losing Positions in CRIM* (2026-08-29 날짜,
  심사 전; GitHub `ArtificialZeng/AI-Has-Taste`, 폴더
  `reproducible_source_code/BigWIN2/BW2-B02-P10`)은 `isP_ofPairs_iff`가 형식화하는
  $\mathcal P$-위치의 분류를 제시하고 증명하며, 그로부터 conj:main을 이끌어 냅니다. conj:bloby는
  언급하지 않습니다. [DETAILS §7](DETAILS.ko.md#7-경계-단어-분류로부터-conjmain)은 Zeng의
  보조정리를 따르며, Lean 증명은 우리가 작성했습니다. `boundary_word_check.py`는 크기 60 이하의
  모든 분할에 대해 이 분류를 정확한 표와 비교하기도 합니다.

새로움은 주장하지 않습니다. 이 작업은 사람이 검토하지 않았으며, 어디에도 제출하지 않았습니다.

## 확인한 출처

2026-10-25에 확인했습니다.

- arXiv에는 2606.16828의 v1만 있고, OpenAlex에는 이 논문을 인용한 문헌이 없습니다.
- MathDB 게시물 375370(conj:main)과 375375(conj:bloby)는 해답 없이 열려 있습니다.
- OpenConjecture에 두 추측이 모두 올라 있습니다.
- Formal Conjectures에는 CRIM에 관한 파일, 이슈, PR이 없습니다.
- GitHub 코드 검색("2606.16828", "Impartial Merge")에서는 trureturing의 파일, Zeng의 저장소, CRIM을
  연습 문제로 내는 강의 자료, conj:main을 미해결로 적은 목록이 나옵니다. Zenodo에는 Mehat의
  아티팩트가 있고 그보다 새로운 것은 없습니다.
