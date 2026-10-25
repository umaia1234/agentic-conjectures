[English](DETAILS.md) | **한국어**

# 덧셈형 싱크–벽 쌍대성: 증명의 세부 사항

이 파일은 [README.ko.md](README.ko.md)를 보충합니다. 쌍대성 공식의 완전한
증명을 각 단계의 Lean 이름과 함께 싣고, 형식 명제를 정할 때의 선택, 계산,
논문 맺음말의 실수, 선행 연구를 정리합니다.

## 1. 설정

정수 $1\le a<b$를 고정하고 $c=a+b$, $S=\{a,b,c\}$로 둡니다. 논문의 기호로는
$a=s_1$, $b=s_2$, $c=s_3$, $m=a$, $\delta=b-a$입니다.

- **벽 게임** (`wall a b x`): $x\ge0$에 대해 $w(x)=\operatorname{mex}\{w(x-s): s\in S,\ s\le x\}$.
- **싱크 게임** (`sink a b y`): $y\le0$이면 $v(y)=0$이고, $y\ge1$이면
  $v(y)=\operatorname{mex}\{v(y-s): s\in S\}$.
- $P=\{x\ge0: w(x)=0\}$는 벽 $\mathcal P$-위치의 집합입니다.
- $p$ (`period a b`)는 논문 정리 3의 주기 길이입니다. $d=\delta\bmod 2m$으로
  두면, $d\le m$일 때 $p=3m+2\delta-d$이고, 그렇지 않으면
  $p=m(m+2\delta+d)/\gcd(m,d)$입니다.
- $\sigma$는 $0$과 $2$를 맞바꾸고 $1$과 $3$은 그대로 두며, $[x]_p\in[0,p)$는
  $x$를 $p$로 나눈 음이 아닌 최소 나머지입니다.

**정리** (`statement_holds`). 모든 $1\le a<b$와 모든 $x\in\mathbb Z$에 대해
$w([x]_p)=\sigma(v([-b-x]_p))$입니다.

증명은 두 부분으로 이루어집니다. 부분 A(2절과 3절, 파일 `Classes.lean`)는
mex 재귀만 씁니다. 이 부분은 정리를 $P$에 관한 사실 하나, 곧 **간격**으로
환원합니다.

$$P\cap[p-c,\ p-1]=\varnothing.\qquad\text{(간격)}$$

부분 B(4절과 5절, 파일 `Explicit.lean`)는 $P$의 명시적 기술로부터 (간격)을
증명합니다. 어느 단계도 $\gcd(a,b)$에 의존하지 않고 $a=1$도 포함하므로,
서로소인 수로 환원할 필요가 없습니다.

## 2. 부분 A: mex 재귀가 주는 것

기본 사실 다섯 가지(`Classes.lean`, 섹션 `soft`). 위치 $x$의 옵션은 한
수로 갈 수 있는 위치 $x-s$($s\in S$, $s\le x$)입니다.

- (P0) `wall_zero_iff`: $x\in P$일 필요충분조건은 $x$의 어떤 옵션도 $P$에
  속하지 않는 것입니다.
- (I) `indep`: $P$의 어떤 두 원소도 $S$의 원소만큼 차이 나지 않습니다.
  그렇다면 큰 쪽이 $P$에 속하는 옵션을 갖게 되기 때문입니다.
- (D) `dom`: $x\notin P$이면 $x$의 어떤 옵션이 $P$에 속합니다.
- (L) `wall_small`: $[0,a)$의 위치는 옵션이 없으므로 $[0,a)\subseteq P$입니다.
- (FD) `fwd`: $x\notin P$이면 어떤 $s\in S$에 대해 $x+s\in P$입니다. 실제로
  $x+c\notin P$이면 $x+c$에서의 (D)가 $P$에 속하는 $x+c$의 옵션을 줍니다.
  그 옵션은 $x$가 아니므로 $x+b$ 또는 $x+a$입니다.

### 보조정리 A1 (T1, 벽 값의 분류: `wall_eq_wallClass`)

$x\ge0$에 대해, $x\in P$이면 $w(x)=0$입니다. 그렇지 않고 $x\ge a$이며
$x-a\in P$이면 $1$, 그렇지 않고 $x+b\in P$이면 $2$, 나머지 경우에는 $3$입니다.

*증명.* $x$에 대한 강한 귀납법을 씁니다. 우변을 $\mathrm{cls}(x)$로 쓰면,
모든 옵션에 대해 $w(x-s)=\mathrm{cls}(x-s)$입니다. 두 가지를 먼저 봅니다.

- (R3, `class3_shift`) $\mathrm{cls}(x)=3$이면 $x\ge a$이고 $x+b-a\in P$입니다.
  실제로 $x\notin P$이므로 (L)에 의해 $x\ge a$입니다. $x+b\notin P$이므로
  $x+b$에서의 (D)가 $x+b-s\in P$인 $s\in S$를 줍니다. $s=b$이면 $x\in P$가
  되고 $s=c$이면 $x-a\in P$가 되므로 $s=a$입니다.
- (R1) $x\notin P$이고 "$x\ge a$이며 $x-a\in P$"가 아니면, 값이 $1$인 옵션이
  있습니다. 실제로 (L)에 의해 $x\ge a$이고, $x-a$에서의 (D)가 $x-a-s\in P$인
  $s\le x-a$를 줍니다. 그러면 옵션 $x-s$는 $x-s\ge a$와 $x-s-a\in P$를
  만족하고, (I)에 의해 $x-s\notin P$이므로 $\mathrm{cls}(x-s)=1$입니다.

이제 각 분류에서 mex를 확인합니다.

- 분류 0: $P$의 정의 그대로입니다.
- 분류 1 ($x-a\in P$): 옵션 $x-a$의 값이 $0$입니다. 값이 $1$인 옵션이
  있다면 $x-s-a\in P$가 되는데, 이는 $x-a\in P$와 $s$만큼 차이 나므로 (I)에
  어긋납니다.
- 분류 2: 값 $0$은 (D)에 의해, 값 $1$은 (R1)에 의해 나타납니다. 값이 $2$인
  옵션이 있다면 $x-s+b\in P$가 되는데, 이는 $x+b\in P$와 $s$만큼 차이
  납니다.
- 분류 3: 값 $0$과 $1$은 분류 2에서처럼 나타납니다. 값 $2$의 경우: (R3)에
  의해 $x\ge a$이고 $x-a+b\in P$입니다. 또 $x-a\notin P$이고, $x\ge2a$이면
  $x-2a$는 $x+b-a$와 $c$만큼 차이 나므로 $x-2a\notin P$입니다. 따라서
  $\mathrm{cls}(x-a)=2$입니다. 값이 $3$인 옵션 $x-s$가 있다면 (R3)에 의해
  $x-s+b-a\in P$가 되는데, 이는 $x+b-a\in P$와 $s$만큼 차이 납니다. $\square$

세 조건은 (I)에 의해 서로 배타적입니다. $p$를 법으로 하면 이것은 Manabe의
따름정리 46의 꼴 $\mathcal W_1=\mathcal W_0+s_1$,
$\mathcal W_2=\mathcal W_0-s_2$입니다.

### 보조정리 A2 (T2, 싱크 값의 분류: `sink_eq_sinkClass`)

$t\ge0$에 대해, $t\ge c$이고 $t-c\in P$이면 $v(t+1)=0$입니다. 그렇지 않고
$t\in P$이면 $1$, 그렇지 않고 $t\ge a$이며 $t-a\in P$이면 $2$, 나머지
경우에는 $3$입니다.

세 조건은 (I)에 의해 서로 배타적입니다. $t$와 $t-c$는 $c$만큼, $t$와
$t-a$는 $a$만큼, $t-a$와 $t-c$는 $b$만큼 차이 나기 때문입니다.

*증명.* $t$에 대한 강한 귀납법을 씁니다. $t+1$의 옵션은 $s\in S$에 대한
$t+1-s$입니다. $s\le t$이면 이것은 $(t-s)+1$이고 귀납 가정이 적용됩니다.
$s>t$이면 이것은 싱크에 있고 값이 $0$입니다(`sink_option`). 두 가지를 먼저
봅니다.

- (Z0) $t<c$이거나, $t\ge c$이고 $t-c\notin P$이면, 값이 $0$인 옵션이
  있습니다. $t<c$이면 수 $c$가 싱크로 들어갑니다. 그렇지 않으면 $t-c$에서의
  (D)가 $t-c-s\in P$인 $s\le t-c$를 주고, 옵션 $(t-s)+1$은 분류 0입니다.
- (S3, `sink_class3_shift`) $t$가 분류 3이면 $t\ge b$이고 $t-b\in P$입니다.
  $t$에서의 (D)가 어떤 $t-s\in P$를 주는데, 분류 조건이 $s=a$와 $s=c$를
  배제합니다.

이제 각 분류에서 mex를 확인합니다.

- 분류 0 ($t-c\in P$): 모든 옵션은 $t-s\ge0$인 $(t-s)+1$입니다. 그 값이
  $0$이라면 $t-s-c\in P$가 되어, $t-c\in P$와 함께 (I)에 어긋납니다. 따라서
  값은 $0$입니다.
- 분류 1 ($t\in P$): $t\ge c$일 때 (I)에 의해 $t-c\notin P$이므로, (Z0)에
  의해 값이 $0$인 옵션이 있습니다. 값이 $1$인 옵션은 $t-s\in P$인
  $(t-s)+1$이어야 하므로 (I)에 어긋납니다. 싱크에 있는 옵션의 값은 $0$입니다.
- 분류 2 ($t-a\in P$): 옵션 $(t-a)+1$은 분류 1입니다. 그 분류 0 조건
  $t-a-c\in P$가 (I)에 어긋나기 때문입니다. $t-c\notin P$이므로($t-a$와
  $b$만큼 차이 남) (Z0)에 의해 값이 $0$인 옵션이 있습니다. 값이 $2$인 옵션이
  있다면 $t-s-a\in P$가 되어 (I)에 어긋납니다.
- 분류 3: (S3)에 의해 $t-b\in P$이므로 옵션 $(t-b)+1$은 분류 1입니다. 또
  (L)에 의해 $t\ge a$이고 $t-a\notin P$이므로, $t-a$에서의 (D)가
  $t-a-s\in P$인 $s\le t-a$를 주고, $(t-s)+1$은 분류 2입니다. (Z0)에 의해
  값이 $0$인 옵션이 있습니다. 값이 $3$인 옵션 $(t-s)+1$이 있다면 (S3)에 의해
  $t-s-b\in P$가 되어, $t-b\in P$와 함께 (I)에 어긋납니다. $\square$

분류 0은 I. Althöfer와 J. Bültermann의 결과(outcome) 관계
$o_{\rm wall}(x)=o_{\rm sink}(x+s_3+1)$입니다(*Superlinear period lengths in
some subtraction games*, Theoret. Comput. Sci. 148 (1995)). 논문은 이를
식 (1)로 상기합니다.

### 보조정리 A3 (주기성: `wall_zero_add_period`)

(간격)이 성립하고 $p>c$이면, 모든 $x\ge0$에 대해 $x+p\in P\iff x\in P$입니다.

*증명.* $x+p$에서의 (P0)을 써서 $x$에 대한 강한 귀납법으로 보입니다.
$s\le x$이면, 귀납 가정에 의해 옵션 $(x-s)+p$가 $P$에 속할 필요충분조건은
$x-s$가 $P$에 속하는 것입니다. $s>x$이면 옵션 $x+p-s$는 $[p-c,p)$에 있으므로
(간격)에 의해 $P$ 밖에 있습니다. 따라서 $x+p\in P$일 필요충분조건은
$s\le x$인 어떤 $x-s$도 $P$에 속하지 않는 것, 곧 $x\in P$입니다. $\square$

(T1), (T2)와 함께 이것은 두 님 수열을 $p$-주기적으로 만듭니다
(`wall_add_period`는 $0$부터, `sink_add_period`는 $1$부터).

### 보조정리 A4 (T3, 반사: `wall_zero_reflect`)

(간격)이 성립하고 $M:=p-c-1\ge0$이면, $0\le x\le M$에 대해
$x\in P\iff M-x\in P$입니다.

*증명.* $R=\{x\in[0,M]: M-x\in P\}$로 두고 $u=M-x$라 합시다. $R$이
$[0,M]$에서 재귀 (P0)을 만족함을 보이겠습니다. 즉 $x\in R$일
필요충분조건은 $x-s\in R$인 $s\le x$가 없는 것, 곧 $u+s\le M$인 $s\in S$
가운데 $u+s\in P$인 것이 없는 것입니다. $u\in P$이면 (I)에 의해 성립합니다.
$u\notin P$이면 (FD)가 어떤 $s\in S$에 대해 $u+s\in P$를 주는데,
$u+s\le M+c=p-1$과 (간격)으로부터 $u+s\le M$입니다. 따라서 $R$과
$P\cap[0,M]$은 같은 재귀를 만족하고, 강한 귀납법에 의해 일치합니다. $\square$

## 3. p를 법으로 한 조립 (`Classes.lean`, 섹션 `residues`)

(간격)과 $p>c$를 가정하므로 $M\ge0$입니다. $Z=\{X\in\mathbb Z:[X]_p\in P\}$
(`Zp`)로 둡니다. 보조정리 A3에 의해 $n\ge0$이면 $n\in Z\iff n\in P$입니다.

- (Z-I, `Zp_indep`) $X\in Z$이고 $s\in S$이면 $X+s\notin Z$입니다.
  $n=[X]_p$로 둡니다. $n+s<p$이면 (I)를 씁니다. 그렇지 않으면
  $n\ge p-s\ge p-c$이므로 (간격)에 의해 $n\notin P$입니다.
- (Z-R, `Zp_reflect`) $X\in Z\iff -X-c-1\in Z$입니다. $n=[X]_p$로 둡니다.
  $n\le M$이면 $[-X-c-1]_p=M-n$이고 보조정리 A4가 적용됩니다. $n>M$이면
  $n$과 $[-X-c-1]_p=M-n+p$가 모두 $[p-c,p)$에 있으므로 $P$ 밖에 있습니다.
- (Z-W, `wall_mod_eq`) $w([x]_p)$는 $x\in Z$이면 $0$, 그렇지 않고
  $x-a\in Z$이면 $1$, 그렇지 않고 $x+b\in Z$이면 $2$, 나머지 경우에는
  $3$입니다. 이것은 $X=[x]_p$에서의 보조정리 A1입니다. $X<a$이면 나머지
  $[x-a]_p=X-a+p$는 $[p-a,p)$에 있어 $P$에 속하지 않으므로, 보조정리 A1의
  조건 $X\ge a$와 맞습니다.
- (Z-S, `sink_mod_eq`) $v([y]_p)$는 $y-c-1\in Z$이면 $0$, 그렇지 않고
  $y-1\in Z$이면 $1$, 그렇지 않고 $y-a-1\in Z$이면 $2$, 나머지 경우에는
  $3$입니다. $Y=[y]_p\ge1$이면 이것은 $t=Y-1$에서의 보조정리 A2이고,
  (간격)이 다시 곁조건 $t\ge c$와 $t\ge a$를 흡수합니다. $Y=0$이면
  $v(0)=0$이고, $x=0\in P$에서의 보조정리 A4에 의해 $[y-c-1]_p=M\in P$입니다.

(Z-I)에 의해 (Z-W)의 조건들은 서로 배타적이고, (Z-S)의 조건들도 그렇습니다.

**(간격)으로부터 정리의 증명** (`conj_of_gap`). $y=-b-x$로 둡니다. (Z-R)에
의해

- $y-c-1=-(x+b)-c-1\in Z\iff x+b\in Z$,
- $y-1=-(x-a)-c-1\in Z\iff x-a\in Z$,
- $y-a-1=-x-c-1\in Z\iff x\in Z$

입니다. 따라서 $v([y]_p)$가 $0$, $1$, $2$, $3$인 것은 각각 $w([x]_p)$가
$2$, $1$, $0$, $3$인 것과 같고, 곧 $w([x]_p)=\sigma(v([y]_p))$입니다. $\square$

같은 조립으로 `sink_period_eq_zero`, 곧 $v(p)=0$도 얻습니다. 따라서 싱크
쪽에서 나머지 $0$의 대표를 어느 것으로 골라도 상관없습니다.

## 4. 부분 B: 벽 P-위치의 명시적 기술 (`Explicit.lean`)

$y\in\mathbb Z$를 $0\le\rho<2a$인 $y=2aY+\rho$로 쓰고 다음과 같이 정의합니다.

- $E=\{y:\rho<a\}$, 곧 $2a$를 법으로 한 나머지 $0,\dots,a-1$;
- $\kappa(y)=aY+\min(a,\rho)$. $y\ge0$이면 이것은 $\#(E\cap[0,y))$입니다;
- $0\le r<2a$인 $b=2aq+r$에 대해 $N=\kappa(b)=aq+\min(a,r)$;
- $\varphi(y)=\lfloor\kappa(y)/N\rfloor$, $\Phi(y)=y+b\,\varphi(y)$;
- $W=\Phi(E)$, 곧 어떤 $j$에 대해 $x-jb\in E$이고 $\varphi(x-jb)=j$인
  $x$들의 집합 (`W`).

$n\ge0$에 대해 $E$의 $n$번째 원소는 $e_n=n+a\lfloor n/a\rfloor$이고
$\kappa(e_n)=n$이므로, $W\cap\mathbb N$은 수
$n+a\lfloor n/a\rfloor+b\lfloor n/N\rfloor$들로 이루어집니다. 이것이 고전적인
괄호 공식(Winning Ways; Flammenkamp)이며, Manabe의 정리 `thm:additive`의
꼴입니다. 우리는 그 어느 결과도 쓰지 않고, 모든 쌍 $a<b$에 대해
$P=W\cap\mathbb N$을 증명합니다.

**기본 사실** (이름공간 `Explicit`). 각 사실은 $y=2aY+\rho$로 쓰고 $\rho$에
따라 경우를 나누면 나옵니다. $aY$와 $aq$를 미지수로 보면 모두 선형입니다.

- F0 (`b_decomp`, `N_ge`). $N\ge a$: $q=0$이면 $r=b>a$이기 때문입니다.
- F1 (`kappa_le_succ`, `kappa_mono`, `phi_mono`, `Phi_strictMono`).
  $\kappa(y)\le\kappa(y+1)$이므로 $\kappa$와 $\varphi$는 감소하지 않고,
  $\Phi$는 순증가합니다.
- F2 (`E_sub_a`). $y\in E\iff y-a\notin E$.
- F3 (`kappa_sub_a`). $0\le\kappa(y)-\kappa(y-a)\le a$.
- F4 (`kappa_sub_b`). $0\le\kappa(y)-\kappa(y-b)\le N$ ($\rho\ge r$인지와
  $r\le a$인지로 경우를 나눕니다).
- F5 (`phi_step`). $0\le u-v\le N$이면
  $\lfloor u/N\rfloor-\lfloor v/N\rfloor\in\{0,1\}$입니다. F0, F3, F4와
  합치면 $\varphi(y)-\varphi(y-a)$와 $\varphi(y)-\varphi(y-b)$는
  $\{0,1\}$에 속합니다(`phi_sub_a`, `phi_sub_b`).
- F6 (`phi_sub_b_lt`). $y\in E$이고 $y-b\in E$이면
  $\varphi(y-b)<\varphi(y)$입니다. $\tau<a$인 $y-b=2aZ+\tau$로 씁니다.
  $\tau+r<2a$이면 $y=2a(Z+q)+\tau+r$이고 $\tau+r<a$이므로 $r<a$,
  $N=aq+r$, $\kappa(y)-\kappa(y-b)=N$입니다. $\tau+r\ge2a$이면 $r>a$,
  $N=a(q+1)$이고, $\tau+r-2a<a$인 $y=2a(Z+q+1)+(\tau+r-2a)$입니다. 이때
  두 $\varphi$ 값이 같은 $j$라면, $a$의 배수 $jN=a\,j(q+1)$이 구간
  $(aZ+\tau+r-2a,\ aZ+\tau]\subset(aZ,aZ+a)$에 놓이게 되는데, 이 구간에는
  $a$의 배수가 없습니다.
- F7 (`phi_sub_c_lt`). $y\in E$이고 $y-c\in E$이면
  $\varphi(y-c)<\varphi(y)$입니다. $\tau<a$인 $y-c=2aZ+\tau$로 쓰면
  $y=2a(Z+q)+(\tau+a+r)$입니다. $\tau+a+r<2a$이면 이것은 $y\notin E$를
  뜻하므로 모순입니다. 그렇지 않으면 $0\le\tau+r-a<2a$인
  $y=2a(Z+q+1)+(\tau+r-a)$이므로, $y\in E$에서 $\tau+r-a<a$이고
  $\kappa(y)-\kappa(y-c)=aq+r\ge N$입니다.
- F8 (`phi_shift`). $y\notin E$이고 $\varphi(y-a)<\varphi(y)<\varphi(y+b)$이면
  $y+b-a\in E$이고 $\varphi(y+b-a)=\varphi(y)$입니다. $a\le\rho<2a$인
  $y=2aU+\rho$로 쓰고 $j=\varphi(y)$로 두면 $aU+\rho-a<jN\le aU+a$입니다.
  $\rho+r<2a$이면 $r<a$, $q\ge1$이고 $y+b-a=2a(U+q)+(\rho-a+r)\in E$이며
  $jN\le\kappa(y+b-a)<(j+1)N$입니다. $2a\le\rho+r<3a$이면
  $\varphi(y+b)>j$에서 $r>a$와 $N=a(q+1)$이 나오고, 따라서 $jN=a(U+1)$이며
  $\rho+r\ge3a$가 되어 모순입니다. $\rho+r\ge3a$이면 $r>a$, $N=a(q+1)$,
  $jN=a(U+1)$이고, $y+b-a=2a(U+q+1)+(\rho+r-3a)\in E$이며
  $jN\le\kappa(y+b-a)<(j+1)N$입니다.

**B1 (독립성, `W_indep`).** $W$의 어떤 두 원소도 $a$, $b$, $c$만큼 차이 나지
않습니다. $e,e'\in E$, $j=\varphi(e)$, $j'=\varphi(e')$에 대해 $x=\Phi(e)$,
$x+s=\Phi(e')$라 하면 $e'=e+s+(j-j')b$입니다. $\varphi$는 감소하지 않으므로
$e'>e$이면 $j'\ge j$이고, $e'<e$이면 $j'\le j$입니다.

- $s=a$: $j'=j$이면 $e'=e+a$가 되어 F2에 어긋나고, 다른 모든 $j'$은
  단조성에 어긋납니다.
- $s=b$: $j'=j+1$이면 $e'=e$이므로 $j'=j$가 되고, $j'=j$이면 $e'=e+b$가
  되어 F6에 어긋나며, 다른 모든 $j'$은 단조성에 어긋납니다.
- $s=c$: $j'=j+1$이면 $e'=e+a$가 되어 F2에 어긋나고, $j'=j$이면
  $e'=e+c$가 되어 F7에 어긋나며, 다른 모든 $j'$은 단조성에 어긋납니다.

**B2 (덮기, `W_cover`).** 모든 $x\in\mathbb Z$에 대해 $x$, $x-a$, $x-b$,
$x-c$ 가운데 하나는 $W$에 속합니다. $\psi(j)=\varphi(x-jb)-j$로 둡니다.
F5에 의해 $\psi(j)-\psi(j+1)\in\{1,2\}$입니다. 따라서 집합
$\{j:\psi(j)\ge0\}$은 공집합이 아니고 위로 유계이며, 그 최대 원소 $j$는
$\psi(j)\in\{0,1\}$을 만족합니다. $y=x-jb$로 둡니다.

- $\psi(j)=0$, 곧 $\varphi(y)=j$인 경우: $y\in E$이면 $x\in W$입니다.
  그렇지 않으면 F2에 의해 $y-a\in E$이고, F5에 의해
  $\varphi(y-a)\in\{j-1,j\}$입니다. 그것이 $j$이면 $x-a\in W$이고, $j-1$이면
  $x-c=(y-a)+(j-1)b$가 $W$에 속합니다.
- $\psi(j)=1$인 경우: $\varphi(y)=j+1$이고 $\varphi(y-b)=j$입니다.
  $y-b\in E$이면 $x-b\in W$입니다. 그렇지 않으면 F2에 의해 $y-c\in E$이고
  $\varphi(y-c)\in\{j-1,j\}$입니다. 그것이 $j$이면 $x-c\in W$입니다.
  $j-1$이면, $y-b$에서의 F8이 $y-a\in E$와 $\varphi(y-a)=j$를 주므로
  $x-a\in W$입니다.

**B3 (두 간격, `W_neg_gap`과 `W_top_gap`).** $W$는 $[-c,-1]$, $[p-c,p-1]$과
만나지 않습니다. 모든 정수 $M$에 대해 $E$는 $[2aM-a,\ 2aM-1]$과 만나지
않습니다($2a$를 법으로 한 나머지 $a,\dots,2a-1$이기 때문입니다). $\Phi$는
순증가하고 $W=\Phi(E)$이므로, $W$의 어떤 원소도 $\Phi(2aM-a-1)$과
$\Phi(2aM)$ 사이에 (양 끝을 빼고) 놓이지 않습니다(`Explicit.not_W_of_gap`).
$M$을 두 가지로 고르면 두 간격이 나옵니다.

- $M=0$: $\kappa(-a-1)=-1$, $\kappa(0)=0$이므로 $\varphi(-a-1)=-1$,
  $\varphi(0)=0$, $\Phi(-a-1)=-c-1$, $\Phi(0)=0$입니다.
- $M=\ell$, 여기서 $\ell$과 $k$는 $p=2a\ell+kb$, $a\ell=kN$, $\ell,k\ge1$을
  만족하는 수입니다(5절). $\kappa(2a\ell)=a\ell=kN$,
  $\kappa(2a\ell-a-1)=a\ell-1$이므로 $\varphi(2a\ell)=k$,
  $\varphi(2a\ell-a-1)=k-1$, $\Phi(2a\ell)=p$, $\Phi(2a\ell-a-1)=p-c-1$입니다.

**B4 ($P=W\cap\mathbb N$, `wall_zero_iff_of_kernel`과 `wall_zero_iff_W`).**
(P0)을 써서 강한 귀납법으로 보입니다. $n\ge0$에 대해 $n\in W$일
필요충분조건은 $n-s\in W$인 $s\le n$이 없는 것입니다. 정방향은 B1입니다.
역으로 $n\notin W$이면 B2가 어떤 $s\in S$에 대해 $n-s\in W$를 주고, B3가
$n-s\ge0$을 강제합니다. `Classes.lean`의 추상적인 형태
`wall_zero_iff_of_kernel`은 임의의 집합 $W\subseteq\mathbb Z$에 대한 가정으로
B1, B2, B3의 첫 간격을 받습니다.

## 5. 주기 공식

**명제** (`Explicit.period_spec`). $g=\gcd(a,N)$, $k=a/g$, $\ell=N/g$로
두면 $a\ell=kN=\operatorname{lcm}(a,N)$이고 $\ell,k\ge1$입니다. 이때
$p=2a\ell+kb$입니다.

*증명.* $0\le r<2a$인 $b=2aq+r$로 씁니다.

- $r\ge a$: $N=a(q+1)$, $g=a$, $k=1$, $\ell=q+1$이고
  $2a\ell+kb=2a(q+1)+b$입니다. 또 $\delta=2aq+(r-a)$이므로 $d=r-a\le m$이고
  $p=3a+2\delta-d=2a+2b-r$인데, 이는 같은 수입니다.
- $r=0$: $q\ge1$, $N=aq$, $g=a$, $k=1$, $\ell=q$이고
  $2a\ell+kb=2aq+b=2b$입니다. 또 $d=a=m$이므로 $p=3a+2(b-a)-a=2b$입니다.
- $0<r<a$: $q\ge1$, $N=aq+r$, $g=\gcd(a,r)$이고
  $2a\ell+kb=(a/g)(2N+b)=(a/g)(2b+r)$입니다. 또 $d=a+r>m$이고
  $\gcd(m,d)=\gcd(a,r)=g$이므로 $p=a(a+2\delta+d)/g=a(2b+r)/g$입니다. $\square$

Lean 명제는 B3에 쓰이는 것만 남깁니다. 곧 $a\ell=kN$이고 $p=2a\ell+kb$인
정수 $\ell,k\ge1$입니다. 특히 $p\ge2a+b>c$입니다(`period_gt`). B3, B4와
합치면 논문의 $p$에 대한 (간격)이 나오고(`wall_ne_zero_of_gap`), 3절이
정리를 줍니다(`statement_holds`). $\blacksquare$

이 명제는 $p=a(2N+b)/\gcd(a,N)$이라는 것도 말해 줍니다. $a\ge2$이고
$\gcd(a,b)=1$이면 이것은 Manabe의 정리 `thm:additive`의 최소 주기이므로, 두
주기 공식은 일치합니다.

## 6. 명제의 충실성

Formal Conjectures에는 이 추측의 명제가 없으므로 명제는 우리가 만든
것입니다. 선택한 내용은
[`AdditiveSinkWallDuality.lean`](../../AgenticConjectures/AdditiveSinkWallDuality.lean)의
docstring에도 적혀 있습니다.

- **게임**은
  [`Games.lean`](../../AgenticConjectures/AdditiveSinkWallDuality/Games.lean)에서
  어떤 공식도 거치지 않고 mex 재귀로 직접 정의합니다. `wall s₁ s₂ x`는
  $x\in\mathbb N$을 받고 $s\le x$인 수만 허용합니다. `sink s₁ s₂ y`는
  $y\in\mathbb Z$를 받고, $y\le0$이면 $0$이며, $y\ge1$에서는 싱크로 들어가는
  수를 포함해 모든 수를 허용합니다. `wall_eq_iff`와 `sink_eq_iff`는 이
  재귀를 다시 쓴 것입니다.
- **크기 0인 수**는 모든 쌍에 대해 재귀가 끝나도록 두 정의 모두에서
  건너뜁니다. $1\le s_1<s_2$이면 그런 수가 없으므로 이 거르기는 아무것도
  바꾸지 않습니다.
- **주기.** `period s₁ s₂`는 정리 3의 공식입니다. 추측은 "(outcome) period
  length" $p$를 말하는데, 정리 3은 싱크 님 수열이 이 주기 길이로 순수
  주기적임을 증명하고, 따름정리 4는 이를 벽 게임의 결과로 옮깁니다. 우리는
  공식의 $p$가 두 님 수열의 주기임을 증명하지만(`wall_periodic`,
  `sink_periodic`), 최소 주기임은 증명하지 않습니다.
  [`check_duality.py`](check_duality.py)는 $s_2\le200$인 모든 경우에 이것이
  최소 주기임을 확인합니다. 양변이 $p$-주기적이고 $v(p)=0$이므로, $p$를
  $p$의 임의의 배수로 바꾸어도 항등식은 성립합니다.
- **변수** $x$는 $\mathbb Z$ 전체를 움직입니다. 양변은 $x\bmod p$에만
  의존하므로, 이 읽기는 $x\in\mathbb N$인 읽기를 포함합니다.
- **나머지.** $[x]_p$는 `x % p`(`Int.emod`, $p>0$이므로 $[0,p)$에 속함)이고,
  벽 쪽에서는 $\mathbb N$으로 바꿉니다. 싱크 쪽에서 나머지 $0$은 값이 $0$인
  싱크 위치 $0$입니다. 논문의 예 5의 표는 그 자리에 $22$를 쓰는데, 그 값도
  같습니다(`sink_period_eq_zero`).
- **$\sigma$**는 `sigma`입니다. $0\mapsto2$, $2\mapsto0$이고 다른 값에서는
  항등입니다. $3$보다 큰 값은 나타나지 않습니다.
- **범위.** 모든 $1\le s_1<s_2$를 다룹니다. $\gcd(s_1,s_2)$나 영역
  $d\le m$에 대한 조건이 없고, $s_1=1$도 포함합니다.
- TeX 원본에는 `\iffalse` 안에 오프셋이 다른 이 추측의 이전 초안도 있습니다.
  우리는 출판된 식 (3)을 형식화합니다.

## 7. 계산

인증서는 Lean 증명입니다. 코드를 공유하지 않는 두 Python 스크립트가
정의로부터 사실들을 다시 계산합니다(표준 라이브러리만 사용).

- [`check_duality.py`](check_duality.py)는 mex 재귀로 두 님 수열을 계산하고,
  모든 $1\le s_1<s_2\le B$에 대해 다음을 검사합니다. 모든 나머지에서의
  식 (3), $p$가 두 수열의 주기이며 $v(p)=0$이라는 것, $p$가 싱크 님 수열과
  벽 결과의 최소 주기라는 것.
- [`check_translates.py`](check_translates.py)는 세 주기에 걸쳐 (T1), 조건의
  배타성을 포함한 (T2), (간격), (T3), $P$의 괄호 공식, 5절의 항등식
  $p=2\operatorname{lcm}(a,N)+(a/\gcd(a,N))\,b$를 검사합니다.

| 명령 | 집합 수 | 시간 (Python 3.12) | CI |
| --- | ---: | ---: | :---: |
| `python3 check_duality.py 100` | 4,950 | 약 3초 | 예 |
| `python3 check_translates.py 100` | 4,950 | 약 7초 | 예 |
| `python3 check_duality.py 200` | 19,900 | 약 40초 | 아니요 |

모든 실행이 실패 0건을 보고합니다. 검사기 자체를 확인하려고 $p$를 $2p$나
$p+1$로, 또는 $\sigma$를 항등함수로 바꾸면 `check_duality.py`가
$s_2\le29$인 406개 집합 모두에서 실패를 보고하고, $p$를 $p+a$로 바꾸면
`check_translates.py`가 그 모두에서 실패를 보고합니다.

## 8. 논문 맺음말의 실수

맺음말(v3의 "Final remarks" 절)을 $\{2,3,5\}$ ($p=7$)와 예 5인
$\{2,5,7\}$ ($p=22$)에서 확인했습니다. 세 곳에 부호 실수가 있고, 두 표의
둘째 행은 값이 1씩 작습니다. 어느 것도 식 (3)에는 영향을 주지 않습니다.

1. 요약 목록의 4번 항목은 $\sigma(v_{\rm sink}(x))=v_{\rm wall}(s_2-x)$라고
   씁니다. 식 (3)을 뒤집으면 대신
   $\sigma(v_{\rm sink}(y))=v_{\rm wall}([-s_2-y]_p)$가 나옵니다.
   $\{2,5,7\}$에서 $v_{\rm sink}(1)=1$이지만
   $v_{\rm wall}(5-1)=v_{\rm wall}(4)=0$이고,
   $v_{\rm wall}([-6]_{22})=v_{\rm wall}(16)=1$입니다.
2. $\{2,3,5\}$의 풀이 예는 싱크의 0들로부터 $14+3-x$를 통해 벽의
   2-위치를 이끌어 냅니다. 이것도 같은 실수입니다. $x=7$은 싱크의 0이지만
   $v_{\rm wall}(10)=1$입니다. $p=7$을 법으로 읽은 $14-3-x$를 쓰면 모든
   싱크의 0이 벽의 2-위치를 주고, 논문이 적은 목록 $4,5,11,12,\dots$는
   맞습니다.
3. 분류 $\mathcal W_2$는 $\{[-w_n-s_1]_p+kp\}$로 적혀 있습니다. 이는 (T1)과
   Manabe의 따름정리 46에서처럼 $\{[w_n-s_2]_p+kp\}$, 곧
   $\mathcal W_0-s_2$여야 합니다. $\{2,5,7\}$에서 적힌 공식은 나머지
   $\{6,7,10,16,19,20\}$을 주지만, 벽의 2-위치는 $\{5,8,9,17,18,21\}$입니다.
   (T3)에 의해 나머지 $[-w_n-s_1]_p$ ($n\ge0$)의 집합은 나머지
   $[w_n+s_2+1]_p$의 집합과 같으므로, 두 공식이 $\{2,3,5\}$에서 일치하는
   것은 $p=7$이 $2s_2+1=7$을 나누기 때문일 뿐입니다. 적힌 공식은
   $s_2-s_n$, 곧 요약 목록의 4번 항목을 아래 4의 행 $s_n$에 적용한
   것입니다.
4. 풀이 예 앞의 두 표는 둘째 데이터 행으로 싱크 쪽으로 옮긴
   $\mathcal P$-위치 $s_n$을 줍니다. 이 행들에 적힌 값은 $w_n+s_3$으로, 요약
   목록의 1번 항목과 $\mathcal S_0$가 주는 싱크 $\mathcal P$-위치
   $w_n+s_3+1$보다 1 작습니다. $\{2,5,7\}$에서 이 행은
   $7,8,11,17,\dots$이지만 싱크의 0은 예 5에서처럼 $8,9,12,18,\dots$입니다.
   $\{2,3,5\}$에서 이 행은 $5,6,12,13,\dots$이지만 싱크의 0은
   $6,7,13,14,\dots$이고, 위치 $5$와 $12$의 값은 풀이 예 자신이 말하듯
   $3$입니다. 이 행에 $14+3-x$를 적용하면 2의 올바른 목록
   $4,5,11,12,\dots$가 나옵니다.

나머지 항목들과 $\mathcal W_0$, $\mathcal W_1$, $\mathcal S_0$,
$\mathcal S_1$, $\mathcal S_2$의 공식은 우리의 계산과 일치하고, 일반적으로
(T2), (T3)와도 일치합니다.

## 9. 선행 연구와 기여

- **추측**은 A. Bhagat, U. Larsson, H. Manabe, T. Yamashita,
  *Additive Sink Subtraction*,
  [arXiv:2601.18715v3](https://arxiv.org/abs/2601.18715v3) (2026-03-16, 최신
  판)의 식 (3)입니다.
- **벽 쪽은 이미 알려져 있습니다.** H. Manabe, *Purely Periodic Three-move
  Subtraction Games*,
  [arXiv:2609.05358v2](https://arxiv.org/abs/2609.05358v2) (2026-09-16)의
  정리 `thm:additive`는 $a\ge2$이고 $\gcd(a,b)=1$일 때 $n$번째 벽
  $\mathcal P$-위치와 최소 주기를 주고, 따름정리 46은 벽 값의 분류를 줍니다.
  다른 쌍은 확대(dilation)로 환원합니다. 이 논문의 arXiv 부속 파일에는 이
  벽 쪽 결과들의 Lean 4 형식화가 들어 있습니다(Lean 4.31.0, Mathlib 없음).
  우리는 어떤 사실이 필요한지 알기 위한 참고로만 이것을 썼고, 그 코드는
  전혀 복사하거나 고쳐 쓰거나 옮기지 않았습니다(라이선스는 CC BY-NC-SA
  4.0입니다). 우리의 (T1)과 부분 B는 필요한 사실을 모든 쌍에 대해 다시
  증명합니다.
- U. Larsson, H. Manabe, *Additive subtraction games*,
  [arXiv:2603.10414v2](https://arxiv.org/abs/2603.10414v2)는 원시 이차
  영역에서 벽 님 값을 결정합니다.
- 벽 $\mathcal P$-위치의 **괄호 공식**은 고전적인 결과입니다(Berlekamp,
  Conway, Guy, *Winning Ways*; A. Flammenkamp의 학위 논문). 논문의 맺음말도
  이를 상기합니다.
- **이 프로젝트의 앞선 정찰 실행**이 (T1), (T2), (T3)를 거치는 경로를 찾고,
  그것들과 식 (3)을 수치로 확인했습니다.
- **2026-10-25의 검색**에서는 식 (3)의 증명이나 반증을 찾지 못했습니다. 세
  논문의 새 arXiv 판도, 싱크 게임에 관한 Manabe나 Larsson의 이후 논문도
  없었습니다. OpenAlex에서 이들을 인용한 문헌, MathDB 항목, Formal
  Conjectures 이슈나 풀 리퀘스트도 없었고, 이에 관한 GitHub 저장소나 코드,
  Zenodo 레코드, the-omega-institute/trureturing 파일도 없었습니다.

새로운 결과라고 주장하지 않습니다. 이 증명을 검토한 사람은 아직 없으며,
저자들에게 알리거나 어디에 제출한 것도 없습니다.
