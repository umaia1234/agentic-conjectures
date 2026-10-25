**English** | [한국어](DETAILS.ko.md)

# Additive sink–wall duality: details of the proof

This file supports [README.md](README.md). It gives the complete proof of the
duality formula, with the Lean name of each step, the choices behind the
formal statement, the computations, slips in the paper's final remarks, and
the prior art.

## 1. Setting

Fix integers $1\le a<b$ and put $c=a+b$ and $S=\{a,b,c\}$. In the paper's
notation $a=s_1$, $b=s_2$, $c=s_3$, $m=a$ and $\delta=b-a$.

- **Wall game** (`wall a b x`): $w(x)=\operatorname{mex}\{w(x-s): s\in S,\ s\le x\}$ for $x\ge0$.
- **Sink game** (`sink a b y`): $v(y)=0$ for $y\le0$, and
  $v(y)=\operatorname{mex}\{v(y-s): s\in S\}$ for $y\ge1$.
- $P=\{x\ge0: w(x)=0\}$ is the set of wall $\mathcal P$-positions.
- $p$ (`period a b`) is the period length of Theorem 3 of the paper: with
  $d=\delta\bmod 2m$, $p=3m+2\delta-d$ if $d\le m$, and
  $p=m(m+2\delta+d)/\gcd(m,d)$ otherwise.
- $\sigma$ swaps $0$ and $2$ and fixes $1$ and $3$, and $[x]_p\in[0,p)$ is the
  least nonnegative residue of $x$ modulo $p$.

**Theorem** (`statement_holds`). For all $1\le a<b$ and all $x\in\mathbb Z$,
$w([x]_p)=\sigma(v([-b-x]_p))$.

The proof has two parts. Part A (sections 2 and 3, file `Classes.lean`) uses
only the mex recursions. It reduces the theorem to one fact about $P$, the
**gap**:

$$P\cap[p-c,\ p-1]=\varnothing.\qquad\text{(Gap)}$$

Part B (sections 4 and 5, file `Explicit.lean`) proves (Gap) from an explicit
description of $P$. No step depends on $\gcd(a,b)$, and $a=1$ is included, so
the proof needs no reduction to coprime moves.

## 2. Part A: what the mex recursion gives

Five basic facts (`Classes.lean`, section `soft`):

- (P0) `wall_zero_iff`: $x\in P$ if and only if no option $x-s$ ($s\in S$,
  $s\le x$) lies in $P$.
- (I) `indep`: no two elements of $P$ differ by an element of $S$, since then
  the larger one would have an option in $P$.
- (D) `dom`: if $x\notin P$, some option of $x$ lies in $P$.
- (L) `wall_small`: $[0,a)\subseteq P$, since these positions have no options.
- (FD) `fwd`: if $x\notin P$, then $x+s\in P$ for some $s\in S$. Indeed, if
  $x+c\notin P$, (D) at $x+c$ gives an option of $x+c$ in $P$; it is not $x$,
  so it is $x+b$ or $x+a$.

### Lemma A1 (T1, the wall classes: `wall_eq_wallClass`)

For $x\ge0$, $w(x)$ is $0$ if $x\in P$; otherwise $1$ if $x\ge a$ and
$x-a\in P$; otherwise $2$ if $x+b\in P$; otherwise $3$.

*Proof.* Strong induction on $x$. Write $\mathrm{cls}(x)$ for the right-hand
side, so that $w(x-s)=\mathrm{cls}(x-s)$ for every option. Two remarks:

- (R3, `class3_shift`) If $\mathrm{cls}(x)=3$, then $x\ge a$ and
  $x+b-a\in P$. Indeed $x\notin P$ gives $x\ge a$ by (L). Since
  $x+b\notin P$, (D) at $x+b$ gives $s\in S$ with $x+b-s\in P$; $s=b$ would
  give $x\in P$ and $s=c$ would give $x-a\in P$, so $s=a$.
- (R1) If $x\notin P$ and not ($x\ge a$ and $x-a\in P$), some option has value
  $1$. Indeed $x\ge a$ by (L), and (D) at $x-a$ gives $s\le x-a$ with
  $x-a-s\in P$. The option $x-s$ then has $x-s\ge a$, $x-s-a\in P$, and
  $x-s\notin P$ by (I), so $\mathrm{cls}(x-s)=1$.

Now check the mex in each class.

- Class 0: by definition of $P$.
- Class 1 ($x-a\in P$): the option $x-a$ has value $0$. An option of value $1$
  would give $x-s-a\in P$, which differs from $x-a\in P$ by $s$, against (I).
- Class 2: value $0$ occurs by (D) and value $1$ by (R1). An option of value
  $2$ would give $x-s+b\in P$, which differs from $x+b\in P$ by $s$.
- Class 3: values $0$ and $1$ occur as in class 2. For value $2$: by (R3),
  $x\ge a$ and $x-a+b\in P$; also $x-a\notin P$, and $x-2a\notin P$ when
  $x\ge2a$, because it differs from $x+b-a$ by $c$; so $\mathrm{cls}(x-a)=2$.
  An option $x-s$ of value $3$ would give, by (R3), $x-s+b-a\in P$, which
  differs from $x+b-a\in P$ by $s$. $\square$

The three conditions are mutually exclusive by (I). Modulo $p$ this is the
form of Manabe's Corollary 46: $\mathcal W_1=\mathcal W_0+s_1$ and
$\mathcal W_2=\mathcal W_0-s_2$.

### Lemma A2 (T2, the sink classes: `sink_eq_sinkClass`)

For $t\ge0$, $v(t+1)$ is $0$ if $t\ge c$ and $t-c\in P$; otherwise $1$ if
$t\in P$; otherwise $2$ if $t\ge a$ and $t-a\in P$; otherwise $3$.

The three conditions are mutually exclusive by (I): $t$ and $t-c$ differ by
$c$, $t$ and $t-a$ by $a$, and $t-a$ and $t-c$ by $b$.

*Proof.* Strong induction on $t$. The options of $t+1$ are the $t+1-s$ with
$s\in S$. If $s\le t$, this is $(t-s)+1$, covered by the induction
hypothesis. If $s>t$, it lies in the sink and has value $0$
(`sink_option`). Two remarks:

- (Z0) Some option has value $0$ whenever $t<c$, or $t\ge c$ and
  $t-c\notin P$. If $t<c$, the move $c$ goes into the sink. Otherwise (D) at
  $t-c$ gives $s\le t-c$ with $t-c-s\in P$, and the option $(t-s)+1$ is of
  class 0.
- (S3, `sink_class3_shift`) If $t$ is of class 3, then $t\ge b$ and
  $t-b\in P$: (D) at $t$ gives some $t-s\in P$, and the class conditions
  exclude $s=a$ and $s=c$.

Now check the mex in each class.

- Class 0 ($t-c\in P$): every option is $(t-s)+1$ with $t-s\ge0$. If it had
  value $0$, then $t-s-c\in P$, against (I) with $t-c\in P$. So the value is
  $0$.
- Class 1 ($t\in P$): some option has value $0$ by (Z0), because $t-c\notin P$
  by (I) when $t\ge c$. An option of value $1$ would be $(t-s)+1$ with
  $t-s\in P$, against (I); options in the sink have value $0$.
- Class 2 ($t-a\in P$): the option $(t-a)+1$ is of class 1, because its class-0
  condition $t-a-c\in P$ contradicts (I). Some option has value $0$ by (Z0),
  because $t-c\notin P$ (it differs from $t-a$ by $b$). An option of value
  $2$ would give $t-s-a\in P$, against (I).
- Class 3: by (S3), $t-b\in P$, so the option $(t-b)+1$ is of class 1. Also
  $t\ge a$ by (L) and $t-a\notin P$, so (D) at $t-a$ gives $s\le t-a$ with
  $t-a-s\in P$, and $(t-s)+1$ is of class 2. Some option has value $0$ by
  (Z0). An option $(t-s)+1$ of value $3$ would give, by (S3), $t-s-b\in P$,
  against (I) with $t-b\in P$. $\square$

Class 0 is the outcome relation of I. Althöfer and J. Bültermann
(*Superlinear period lengths in some subtraction games*, Theoret. Comput.
Sci. 148 (1995)), which the paper recalls as its equation (1),
$o_{\rm wall}(x)=o_{\rm sink}(x+s_3+1)$.

### Lemma A3 (periodicity: `wall_zero_add_period`)

If (Gap) holds and $p>c$, then $x+p\in P\iff x\in P$ for all $x\ge0$.

*Proof.* Strong induction on $x$, using (P0) at $x+p$. For $s\le x$, the option
$(x-s)+p$ lies in $P$ if and only if $x-s$ does, by induction. For $s>x$, the
option $x+p-s$ lies in $[p-c,p)$, outside $P$ by (Gap). So $x+p\in P$ if and
only if no $x-s$ with $s\le x$ lies in $P$, that is, if and only if
$x\in P$. $\square$

With (T1) and (T2), this makes both nim-sequences $p$-periodic
(`wall_add_period` from $0$, `sink_add_period` from $1$).

### Lemma A4 (T3, reflection: `wall_zero_reflect`)

If (Gap) holds and $M:=p-c-1\ge0$, then $x\in P\iff M-x\in P$ for
$0\le x\le M$.

*Proof.* Let $R=\{x\in[0,M]: M-x\in P\}$, and put $u=M-x$. We claim that $R$
satisfies the recursion (P0) on $[0,M]$: $x\in R$ if and only if no $s\le x$
has $x-s\in R$, that is, if and only if no $s\in S$ with $u+s\le M$ has
$u+s\in P$. If $u\in P$, this holds by (I). If $u\notin P$, (FD) gives
$u+s\in P$ for some $s\in S$, and $u+s\le M+c=p-1$ with (Gap) forces
$u+s\le M$. So $R$ and $P\cap[0,M]$ satisfy the same recursion, and they
coincide by strong induction. $\square$

## 3. Assembly modulo p (`Classes.lean`, section `residues`)

Assume (Gap) and $p>c$, so $M\ge0$. Let $Z=\{X\in\mathbb Z:[X]_p\in P\}$
(`Zp`). By Lemma A3, $n\in Z\iff n\in P$ for $n\ge0$.

- (Z-I, `Zp_indep`) If $X\in Z$ and $s\in S$, then $X+s\notin Z$. Let
  $n=[X]_p$. If $n+s<p$, use (I); otherwise $n\ge p-s\ge p-c$, and $n\notin P$
  by (Gap).
- (Z-R, `Zp_reflect`) $X\in Z\iff -X-c-1\in Z$. Let $n=[X]_p$. If $n\le M$,
  then $[-X-c-1]_p=M-n$ and Lemma A4 applies. If $n>M$, then $n$ and
  $[-X-c-1]_p=M-n+p$ both lie in $[p-c,p)$, outside $P$.
- (Z-W, `wall_mod_eq`) $w([x]_p)$ is $0$, $1$, $2$ or $3$ according as
  $x\in Z$; else $x-a\in Z$; else $x+b\in Z$; else none. This is Lemma A1 at
  $X=[x]_p$. When $X<a$, the residue $[x-a]_p=X-a+p$ lies in $[p-a,p)$ and is
  not in $P$, which matches the condition $X\ge a$ of Lemma A1.
- (Z-S, `sink_mod_eq`) $v([y]_p)$ is $0$, $1$, $2$ or $3$ according as
  $y-c-1\in Z$; else $y-1\in Z$; else $y-a-1\in Z$; else none. For
  $Y=[y]_p\ge1$ this is Lemma A2 at $t=Y-1$; (Gap) again absorbs the side
  conditions $t\ge c$ and $t\ge a$. For $Y=0$, $v(0)=0$, and
  $[y-c-1]_p=M\in P$ by Lemma A4 at $x=0\in P$.

By (Z-I), the conditions in (Z-W) are mutually exclusive, and so are those in
(Z-S).

**Proof of the theorem from (Gap)** (`conj_of_gap`). Put $y=-b-x$. By (Z-R),

- $y-c-1=-(x+b)-c-1\in Z\iff x+b\in Z$,
- $y-1=-(x-a)-c-1\in Z\iff x-a\in Z$,
- $y-a-1=-x-c-1\in Z\iff x\in Z$.

So $v([y]_p)$ is $0$, $1$, $2$ or $3$ exactly when $w([x]_p)$ is $2$, $1$, $0$
or $3$, that is, $w([x]_p)=\sigma(v([y]_p))$. $\square$

The same assembly gives `sink_period_eq_zero`: $v(p)=0$, so the choice of
representative of the residue $0$ on the sink side does not matter.

## 4. Part B: the wall P-positions explicitly (`Explicit.lean`)

For $y\in\mathbb Z$ write $y=2aY+\rho$ with $0\le\rho<2a$, and define

- $E=\{y:\rho<a\}$, the residues $0,\dots,a-1$ modulo $2a$;
- $\kappa(y)=aY+\min(a,\rho)$; for $y\ge0$ this is $\#(E\cap[0,y))$;
- $b=2aq+r$ with $0\le r<2a$, and $N=\kappa(b)=aq+\min(a,r)$;
- $\varphi(y)=\lfloor\kappa(y)/N\rfloor$ and $\Phi(y)=y+b\,\varphi(y)$;
- $W=\Phi(E)=\{x:\ x-jb\in E\text{ and }\varphi(x-jb)=j\text{ for some }j\}$ (`W`).

For $n\ge0$ the $n$-th element of $E$ is $e_n=n+a\lfloor n/a\rfloor$, and
$\kappa(e_n)=n$, so $W\cap\mathbb N$ consists of the numbers
$n+a\lfloor n/a\rfloor+b\lfloor n/N\rfloor$. This is the classical bracket
formula (Winning Ways; Flammenkamp), in the form of Manabe's Theorem
`thm:additive`. We use neither of those results: we prove $P=W\cap\mathbb N$
for every pair $a<b$.

**Elementary facts** (namespace `Explicit`). Each follows by writing
$y=2aY+\rho$ and splitting on $\rho$; all are linear once $aY$ and $aq$ are
treated as unknowns.

- F0 (`b_decomp`, `N_ge`). $N\ge a$: if $q=0$, then $r=b>a$.
- F1 (`kappa_le_succ`, `kappa_mono`, `phi_mono`, `Phi_strictMono`).
  $\kappa(y)\le\kappa(y+1)$, so $\kappa$ and $\varphi$ are nondecreasing and
  $\Phi$ is strictly increasing.
- F2 (`E_sub_a`). $y\in E\iff y-a\notin E$.
- F3 (`kappa_sub_a`). $0\le\kappa(y)-\kappa(y-a)\le a$.
- F4 (`kappa_sub_b`). $0\le\kappa(y)-\kappa(y-b)\le N$ (split on $\rho\ge r$
  and on $r\le a$).
- F5 (`phi_step`). If $0\le u-v\le N$, then
  $\lfloor u/N\rfloor-\lfloor v/N\rfloor\in\{0,1\}$. With F0, F3 and F4:
  $\varphi(y)-\varphi(y-a)$ and $\varphi(y)-\varphi(y-b)$ lie in $\{0,1\}$
  (`phi_sub_a`, `phi_sub_b`).
- F6 (`phi_sub_b_lt`). If $y\in E$ and $y-b\in E$, then
  $\varphi(y-b)<\varphi(y)$. Write
  $y-b=2aZ+\tau$ with $\tau<a$. If $\tau+r<2a$, then $y=2a(Z+q)+\tau+r$ with
  $\tau+r<a$, so $r<a$, $N=aq+r$ and $\kappa(y)-\kappa(y-b)=N$. If
  $\tau+r\ge2a$, then $r>a$, $N=a(q+1)$ and $y=2a(Z+q+1)+(\tau+r-2a)$ with
  $\tau+r-2a<a$; equal $\varphi$-values $j$ would put the multiple
  $jN=a\,j(q+1)$ of $a$ in $(aZ+\tau+r-2a,\ aZ+\tau]\subset(aZ,aZ+a)$, which
  contains no multiple of $a$.
- F7 (`phi_sub_c_lt`). If $y\in E$ and $y-c\in E$, then
  $\varphi(y-c)<\varphi(y)$. Write $y-c=2aZ+\tau$ with $\tau<a$, so that
  $y=2a(Z+q)+(\tau+a+r)$. If $\tau+a+r<2a$, this says $y\notin E$, a
  contradiction. Otherwise $y=2a(Z+q+1)+(\tau+r-a)$ with
  $0\le\tau+r-a<2a$, so $y\in E$ gives $\tau+r-a<a$, and
  $\kappa(y)-\kappa(y-c)=aq+r\ge N$.
- F8 (`phi_shift`). If $y\notin E$ and $\varphi(y-a)<\varphi(y)<\varphi(y+b)$, then
  $y+b-a\in E$ and $\varphi(y+b-a)=\varphi(y)$. Write $y=2aU+\rho$ with
  $a\le\rho<2a$ and $j=\varphi(y)$; then $aU+\rho-a<jN\le aU+a$. If
  $\rho+r<2a$: $r<a$, $q\ge1$, $y+b-a=2a(U+q)+(\rho-a+r)\in E$ and
  $jN\le\kappa(y+b-a)<(j+1)N$. If $2a\le\rho+r<3a$: $\varphi(y+b)>j$ forces
  $r>a$ and $N=a(q+1)$, hence $jN=a(U+1)$ and $\rho+r\ge3a$, a
  contradiction. If $\rho+r\ge3a$: $r>a$, $N=a(q+1)$, $jN=a(U+1)$,
  $y+b-a=2a(U+q+1)+(\rho+r-3a)\in E$, and $jN\le\kappa(y+b-a)<(j+1)N$.

**B1 (independence, `W_indep`).** No two elements of $W$ differ by $a$, $b$
or $c$. Let $x=\Phi(e)$ and $x+s=\Phi(e')$ with $e,e'\in E$, $j=\varphi(e)$
and $j'=\varphi(e')$; then $e'=e+s+(j-j')b$. Since $\varphi$ is
nondecreasing, $e'>e$ forces $j'\ge j$ and $e'<e$ forces $j'\le j$.

- $s=a$: $j'=j$ gives $e'=e+a$, against F2; every other $j'$ violates
  monotonicity.
- $s=b$: $j'=j+1$ gives $e'=e$ and so $j'=j$; $j'=j$ gives $e'=e+b$, against
  F6; every other $j'$ violates monotonicity.
- $s=c$: $j'=j+1$ gives $e'=e+a$, against F2; $j'=j$ gives $e'=e+c$, against
  F7; every other $j'$ violates monotonicity.

**B2 (covering, `W_cover`).** For every $x\in\mathbb Z$, one of $x$, $x-a$,
$x-b$, $x-c$ lies in $W$. Let $\psi(j)=\varphi(x-jb)-j$. By F5,
$\psi(j)-\psi(j+1)\in\{1,2\}$. So the set $\{j:\psi(j)\ge0\}$ is nonempty and
bounded above, and its largest element $j$ has $\psi(j)\in\{0,1\}$. Put
$y=x-jb$.

- $\psi(j)=0$, that is, $\varphi(y)=j$. If $y\in E$, then $x\in W$.
  Otherwise $y-a\in E$ by F2, and $\varphi(y-a)\in\{j-1,j\}$ by F5. If it is
  $j$, then $x-a\in W$; if it is $j-1$, then $x-c=(y-a)+(j-1)b$ lies in $W$.
- $\psi(j)=1$: then $\varphi(y)=j+1$ and $\varphi(y-b)=j$. If $y-b\in E$,
  then $x-b\in W$. Otherwise $y-c\in E$ by F2, and
  $\varphi(y-c)\in\{j-1,j\}$. If it is $j$, then $x-c\in W$. If it is $j-1$,
  F8 at $y-b$ gives $y-a\in E$ and $\varphi(y-a)=j$, so $x-a\in W$.

**B3 (two gaps, `W_neg_gap` and `W_top_gap`).** $W$ misses $[-c,-1]$ and
$[p-c,p-1]$. For every integer $M$, $E$ misses $[2aM-a,\ 2aM-1]$ (these are
residues $a,\dots,2a-1$ modulo $2a$). Since $\Phi$ is strictly increasing and
$W=\Phi(E)$, no element of $W$ lies strictly between $\Phi(2aM-a-1)$ and
$\Phi(2aM)$ (`Explicit.not_W_of_gap`). Two choices of $M$ give the gaps.

- $M=0$: $\kappa(-a-1)=-1$ and $\kappa(0)=0$, so $\varphi(-a-1)=-1$,
  $\varphi(0)=0$, $\Phi(-a-1)=-c-1$ and $\Phi(0)=0$.
- $M=\ell$, where $p=2a\ell+kb$ with $a\ell=kN$ and $\ell,k\ge1$ (section 5):
  $\kappa(2a\ell)=a\ell=kN$ and $\kappa(2a\ell-a-1)=a\ell-1$, so
  $\varphi(2a\ell)=k$, $\varphi(2a\ell-a-1)=k-1$, $\Phi(2a\ell)=p$ and
  $\Phi(2a\ell-a-1)=p-c-1$.

**B4 ($P=W\cap\mathbb N$, `wall_zero_iff_of_kernel` and `wall_zero_iff_W`).**
By strong induction with (P0): for $n\ge0$, $n\in W$ if and only if no
$s\le n$ has $n-s\in W$. The forward direction is B1. Conversely, if
$n\notin W$, B2 gives $n-s\in W$ for some $s\in S$, and B3 forces $n-s\ge0$.
The abstract form `wall_zero_iff_of_kernel` in `Classes.lean` takes B1, B2 and
the first gap of B3 as hypotheses about any set $W\subseteq\mathbb Z$.

## 5. The period formula

**Proposition** (`Explicit.period_spec`). Let $g=\gcd(a,N)$, $k=a/g$ and
$\ell=N/g$, so that $a\ell=kN=\operatorname{lcm}(a,N)$ and $\ell,k\ge1$. Then
$p=2a\ell+kb$.

*Proof.* Write $b=2aq+r$ with $0\le r<2a$.

- $r\ge a$: $N=a(q+1)$, $g=a$, $k=1$, $\ell=q+1$ and
  $2a\ell+kb=2a(q+1)+b$. Also $\delta=2aq+(r-a)$, so $d=r-a\le m$ and
  $p=3a+2\delta-d=2a+2b-r$, which is the same number.
- $r=0$: $q\ge1$, $N=aq$, $g=a$, $k=1$, $\ell=q$ and $2a\ell+kb=2aq+b=2b$.
  Also $d=a=m$, so $p=3a+2(b-a)-a=2b$.
- $0<r<a$: $q\ge1$, $N=aq+r$, $g=\gcd(a,r)$ and
  $2a\ell+kb=(a/g)(2N+b)=(a/g)(2b+r)$. Also $d=a+r>m$ and
  $\gcd(m,d)=\gcd(a,r)=g$, so $p=a(a+2\delta+d)/g=a(2b+r)/g$. $\square$

The Lean statement keeps what B3 uses: integers $\ell,k\ge1$ with
$a\ell=kN$ and $p=2a\ell+kb$. In particular $p\ge2a+b>c$ (`period_gt`). With
B3 and B4 this gives (Gap) for the paper's $p$ (`wall_ne_zero_of_gap`), and
section 3 gives the theorem (`statement_holds`). $\blacksquare$

The proposition also says $p=a(2N+b)/\gcd(a,N)$. When $a\ge2$ and
$\gcd(a,b)=1$, this is the least period in Manabe's Theorem `thm:additive`,
so the two period formulas agree.

## 6. Statement faithfulness

There is no Formal Conjectures statement of this conjecture, so the statement
is ours. The choices, also listed in the docstring of
[`AdditiveSinkWallDuality.lean`](../../AgenticConjectures/AdditiveSinkWallDuality.lean):

- **The games** are defined directly by their mex recursions in
  [`Games.lean`](../../AgenticConjectures/AdditiveSinkWallDuality/Games.lean),
  not through any formula. `wall s₁ s₂ x` takes $x\in\mathbb N$ and allows
  the moves $s\le x$. `sink s₁ s₂ y` takes $y\in\mathbb Z$, is $0$ for
  $y\le0$, and allows every move from $y\ge1$, also into the sink. The
  characterizations `wall_eq_iff` and `sink_eq_iff` restate the recursions.
- **Moves of size 0** are skipped in both definitions so that the recursions
  terminate for every pair. For $1\le s_1<s_2$ there are no such moves, so
  the filter changes nothing.
- **The period.** `period s₁ s₂` is the formula of Theorem 3. The conjecture
  speaks of the "(outcome) period length" $p$; Theorem 3 proves that the sink
  nim-sequence is purely periodic with this period length, and Corollary 4
  transfers it to the wall outcomes. We prove that the formula's $p$ is a
  period of both nim-sequences (`wall_periodic`, `sink_periodic`), not that
  it is the least one; [`check_duality.py`](check_duality.py) confirms that
  it is the least period for every $s_2\le200$. Since both sides are
  $p$-periodic and $v(p)=0$, the identity also holds with $p$ replaced by any
  multiple of $p$.
- **The variable** $x$ ranges over $\mathbb Z$. Both sides depend only on
  $x\bmod p$, so this reading contains the reading with $x\in\mathbb N$.
- **Residues.** $[x]_p$ is `x % p` (`Int.emod`, in $[0,p)$ since $p>0$),
  converted to $\mathbb N$ on the wall side. On the sink side the residue $0$
  is the sink position $0$, with value $0$; the paper's table in Example 5
  writes $22$ there instead, which has the same value (`sink_period_eq_zero`).
- **$\sigma$** is `sigma`: $0\mapsto2$, $2\mapsto0$, and the identity on other
  values. Values above $3$ never occur.
- **Scope.** Every $1\le s_1<s_2$: no condition on $\gcd(s_1,s_2)$ or on the
  regime $d\le m$, and $s_1=1$ is included.
- The TeX source also contains, inside `\iffalse`, an earlier draft of the
  conjecture with a different offset; we formalize the published equation (3).

## 7. Computations

The Lean proof is the certificate. Two Python scripts, which share no code,
recompute the facts from the definitions (standard library only):

- [`check_duality.py`](check_duality.py) computes both nim-sequences by the mex
  recursions and checks, for every $1\le s_1<s_2\le B$: equation (3) at every
  residue; that $p$ is a period of both sequences and $v(p)=0$; and that $p$
  is the least period of the sink nim-sequence and of the wall outcomes.
- [`check_translates.py`](check_translates.py) checks, over three periods,
  (T1), (T2) with the mutual exclusivity of the conditions, (Gap), (T3), the
  bracket formula for $P$, and the identity
  $p=2\operatorname{lcm}(a,N)+(a/\gcd(a,N))\,b$ of section 5.

| Command | Sets | Time (Python 3.12) | CI |
| --- | ---: | ---: | :---: |
| `python3 check_duality.py 100` | 4,950 | about 3 s | yes |
| `python3 check_translates.py 100` | 4,950 | about 7 s | yes |
| `python3 check_duality.py 200` | 19,900 | about 40 s | no |

All runs report 0 failures. As a check of the checkers, replacing $p$ by
$2p$ or $p+1$, or $\sigma$ by the identity, makes `check_duality.py` flag all
406 sets with $s_2\le29$, and replacing $p$ by $p+a$ makes
`check_translates.py` flag all of them.

## 8. Slips in the paper's final remarks

We checked the final remarks (section "Final remarks" of v3) on
$\{2,3,5\}$ ($p=7$) and on Example 5, $\{2,5,7\}$ ($p=22$). Three statements
have a sign slip, and the second rows of the two tables are off by one;
none of them affects equation (3).

1. Item 4 of the summary list states $\sigma(v_{\rm sink}(x))=v_{\rm wall}(s_2-x)$.
   Inverting equation (3) gives $\sigma(v_{\rm sink}(y))=v_{\rm wall}([-s_2-y]_p)$
   instead. For $\{2,5,7\}$: $v_{\rm sink}(1)=1$, but $v_{\rm wall}(5-1)=v_{\rm wall}(4)=0$,
   while $v_{\rm wall}([-6]_{22})=v_{\rm wall}(16)=1$.
2. The worked example for $\{2,3,5\}$ derives the wall 2-positions from the
   sink zeros through $14+3-x$. This is the same slip: $x=7$ is a sink zero,
   but $v_{\rm wall}(10)=1$. With $14-3-x$, read modulo $p=7$, every sink zero
   gives a wall 2-position, and the list $4,5,11,12,\dots$ that the paper
   prints is correct.
3. The class $\mathcal W_2$ is printed as $\{[-w_n-s_1]_p+kp\}$. It should be
   $\{[w_n-s_2]_p+kp\}$, that is, $\mathcal W_0-s_2$, as in (T1) and Manabe's
   Corollary 46. For $\{2,5,7\}$ the printed formula gives the residues
   $\{6,7,10,16,19,20\}$, while the wall 2-positions are
   $\{5,8,9,17,18,21\}$. By (T3), the residues $[-w_n-s_1]_p$ ($n\ge0$) form
   the same set as the residues $[w_n+s_2+1]_p$, so the two formulas agree
   for $\{2,3,5\}$ only because $p=7$ divides $2s_2+1=7$. The printed formula
   is $s_2-s_n$: item 4 of the summary list applied to the rows $s_n$ of
   point 4 below.
4. The two tables before the worked example give, as a second data row, the
   sink-shifted $\mathcal P$-positions $s_n$. These rows list $w_n+s_3$, one
   less than the sink $\mathcal P$-positions $w_n+s_3+1$ of item 1 of the
   summary list and of $\mathcal S_0$. For $\{2,5,7\}$ the row reads
   $7,8,11,17,\dots$, but the sink zeros are $8,9,12,18,\dots$, as in
   Example 5. For $\{2,3,5\}$ the row reads $5,6,12,13,\dots$, but the sink
   zeros are $6,7,13,14,\dots$; positions $5$ and $12$ have value $3$, as the
   worked example itself states. Applied to this row, $14+3-x$ gives the
   correct list $4,5,11,12,\dots$ of point 2.

The other items and the formulas for $\mathcal W_0$, $\mathcal W_1$,
$\mathcal S_0$, $\mathcal S_1$ and $\mathcal S_2$ agree with our computations,
and with (T2) and (T3) in general.

## 9. Prior art and credits

- **The conjecture** is equation (3) of A. Bhagat, U. Larsson, H. Manabe and
  T. Yamashita, *Additive Sink Subtraction*,
  [arXiv:2601.18715v3](https://arxiv.org/abs/2601.18715v3) (2026-03-16), the
  latest version.
- **The wall side is known.** H. Manabe, *Purely Periodic Three-move
  Subtraction Games*,
  [arXiv:2609.05358v2](https://arxiv.org/abs/2609.05358v2) (2026-09-16),
  Theorem `thm:additive`, gives the $n$-th wall $\mathcal P$-position and the
  least period when $a\ge2$ and $\gcd(a,b)=1$, and Corollary 46 gives the
  wall value classes; the paper reduces other pairs by dilation. Its arXiv
  ancillary files contain a Lean 4 formalization of these wall-side results
  (Lean 4.31.0, without Mathlib). We used it only as a reference for which
  facts are needed; none of its code was copied, adapted or translated (it is
  licensed CC BY-NC-SA 4.0). Our (T1) and Part B prove the facts we need again,
  for every pair.
- U. Larsson and H. Manabe, *Additive subtraction games*,
  [arXiv:2603.10414v2](https://arxiv.org/abs/2603.10414v2), determine the wall
  nim-values in the primitive quadratic regime.
- **The bracket formula** for the wall $\mathcal P$-positions is classical
  (Berlekamp, Conway and Guy, *Winning Ways*; A. Flammenkamp's thesis), as
  the paper's final remarks recall.
- **An earlier scouting run of this project** found the route through (T1),
  (T2) and (T3) and checked them, and equation (3), numerically.
- **Searches on 2026-10-25** found no proof or disproof of equation (3): no
  new arXiv version of the three papers and no later paper by Manabe or
  Larsson on sink games; no work citing them in OpenAlex; no MathDB entry; no
  Formal Conjectures issue or pull request; and no GitHub repository or code,
  Zenodo record or the-omega-institute/trureturing file about it.

We make no novelty claim. No human has reviewed this proof, and nothing has
been reported to the authors or submitted anywhere.
