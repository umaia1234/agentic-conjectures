**English** | [한국어](DETAILS.ko.md)

# Vieta jumping with $r=2$: mathematical details

The problem and Conjecture 4.2 are due to Steven J. Miller, Dimitrios
Nikolakopoulos and Anitha Srinivasan
([arXiv:2605.19083v2](https://arxiv.org/abs/2605.19083v2)).

The results of sections 1–3 are checked by Lean in
[`VietaR2Gcd.lean`](../../AgenticConjectures/VietaR2Gcd.lean), except one remark
in §3.1 that is marked as not in Lean; each step names its Lean declaration.
Section 4 is computation only and is not machine-checked. The [Credit](#credit)
section says which steps are the paper's.

## 1. Setting and readings

For integers $r,k$ and positive integers $a,b$, the equation
$(a+r)/b+(b+r)/a=k$ is, after multiplying by $ab$,

\[
a^2+ra+b^2+rb=kab. \tag{$E_r$}
\]

In Lean, `Sol r a b k` says $a>0$, $b>0$ and $(E_r)$. The equation is symmetric
in $a$ and $b$ (`Sol.symm`).

Conjecture 4.2 of [arXiv:2605.19083v2](https://arxiv.org/abs/2605.19083v2)
concerns $r=2$. The formal statement is

```lean
def IsSolution (a b : ℕ) (k : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ ((a : ℚ) + 2) / b + ((b : ℚ) + 2) / a = k

def normSum (a b : ℕ) : ℚ := 2 * ((a : ℚ) + b) / (Nat.gcd a b : ℚ) ^ 2

def statement : Prop :=
  (∀ a b : ℕ, ∀ k : ℤ, IsSolution a b k → normSum a b ∈ ({1, 2, 3, 4, 5, 8} : Set ℚ)) ∧
    {q | ∃ a b, IsSolution a b 3 ∧ q = normSum a b} = {1, 5} ∧
    {q | ∃ a b, IsSolution a b 4 ∧ q = normSum a b} = {2, 3} ∧
    {q | ∃ a b, IsSolution a b 6 ∧ q = normSum a b} = {4, 8}
```

with these readings:

- $k$ is an integer, as in the paper's setup (§1). For rational $k$ the
  statement is false: $(a,b)=(1,2)$ gives $k=3/2+4=11/2$ and
  $2\cdot3/1=6$.
- $a,b$ are positive natural numbers; the fractions and $2(a+b)/\gcd(a,b)^2$
  are computed in $\mathbb Q$, with `Nat.gcd`.
- "If $k=3$, the values are $1$ and $5$" is an equality of sets: every
  solution with $k=3$ has value $1$ or $5$, and both occur. The same holds for
  $k=4$ and $k=6$.

`IsSolution.sol` turns `IsSolution a b k` into `Sol 2 a b k` by multiplying by
$ab\ne0$. `statement_holds` proves `statement` from `normSum_cases` (§2.3)
and the witnesses of §2.4.

## 2. Proof of Conjecture 4.2

### 2.1 Only $k=3,4,6$ occur (`diag`, `k_cases`)

This is the paper's Remark 4.1. Let $(a,b)$ solve $(E_2)$; by symmetry
$a\le b$.

- **Diagonal.** If $a=b$, then $(E_2)$ reads $2a^2+4a=ka^2$, so
  $(k-2)a=4$. Hence $k-2>0$ and $k-2$ divides $4$ with quotient $a$:
  $(a,k)\in\{(1,6),(2,4),(4,3)\}$.
- **Off the diagonal.** If $a<b$, view $(E_2)$ as the quadratic
  $t^2-(ka-2)t+(a^2+2a)=0$ in $t$, with root $t=b$. The other root
  $b'=ka-2-b$ satisfies $bb'=a^2+2a$. Since $b>0$, $b'>0$, and since
  $b\ge a+1$,
  \[
  b'=\frac{a^2+2a}{b}\le\frac{a^2+2a}{a+1}<a+1\le b .
  \]
  So $(a,b')$ solves $(E_2)$ with the same $k$ and a smaller sum $a+b'<a+b$.

Induction on $a+b$ ends on the diagonal, so $k\in\{3,4,6\}$.

### 2.2 The value as a quadratic form, and a divisibility (`key`)

This step holds for every $r$. Let $g=\gcd(a,b)$, $a=gx$, $b=gy$ with
$x,y\ge1$ coprime, and put

\[
m=kxy-x^2-y^2 .
\]

Substituting into $(E_r)$ and dividing by $g$ gives
$g(x^2+y^2-kxy)+r(x+y)=0$, that is,

\[
g\,m=r(x+y). \tag{1}
\]

So $m=r(x+y)/g=r(a+b)/g^2$ is the quantity of the conjecture (for $r=2$), and
$m>0$ when $r>0$. Expanding the definition of $m$ gives the identity

\[
(x+y)^2+m=(k+2)\,xy. \tag{2}
\]

Multiply (2) by $g$ and use (1): $(x+y)\bigl(g(x+y)+r\bigr)=(k+2)g\,xy$. A
prime dividing $x+y$ and $x$ (or $y$) would divide both $x$ and $y$, so $x+y$
is coprime to $xy$, and therefore $x+y$ divides $(k+2)g$. Write
$(k+2)g=(x+y)s$ with $s\in\mathbb Z$. Multiplying by $m$ and using (1),
$(x+y)\,r(k+2)=(x+y)\,s\,m$, and since $x+y>0$,

\[
r(k+2)=s\,m,\qquad\text{so } m\mid r(k+2). \tag{3}
\]

For $r=2$ this leaves $m\mid10$ when $k=3$, $m\mid12$ when $k=4$ and
$m\mid16$ when $k=6$, with $m>0$.

### 2.3 Congruence eliminations (`no_k_m`, `normSum_cases`)

For $k=3,4,6$, identity (2) reads $(x+y)^2+m=5xy$, $6xy$, $8xy$. The lemma
`no_k_m` says that this equation has no integer solution for the given $m$.
Lean checks the residue cases with `decide` in `ZMod n` for the modulus $n$
shown; the arguments below are the same checks done by hand. Recall that
squares are $0,1,4$ mod 5; $0,1$ mod 3; $0,1,4$ mod 8; and $0,1$ mod 4.

**$k=3$, $m\in\{1,2,5,10\}$.**

- $m=2$ (mod 5): $(x+y)^2\equiv-2\equiv3$, not a square mod 5.
- $m=10$ (mod 25): mod 5, $(x+y)^2\equiv0$, so $5\mid x+y$ and
  $25\mid(x+y)^2$. Then mod 25, $5xy\equiv10$, so $xy\equiv2\pmod 5$. As
  $y\equiv-x\pmod5$, this says $x^2\equiv-2\equiv3\pmod5$, impossible.
- $m=1$ and $m=5$ remain.

**$k=4$, $m\in\{1,2,3,4,6,12\}$.**

- $m=1$ and $m=4$ (mod 3): $(x+y)^2\equiv-1\equiv2$, not a square mod 3.
- $m=6$ (mod 9): mod 3, $3\mid x+y$, so $9\mid(x+y)^2$. Mod 9, $6xy\equiv6$,
  so $3\mid2(xy-1)$ and $xy\equiv1\pmod3$. As $y\equiv-x\pmod 3$, this says
  $x^2\equiv-1\equiv2\pmod3$, impossible.
- $m=12$ (parity, then mod 4; uses $\gcd(x,y)=1$): $(x+y)^2=6xy-12$ is even,
  so $x+y$ is even, and coprime $x,y$ are then both odd. So $4\mid(x+y)^2$,
  while $6xy-12\equiv6xy\equiv2\pmod4$ because $xy$ is odd.
- $m=2$ and $m=3$ remain.

**$k=6$, $m\in\{1,2,4,8,16\}$.**

- $m=1$ and $m=2$ (mod 8): $(x+y)^2\equiv7$ or $6$, not squares mod 8.
- $m=16$ (parity, then mod 16; uses $\gcd(x,y)=1$): $(x+y)^2=8xy-16$ is even,
  so $x,y$ are both odd. With $x+y=2s$, $4s^2=8xy-16$, so
  $s^2=2xy-4\equiv2\pmod4$ because $xy$ is odd; not a square mod 4.
- $m=4$ and $m=8$ remain.

Together with §2.1, `normSum_cases` gives: every solution has
$(k,m)\in\{(3,1),(3,5),(4,2),(4,3),(6,4),(6,8)\}$. This proves the membership
claim and the inclusions "$\subseteq$" of the three set equalities.

### 2.4 Attainment

| $k$ | $(a,b)$ | check of $(a+2)/b+(b+2)/a$ | $\gcd$ | $2(a+b)/\gcd^2$ |
|---|---|---|---|---|
| 3 | $(4,4)$ | $3/2+3/2=3$ | 4 | $16/16=1$ |
| 3 | $(4,6)$ | $1+2=3$ | 2 | $20/4=5$ |
| 4 | $(2,2)$ | $2+2=4$ | 2 | $8/4=2$ |
| 4 | $(2,4)$ | $1+3=4$ | 2 | $12/4=3$ |
| 6 | $(1,1)$ | $3+3=6$ | 1 | $4$ |
| 6 | $(1,3)$ | $1+5=6$ | 1 | $8$ |

Lean checks each row with `norm_num`. This proves the inclusions
"$\supseteq$", and with §2.3 the conjecture.

## 3. General $r$ (namespace `GeneralR`)

Here $r>0$, and "solution" means a solution of $(E_r)$ with $a,b>0$. The
paper analyses the diagonal solutions for general $r$ (its §4.1): there
$(k-2)a=2r$. The results below go beyond the paper; their proofs are standard
Vieta-jumping arguments.

**Vieta step (`Sol.next`).** If $(a,b)$ is a solution, so is
$(b,\,kb-r-a)$: viewing $(E_r)$ as a quadratic in $a$, the other root
$c=kb-r-a$ satisfies $ac=b(b+r)>0$, so $c>0$.

**G1 (`k_ge_three`).** $k\ge3$: $kab=a^2+b^2+r(a+b)>a^2+b^2\ge2ab$.

**Reduced solutions.** $(a,b)$ is *reduced* (`Reduced`) if $a\le b$ and
$b^2\le a^2+ra$.

**G2 (`descent`).** Every solution leads, by Vieta steps and swaps, to a
reduced solution with the same $k$. If $a\le b$ and $b^2>a^2+ra$, the other
root $b'=ka-r-b$ of $(E_r)$ in $b$ satisfies $bb'=a^2+ra>0$, so $b'>0$, and
$b'=(a^2+ra)/b<b$. So $(a,b')$ is a solution with a smaller sum; induct on
$a+b$.

The paper descends to the diagonal and notes that for $r\ge3$ its argument
breaks down. Reduced solutions take the place of the diagonal, and they can be
off the diagonal: $(1,2)$ is a reduced solution for $r=3$, $k=7$.

**G3 (`reduced_bounds`).** A reduced solution has $2(b-a)\le r$ and
$a\le2r$.

- From $(b-a)(b+a)=b^2-a^2\le ra$ and $b+a\ge2a$: $2a(b-a)\le ra$, so
  $2(b-a)\le r$.
- Put $d=b-a\ge0$. By G1, $3ab\le kab=a^2+b^2+r(a+b)$. Substituting
  $b=a+d$, this is $a^2+ad-d^2\le r(2a+d)$, that is,
  \[
  a(a-2r)+d(a-d-r)\le0 .
  \]
  If $a>2r$, the first term is at least $a>0$, and $a-d-r\ge a-\tfrac r2-r>0$
  makes the second term nonnegative: a contradiction.

So for each $r$ there are finitely many reduced solutions:
$1\le a\le 2r$ and $a\le b\le a+r/2$.

**G4 (`k_le_reduced`, `k_range`, `k_range_sharp`).** Every solution has
$3\le k\le2r+2$, and both ends occur. By G2 it suffices to bound $k$ on a
reduced solution.

- If $a=1$: $b^2\le1+r$, so $1\le b\le r+1$ and $(b-1)(b-r-1)\le0$, that is,
  $b^2+r+1\le(r+2)b$. Then $kb=1+r+b^2+rb\le(2r+2)b$.
- If $a\ge2$ (so $b\ge2$): $a^2\le ab$, $b^2\le a^2+ra$, $2ra\le rab$ and
  $2rb\le rab$. Hence
  $2kab=2a^2+2b^2+2ra+2rb\le4a^2+4ra+2rb\le(4+3r)ab$, so
  $k\le2+\tfrac32r\le2r+2$.

The ends: $(1,1)$ gives $k=2r+2$, and $(2r,2r)$ gives
$12r^2=3\cdot4r^2$, so $k=3$.

**G5 (`key`).** §2.2 holds for every $r$: $m=r(a+b)/\gcd(a,b)^2$ is a
positive integer dividing $r(k+2)$.

**G6 (`thm12`).** For $r=1$, G4 gives $k\in\{3,4\}$. With G5: if $k=3$, then
$m\mid5$, so $m\in\{1,5\}$; if $k=4$, then $m\mid6$, and $m=1$ and $m=6$ fail
by the $k=4$ cases of §2.3 (identity (2) does not involve $r$), so
$m\in\{2,3\}$. This is the inclusion half of the paper's Theorem 1.2;
`values_one` below gives all of it.

### 3.1 Two-periodicity and the set of values (G7)

Write $v(a,b)=r(a+b)/\gcd(a,b)^2$ (`normVal`, a rational number). A solution
$(p_0,p_1)$ extends to a two-sided Vieta chain $p_{n+1}=kp_n-r-p_{n-1}$, in
which every pair $(p_n,p_{n+1})$ is a solution (`Sol.next`).

**Lemma (`normVal_eq`).** If $x,y$ are coprime and $(xg,yg)$ is a solution,
then $v(xg,yg)=kxy-x^2-y^2$. This is (1).

**Theorem (`two_periodic`).** If $(a,b)$ is a solution, $c=kb-r-a$ and
$d=kc-r-b$, then $v(c,d)=v(a,b)$.

*Proof.* Let $g=\gcd(a,b)$, $a=gx$, $b=gy$. Then $c+r=g(ky-x)$. The pair
$(b,c)$ is a solution and $d$ is the other root for it, so $bd=c(c+r)$, that is,
$gy\,d=c\,g(ky-x)$ and $yd=c(ky-x)$. Since $\gcd(y,ky-x)=\gcd(y,x)=1$, $y$
divides $c$: $c=ty$ and then $d=t(ky-x)$, where $t>0$ and $ky-x>0$ because
$c,d>0$. So $(c,d)=t\,(y,\,ky-x)$ with $y$ and $ky-x$ coprime, and by the lemma

\[
v(c,d)=ky(ky-x)-y^2-(ky-x)^2=kxy-x^2-y^2=v(a,b). \qquad\square
\]

So along a chain the value alternates between two numbers. The chain through a
solution $(a,b)$ also contains the pair $(a,\,ka-r-b)$ (one step on the other
side, up to order), so its values are

\[
\mathrm{chainVals}(a,b)=\{v(a,b),\ v(a,\,ka-r-b)\}.
\]

**Theorem (`values_eq`).** For every $k$, the set of values $v(a,b)$ over all
solutions with this $k$ is the union of $\mathrm{chainVals}(a,b)$ over the
reduced solutions with this $k$.

*Proof.* `chainVals` does not change under the step $(a,b)\mapsto(a,ka-r-b)$
(`chainVals_jump`) or under a swap (`chainVals_swap`, from `two_periodic`), so
the descent of G2 keeps it (`descent_chainVals`), and $v(a,b)$ lies in
$\mathrm{chainVals}(a,b)$. Conversely, both elements of
$\mathrm{chainVals}(a,b)$ are values of solutions. $\square$

By G3 this reduces the value set for each $r$ to finitely many reduced
solutions. Lean enumerates them with `interval_cases` for $r=1,2,3$
(`reduced_one`, `reduced_two`, `reduced_three`) and evaluates `chainVals`
(`values_one`, `values_two`, `values_three`):

| $r$ | reduced solutions $(a,b;k)$ | values |
|---|---|---|
| 1 | $(1,1;4)$, $(2,2;3)$ | $k=3$: $1,5$; $k=4$: $2,3$ |
| 2 | $(1,1;6)$, $(2,2;4)$, $(4,4;3)$ | $k=3$: $1,5$; $k=4$: $2,3$; $k=6$: $4,8$ |
| 3 | $(1,1;8)$, $(1,2;7)$, $(2,2;5)$, $(3,3;4)$, $(6,6;3)$ | $k=3$: $1,5$; $k=4$: $2,3$; $k=5$: $3,21$; $k=7$: $9$; $k=8$: $6,15$ |

For $r=2$ this proves the value sets of Conjecture 4.2 a second time, without
the congruences of §2.3. For $r=1$ it is the paper's Theorem 1.2.

**$r=11$ (`eleven_three`).** $(21,28)$ solves $(E_{11})$ with $k=3$:
$441+231+784+308=1764=3\cdot21\cdot28$. Its gcd is $7$, so its value is
$11\cdot49/49=11$. So the values for $k=3$ are not $\{1,5\}$ for every $r$.

**Remark (by hand, not in Lean).** For every $r\ge1$, $(2r,2r)$ is a reduced
solution with $k=3$ and neighbour $(2r,3r)$, so the values for $k=3$ include
$v(2r,2r)=1$ and $v(2r,3r)=5r^2/r^2=5$. Likewise $(r,r)$ is a reduced
solution with $k=4$ and neighbour $(r,2r)$, so the values for $k=4$ include
$2$ and $3$. Only the equality with $\{1,5\}$ and $\{2,3\}$ can fail, as it
does at $r=11$.

## 4. Computation (not machine-checked)

The programs in [`programs/`](programs/) are evidence only; the Lean proof
does not use them.

- `vieta_brute.c` enumerates all pairs $a\le b\le N$. For $r=2$ and
  $N=60000$ it finds 28 solutions, all with allowed $(k,m)$, and all six
  values ([log](logs/vieta_brute_r2_60000.log)). For $r=3$ and $r=11$ with
  $N=20000$ it lists 36 and 86 solutions
  ([r=3](logs/vieta_brute_r3_20000.log), [r=11](logs/vieta_brute_r11_20000.log)).
- `vieta_chains.py` walks the $r=2$ chains up to $10^{200}$ (1091 solutions
  with $a\le b$, all with allowed values). For each $r\le40$ it finds the
  reduced solutions by searching $a\le4r+4$, beyond the bound of G3, and checks
  the bounds of G1, G3 and G4 on them; checks (3) and two-periodicity along
  every chain; compares the chains with an enumeration over divisors
  ($b\mid a(a+r)$) for $b\le20000$; and prints the values for each $(r,k)$
  ([log](logs/vieta_chains_r40.log)).

These tables apply `values_eq`, which is in Lean, to reduced solutions found by
the program; the enumeration itself is not machine-checked for $r\ge4$. For
$r=11$ the program finds the values $1,5,11,55$ for $k=3$ and $2,3,11,66$ for
$k=4$, and the C enumeration agrees. For $r\le40$, the values for $k=3$ differ
from $\{1,5\}$ exactly when $r$ is a multiple of $11$, $19$, $29$ or $31$, and
the values for $k=4$ differ from $\{2,3\}$ exactly when $r$ is a multiple of
$11$, $13$, $23$ or $37$. These are the primes up to $40$ that are $\equiv\pm1$
modulo $5$, and modulo $12$, respectively. This is an observation from the
computation, not a proved statement.

## Credit

The paper is Steven J. Miller, Dimitrios Nikolakopoulos and Anitha Srinivasan,
*Fibonacci Numbers and Vieta Jumping for a Rational Diophantine Equation*,
[arXiv:2605.19083v2](https://arxiv.org/abs/2605.19083v2). The following are
the paper's:

- the problem: the equations $(a+r)/b+(b+r)/a=k$ and the quantity
  $(a+b)/\gcd(a,b)^2$;
- the results for $r=1$: Theorem 1.1 ($k\in\{3,4\}$ and the description of all
  solutions by Vieta jumps) and Theorem 1.2 (the values $1,5$ for $k=3$ and
  $2,3$ for $k=4$);
- for $r=2$, the descent to the diagonal and $k\in\{3,4,6\}$ (Remark 4.1;
  §2.1 here);
- for general $r$, the analysis of diagonal solutions and the observation that
  the descent breaks down for $r\ge3$ (§4.1 of the paper);
- Conjecture 4.2 itself.

This entry adds:

- the divisibility step $m\mid r(k+2)$ (§2.2) and the congruence eliminations
  (§2.3), which complete the proof;
- the Lean proof of all of the above;
- the extension to general $r$ in §3 (descent to reduced solutions, their
  bounds, $k\le2r+2$, two-periodicity and the value sets), which uses standard
  Vieta-jumping technique.

No novelty is claimed for any of these steps. No human has reviewed them, and
nothing has been reported to the paper's authors. The paper presents this line
of problems as part of a student-mentoring project.
