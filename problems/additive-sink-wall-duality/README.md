**English** | [한국어](README.ko.md)

# Additive sink subtraction: the sink–wall duality

The conjecture is due to Anjali Bhagat, Urban Larsson, Hikaru Manabe and
Takahiro Yamashita: it is equation (3) of *Additive Sink Subtraction*
([arXiv:2601.18715v3](https://arxiv.org/abs/2601.18715v3)), stated after
Corollary 4. This entry proves it in Lean 4 for every additive subtraction
set. We make no novelty claim. Our searches on 2026-10-25 found no earlier
proof, but no human has reviewed this one, and nothing has been reported to
the authors or submitted anywhere.

## The games

Fix integers $1\le s_1<s_2$ and let $S=\{s_1,s_2,s_1+s_2\}$. A move subtracts
an element of $S$ from the position, and the player who cannot move loses.
The paper compares two conventions.

- **Wall subtraction** is the classical game: the positions are the integers
  $x\ge0$, and no move may go below $0$.
- **Sink subtraction**: every $y\le0$ is a terminal position (the sink), and
  from $y\ge1$ every move $y-s$ with $s\in S$ is allowed, also into the sink.
  So a player who moves into the sink wins.

The nim-values follow the mex rule:

$$v_{\rm wall}(x)=\operatorname{mex}\{v_{\rm wall}(x-s): s\in S,\ s\le x\},$$

$$v_{\rm sink}(y)=0\ \text{ for } y\le0,\qquad v_{\rm sink}(y)=\operatorname{mex}\{v_{\rm sink}(y-s): s\in S\}\ \text{ for } y\ge1.$$

With $m=s_1$, $\delta=s_2-s_1$ and $d=\delta\bmod 2m$, put
$p=3m+2\delta-d$ if $d\le m$, and $p=m(m+2\delta+d)/\gcd(m,d)$ otherwise.
The paper's Theorem 3 proves that the sink nim-sequence is purely periodic
with period length $p$, and its Corollary 4 transfers this period length to
the outcomes of the wall game.

## The conjecture

**Equation (3) of the paper** (paraphrased). For all $x$,

$$v_{\rm wall}([x]_p)=\sigma\bigl(v_{\rm sink}([-s_2-x]_p)\bigr),$$

where $[x]_p$ is the least nonnegative residue of $x$ modulo $p$, and $\sigma$
swaps the values $0$ and $2$ and fixes $1$ and $3$.

For example, for $S=\{2,5,7\}$ the period length is $p=22$ (the paper's
Example 5). For $x=0,1,\dots,21$:

| Sequence | Values |
| --- | --- |
| $v_{\rm wall}(x)$ | `0 0 1 1 0 2 1 3 2 2 0 3 1 0 0 1 1 2 2 3 3 2` |
| $[-5-x]_{22}$ | `17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 0 21 20 19 18` |
| $v_{\rm sink}([-5-x]_{22})$ | `2 2 1 1 2 0 1 3 0 0 2 3 1 2 2 1 1 0 0 3 3 0` |

Applying $\sigma$ to the last row gives the first.

## Result

**Theorem (Lean).** Equation (3) holds for every pair $1\le s_1<s_2$ and every
integer $x$ (`statement_holds`).

On the way, the Lean files prove for every pair, with no condition on
$\gcd(s_1,s_2)$: the wall value classes (T1), the sink value classes (T2),
that $p$ is a period of both nim-sequences, the reflection symmetry (T3) of
the wall $\mathcal P$-positions, and an explicit description of them.
Section 4 of DETAILS.md explains, outside Lean, why this description is the
classical bracket formula.

## Proof idea

Let $P$ be the set of wall $\mathcal P$-positions (value $0$) and
$c=s_1+s_2$.

1. **(T1) Wall classes.** $v_{\rm wall}(x)$ is $0$, $1$, $2$ or $3$ according
   as $x\in P$, $x-s_1\in P$, $x+s_2\in P$, or none of these.
2. **(T2) Sink classes.** $v_{\rm sink}(t+1)$ is $0$, $1$, $2$ or $3$
   according as $t-c\in P$, $t\in P$, $t-s_1\in P$, or none of these.
   (T1) and (T2) follow by induction from the mex rule and from the fact that
   no two elements of $P$ differ by a move.
3. **(Gap).** No element of $P$ lies in $[p-c,p)$. This is the only place
   where the value of $p$ matters. It follows from the bracket formula: the
   $n$-th element of $P$ is $n+s_1\lfloor n/s_1\rfloor+s_2\lfloor n/N\rfloor$,
   where $N=s_1\lfloor s_2/2s_1\rfloor+\min(s_1,\ s_2\bmod 2s_1)$. We prove an
   equivalent description of $P$ for every pair, and the identity
   $p=2\operatorname{lcm}(s_1,N)+(s_1/\gcd(s_1,N))\,s_2$; together they
   leave no element of $P$ in $[p-c,p)$.
4. **(T3) and periodicity.** With (Gap), $P$ is $p$-periodic, and
   $P\cap[0,p-c-1]$ is symmetric under $x\mapsto p-c-1-x$. So, modulo $p$, the
   set $P$ is invariant under $X\mapsto-X-c-1$.
5. **Assembly.** Put $y=-s_2-x$. The reflection turns the three conditions of
   (T2) at $y$ into those of (T1) at $x$, with classes $0$ and $2$ exchanged.
   That is equation (3).

[DETAILS.md](DETAILS.md) has the complete proof, with the Lean name of each
step.

## Lean formal proof

The module
[`AgenticConjectures/AdditiveSinkWallDuality.lean`](../../AgenticConjectures/AdditiveSinkWallDuality.lean)
states the conjecture and proves `statement_holds : statement`. It rests on
three files:

- [`Games.lean`](../../AgenticConjectures/AdditiveSinkWallDuality/Games.lean):
  the two games, by their mex recursions, the period formula and $\sigma$;
- [`Classes.lean`](../../AgenticConjectures/AdditiveSinkWallDuality/Classes.lean):
  (T1), (T2), periodicity, (T3) and the assembly modulo $p$, from the mex
  recursions alone;
- [`Explicit.lean`](../../AgenticConjectures/AdditiveSinkWallDuality/Explicit.lean):
  the explicit description of $P$ and (Gap) for the paper's $p$.

There is no `sorry`, no extra axiom, and no `native_decide`, `decide +native`,
`ofReduceBool` or `ofReduceNat`. `#print axioms` lists only `propext`,
`Classical.choice` and `Quot.sound` for the theorems below. Compiled one at a
time with `lake env lean`, the four files take about 20 seconds in total (4,
5, 7 and 4 seconds, Mathlib loading included).

| Declaration | Content |
| --- | --- |
| `wall`, `sink`, `period`, `sigma` | The two games, the period length of Theorem 3, and $\sigma$. |
| `wall_eq_iff`, `sink_eq_iff` | The mex recursions, restated. |
| `statement`, `statement_holds` | Equation (3), for all $1\le s_1<s_2$ and $x\in\mathbb Z$, and its proof. |
| `wall_eq_wallClass` | (T1) The wall value classes. |
| `sink_eq_sinkClass` | (T2) The sink value classes. |
| `wall_periodic`, `sink_periodic` | $p$ is a period of the wall nim-sequence (from $0$) and of the sink nim-sequence (from $1$). |
| `wall_zero_reflect_period` | (T3) $P\cap[0,p-c-1]$ is symmetric under $x\mapsto p-c-1-x$. |
| `wall_ne_zero_of_gap` | (Gap) No wall $\mathcal P$-position lies in $[p-c,p)$. |
| `sink_period_eq_zero` | $v_{\rm sink}(p)=0$, so either representative of the residue $0$ may be used. |
| `conj_of_gap` | Equation (3) for any $p>c$ that satisfies (Gap). |
| `W`, `wall_zero_iff_W` | The bracket description of $P$, for every pair. |
| `W_indep`, `W_cover`, `W_neg_gap`, `W_top_gap`, `period_gt` | The properties of the explicit set that the proof uses. |
| `Explicit.period_spec` | The formula of Theorem 3 as $p=2s_1\ell+ks_2$ with $s_1\ell=kN$ and $\ell,k\ge1$. |

## Statement faithfulness

There is no Formal Conjectures statement of this conjecture, so the statement
is ours. Its choices, also listed in the module docstring and in
[DETAILS.md](DETAILS.md#6-statement-faithfulness):

- Both games are defined directly by their mex recursions, not through any
  formula. Moves of size $0$ are skipped so that the recursions terminate for
  every pair; for $1\le s_1<s_2$ there are none.
- `period` is the formula of Theorem 3, which the paper proves to be the
  period length. We prove that it is a period of both nim-sequences, not that
  it is the least one; the checker below confirms that it is the least period
  for every $s_2\le200$.
- $x$ ranges over $\mathbb Z$; both sides depend only on $x\bmod p$.
- $[x]_p$ is `x % p`, the least nonnegative residue. On the sink side the
  residue $0$ is the sink position $0$; the paper's table in Example 5 uses
  the position $p$ instead, which has the same value $0$.
- There is no condition on $\gcd(s_1,s_2)$ or on the regime, and $s_1=1$ is
  included.

## Computational cross-checks

The Lean proof is the certificate. Two Python scripts that share no code
recompute the facts from the definitions, with the standard library only:
[`check_duality.py`](check_duality.py) checks equation (3), the period and
its minimality, and [`check_translates.py`](check_translates.py) checks (T1),
(T2), (T3), (Gap) and the bracket formula. The argument is the largest $s_2$.

```
python3 check_duality.py 100      # 4,950 sets, about 3 s (CI)
python3 check_translates.py 100   # 4,950 sets, about 7 s (CI)
python3 check_duality.py 200      # 19,900 sets, about 40 s
```

All three runs report 0 failures.

## Prior art and credits

- The conjecture and the period formula are Bhagat, Larsson, Manabe and
  Yamashita's ([arXiv:2601.18715v3](https://arxiv.org/abs/2601.18715v3)).
- The wall side is known. Manabe's Theorem `thm:additive` and Corollary 46
  ([arXiv:2609.05358v2](https://arxiv.org/abs/2609.05358v2)) give the wall
  $\mathcal P$-positions, the least period and the wall value classes for
  coprime pairs with $s_1\ge2$, and his paper ships a Lean formalization of
  them. We used it as a reference only and copied none of its code. Larsson
  and Manabe ([arXiv:2603.10414v2](https://arxiv.org/abs/2603.10414v2))
  determine the wall nim-values in the primitive quadratic regime. The bracket
  formula is classical (*Winning Ways*; Flammenkamp).
- An earlier scouting run of this project found the route through (T1), (T2)
  and (T3) and checked it numerically.
- [DETAILS.md](DETAILS.md#8-slips-in-the-papers-final-remarks) records three
  sign slips and two table rows that are off by one in the paper's final
  remarks. None of them affects equation (3).

No human has reviewed this proof. Nothing has been reported to the authors or
submitted to MathDB, OpenConjecture, Formal Conjectures or anywhere else.
