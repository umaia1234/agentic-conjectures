**English** | [한국어](README.ko.md)

# Vieta jumping with $r=2$: the values of $2(a+b)/\gcd(a,b)^2$

The problem and the conjecture on this page are due to Steven J. Miller,
Dimitrios Nikolakopoulos and Anitha Srinivasan. They pose the conjecture as
Conjecture 4.2 (in §4.1) of their paper *Fibonacci Numbers and Vieta Jumping for
a Rational Diophantine Equation*,
[arXiv:2605.19083v2](https://arxiv.org/abs/2605.19083v2). This entry proves
their conjecture in Lean 4. The steps that are the paper's and the steps that
this entry adds are listed in the [Credit](DETAILS.md#credit) section of the
mathematical details.

## The conjecture

The paper studies the positive integer solutions $(a,b)$ of

\[
\frac{a+r}{b}+\frac{b+r}{a}=k,\qquad k\in\mathbb Z .
\]

For $r=1$ it shows that only $k=3$ and $k=4$ occur, that Vieta jumps reach
every solution from $(2,2)$ (for $k=3$) or $(1,1)$ (for $k=4$), with a
Fibonacci formula for $k=3$ (Theorem 1.1), and proves that $(a+b)/\gcd(a,b)^2$
takes only the values $1,2,3,5$ (Theorem 1.2). For $r=2$ its Remark 4.1 runs
the same descent to the diagonal and finds $k\in\{3,4,6\}$; for $r\ge3$ the
paper notes that this descent breaks down.

In our words, Conjecture 4.2 says: for every solution with $r=2$,

\[
\frac{2(a+b)}{\gcd(a,b)^2}\in\{1,2,3,4,5,8\},
\]

and the values that occur are exactly $1,5$ for $k=3$, exactly $2,3$ for
$k=4$, and exactly $4,8$ for $k=6$.

## Result

`AgenticConjectures.VietaR2Gcd.statement_holds` proves
`AgenticConjectures.VietaR2Gcd.statement`, the formal version of Conjecture
4.2, in [`VietaR2Gcd.lean`](../../AgenticConjectures/VietaR2Gcd.lean), without
`sorry`, extra axioms or `native_decide`. The proof has four steps, given in full
in the [mathematical details](DETAILS.md):

1. The paper's descent (Remark 4.1) gives $k\in\{3,4,6\}$.
2. With $g=\gcd(a,b)$, $a=gx$, $b=gy$, the value $m=2(a+b)/g^2$ equals
   $kxy-x^2-y^2$, and $m$ divides $2(k+2)$.
3. The identity $(x+y)^2+m=(k+2)xy$, read modulo $3,4,5,8,9,16$ or $25$, rules
   out every other divisor.
4. The pairs $(4,4),(4,6),(2,2),(2,4),(1,1),(1,3)$ give the six values.

The same module also proves, for every $r>0$ (namespace `GeneralR`): $3\le
k\le2r+2$ with both ends attained; descent to *reduced* solutions, of which
there are finitely many; that the value $r(a+b)/\gcd(a,b)^2$ repeats with
period two along each Vieta chain; and hence the complete sets of values for
$r=1,2,3$. For $r=2$ this gives a second proof of the value sets, without
congruences. For $r=11$ the values with $k=3$ include $11$, so the pattern
"$k=3$ gives $1$ and $5$" does not persist for every $r$.

## Lean declarations

All names are in the namespace `AgenticConjectures.VietaR2Gcd`.

| Declaration | Statement |
|---|---|
| `statement`, `statement_holds` | Conjecture 4.2, and its proof |
| `IsSolution.sol` | the equation over $\mathbb Q$ clears to $a^2+2a+b^2+2b=kab$ |
| `k_cases` | for $r=2$, $k\in\{3,4,6\}$ (the paper's Remark 4.1) |
| `key` | $g\,m=r(x+y)$ and $m\mid r(k+2)$, for coprime $x,y$ and any $r$ |
| `normSum_cases` | every $r=2$ solution has $(k,m)$ among the six allowed pairs |
| `GeneralR.k_range`, `GeneralR.k_range_sharp` | $3\le k\le 2r+2$, and $(1,1)$, $(2r,2r)$ attain the ends |
| `GeneralR.descent`, `GeneralR.reduced_bounds` | every solution descends to a reduced one; reduced solutions have $2(b-a)\le r$ and $a\le 2r$ |
| `GeneralR.thm12` | the paper's Theorem 1.2 ($r=1$), in coprime form |
| `GeneralR.two_periodic` | two Vieta steps keep the value $r(a+b)/\gcd(a,b)^2$ |
| `GeneralR.values_eq` | the values for a given $k$ are those of the reduced solutions and their neighbours |
| `GeneralR.values_one`, `GeneralR.values_two`, `GeneralR.values_three` | the value sets for $r=1,2,3$ |
| `GeneralR.eleven_three` | $r=11$, $(a,b)=(21,28)$: $k=3$ and value $11$ |

`status.yaml` lists every public theorem of the module, so the axiom audit
covers all of them.

## Statement faithfulness

There is no Formal Conjectures file for this conjecture, so the Lean statement
is ours. It makes these readings explicit:

- $k$ is an integer, as in the paper's setup in §1. With rational $k$ the claim
  would be false: $(a,b)=(1,2)$ gives $k=11/2$ and the value $6$.
- $a$ and $b$ are positive natural numbers. Both fractions, and
  $2(a+b)/\gcd(a,b)^2$, are computed in $\mathbb Q$, with `Nat.gcd`.
- "If $k=3$, the values are $1$ and $5$" is read as an equality of sets: the
  values over all solutions with $k=3$ are exactly $1$ and $5$. This covers
  both readings, inclusion and attainment. The same goes for $k=4$ and $k=6$.

`statement` is the conjunction of the membership claim for every integer $k$
and the three set equalities. The module docstring repeats these readings.

## Computation (supporting evidence only)

The Lean proof does not use any computation. Two programs, written separately
from the Lean proof and from each other, check the same facts numerically:

- [`programs/vieta_brute.c`](programs/vieta_brute.c) tests every pair
  $1\le a\le b\le N$ directly. For $r=2$ it checks that each solution has an
  allowed pair $(k,m)$ and that all six values occur.
- [`programs/vieta_chains.py`](programs/vieta_chains.py) walks the Vieta chains
  of $r=2$ up to $10^{200}$. For each $r\le R$ it also checks the bounds on
  reduced solutions, the divisibility $m\mid r(k+2)$ and the period-two
  pattern, and compares the chains with a separate enumeration over divisors
  ($b\mid a(a+r)$).

From this directory:

```bash
mkdir -p build && cc -O2 -std=c99 -Wall -Wextra -o build/vieta_brute programs/vieta_brute.c && build/vieta_brute 60000
build/vieta_brute 20000 3
build/vieta_brute 20000 11
python3 programs/vieta_chains.py --height 200 --max-r 40 --brute 20000
```

On 2026-10-25, on an Apple silicon Mac, these took 1.05 s (including the
compilation), 0.11 s, 0.11 s and 4.92 s; the outputs are in [`logs/`](logs/).
The $r=2$ enumeration finds 28 solutions with $a\le b\le 60000$. The CI
entries in `status.yaml` rerun the first and last commands. To rebuild the
Lean proof:

```bash
lake build AgenticConjectures.VietaR2Gcd
```

## Status and credit

The conjecture is proved in Lean. No human has reviewed the proof or this
write-up, and nothing has been reported to the authors or submitted anywhere.
No novelty is claimed: the descent and the reduction to $k\in\{3,4,6\}$ are
the paper's, and the remaining steps use standard Vieta-jumping and congruence
arguments. See the [Credit](DETAILS.md#credit) section for the full split.

## Sources checked

Checked on 2026-10-25 (about 15:10 UTC):

- arXiv: [2605.19083](https://arxiv.org/abs/2605.19083) is at v2
  (2026-05-27). An arXiv search for "Vieta jumping" finds only this paper and
  F. Lemmermeyer, *Vieta jumping and small norms in quadratic number fields*,
  [arXiv:2601.15229](https://arxiv.org/abs/2601.15229), which the paper cites
  as related work.
- OpenAlex lists no work citing the paper (work W7161841799). Its 2026 records
  on Vieta jumping are about the $r=1$ equation or unrelated.
- Formal Conjectures: no issue or pull request mentions the paper, its title or
  Vieta jumping.
- GitHub code and repository search, Zenodo and MathDB: no result about $r=2$
  or this conjecture.
- The OpenConjecture dataset (last updated 2026-09-25) lists the conjecture as
  open, as entry 2765.
