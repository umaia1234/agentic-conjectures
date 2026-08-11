# Immediate losses for every size `n > 6` in Floridian solitaire

## Claim resolved

Meyerowitz, Curran, Locke, and Low, *Floridian Solitaire: A New
Variant of Bulgarian Solitaire*, arXiv:2608.08313v1, ask:

> Prove that there is a losing position for each \(n>6\). The open
> cases are \(n=6m\) and \(n=6m+2\).

The question occurs in the paper's "Directions for further research."
The definitions used below are those in the paper's Floridian-solitaire
section.  The construction proves the stronger assertion that every
\(n>6\) has an **immediate loss**.

Primary source:

- <https://arxiv.org/abs/2608.08313>
- <https://arxiv.org/html/2608.08313>

## Definitions from the paper

A partition is **separated** if any two distinct part sizes differ by at
least two.  From a separated partition \(\lambda_1\), an
\(\alpha\)-move selects \(s\geq 1\) individual parts, reduces every
selected part by one (deleting a selected 1-part), and adds one new
part of size \(s\).  The resulting partition \(\lambda_2\) must

1. differ from \(\lambda_1\),
2. be separated, and
3. have separated \(\Omega(\lambda_2)\).

If \(p\) is the number of parts of a separated \(\lambda_2\), the
paper proves that condition 3 is equivalent to \(\lambda_2\) having
no part of size \(p\) or \(p+2\).  Its notation \(T(n)\) denotes
exactly these eligible middle-of-turn partitions.  An immediate loss
is an \(\alpha\)-position with no legal \(\alpha\)-move.

For completeness, this criterion follows directly from the move. Reducing
all existing parts preserves the differences between their distinct sizes,
so the only possible new adjacency involves the newly added \(p\)-part.
An old \(m\)-part becomes \(m-1\), adjacent to \(p\), exactly when
\(m=p\) or \(m=p+2\). An old \((p+1)\)-part instead becomes another
\(p\)-part, and equal parts are allowed; deleting old 1-parts introduces no
new positive size. Thus precisely the old \(p\)- and \((p+2)\)-parts are
forbidden.

## Block lemma

**Lemma.**  Let \(r\geq2\), let \(\delta\in\{0,1\}\), and put

\[
    a=r+2+2\delta.
\]

Suppose \(\lambda\) has exactly \(r\) parts and its distinct part
sizes are exactly

\[
    a,a+2,a+4,\ldots,a+2h
\]

for some \(0\leq h\leq r-1\), with every displayed size occurring at
least once.  Then \(\lambda\) is an immediate loss.

**Proof.**  Consider any nonempty selection of parts.  If it selects
some but not all copies of one size, the selected copies decrease by
one while the unselected copies remain fixed, so the result has two
distinct adjacent sizes and is not separated.  Thus, in any candidate
whose result is separated, every size class is either selected in full
or not selected.

If a class \(a+2j\), \(j>0\), is selected while the immediately lower
class \(a+2j-2\) is not, the result contains both \(a+2j-1\) and
\(a+2j-2\).  It is again not separated.  Consequently, the selected
classes of any candidate with separated result form a nonempty lower
prefix.  In particular, all copies of the smallest size \(a\) are
selected and become parts of size

\[
    a-1=r+1+2\delta.
\]

All original parts exceed one, so none disappears.  The move adds one
new part, hence its result has \(p=r+1\) parts.  If \(\delta=0\), the
result contains a part of size \(p\); if \(\delta=1\), it contains a
part of size \(p+2\).  In either case it is not in \(T(n)\), so the
move is illegal.  Every nonempty selection is illegal, proving the
lemma. \(\square\)

## Every integer in two block intervals is represented

Write the \(r\) parts as

\[
    a+2y_1,\ldots,a+2y_r.
\]

The block hypothesis says that the set of values among the \(y_i\) is
\(\{0,1,\ldots,h\}\).  We need the following elementary fact.

**Representation lemma.**  For every integer

\[
    0\leq K\leq \frac{r(r-1)}2,
\]

there are \(r\) nonnegative integers \(y_i\), with support
\(\{0,1,\ldots,h\}\) for some \(h\), whose sum is \(K\).

**Proof.**  For a fixed \(h\), first use one copy of each of
\(0,1,\ldots,h\).  Their sum is

\[
    L_h=\frac{h(h+1)}2.
\]

There are \(r-h-1\) slots left.  Filling each with a value from
\(0\) through \(h\) realizes every additional integer from zero
through \(h(r-h-1)\) (greedily use copies of \(h\), then one
remainder).  Thus fixed \(h\) realizes every integer in

\[
    A_h=\left[\frac{h(h+1)}2,
              hr-\frac{h(h+1)}2\right].
\]

For \(0\leq h\leq r-2\), the lower endpoint of \(A_{h+1}\) is at
most one more than the upper endpoint of \(A_h\), because

\[
 \left(hr-\frac{h(h+1)}2\right)
 -\frac{(h+1)(h+2)}2
 =h(r-h-2)-1\geq-1.
\]

The first interval starts at zero, and \(A_{r-1}\) ends at
\(r(r-1)/2\).  The integer intervals therefore cover the whole
claimed range. \(\square\)

It follows that, for fixed \(r\), the block lemma supplies an
immediate loss for every integer of the same parity as \(r\) in each
of the following inclusive intervals (successive values differ by
two):

\[
\begin{aligned}
J_r&=[r^2+2r,\;2r^2+r] &&(\delta=0),\\
I_r&=[r^2+4r,\;2r^2+3r] &&(\delta=1).
\end{aligned}
\]

Indeed, the sum of the parts is

\[
    r(r+2+2\delta)+2K,
    \qquad 0\leq K\leq\frac{r(r-1)}2.
\]

This is also a direct algorithm for constructing the partition: find
an \(h\) for which \(K\in A_h\), place one copy of every value
\(0,\ldots,h\), and greedily distribute \(K-L_h\) over the remaining
slots.

## Coverage of the formerly open congruence classes

Take \(r\) even.  The first intervals are

| \(r\) | \(J_r\) | \(I_r\) |
|---:|:---:|:---:|
| 2 | 8--10 | 12--14 |
| 4 | 24--36 | 32--44 |
| 6 | 48--78 | 60--90 |
| 8 | 80--136 | 96--152 |

Here and below an even-endpoint interval means every even integer in
it. Moreover, successive \(J\)-intervals overlap or are adjacent on the
even lattice for every even \(r\geq6\), since

\[
 (2r^2+r)+2-\big((r+2)^2+2(r+2)\big)
 =r^2-5r-6=(r-6)(r+1)\geq0.
\]

Their lower endpoints tend to infinity. Hence
\(J_6,J_8,J_{10},\ldots\) cover every even \(n\geq48\). Together with
the displayed smaller intervals, the block construction covers every even
\(n\geq8\) except

\[
 16,18,20,22,46.
\]

Of these, only \(18\) and \(20\) belong to the formerly open classes
\(0,2\pmod6\); the other three are \(1\pmod3\) and are covered by the
paper's family.

For those two values use

\[
   \lambda_{18}=(1,5,5,7),\qquad
   \lambda_{20}=(4,4,6,6).
\]

Both are separated.  For \(\lambda_{18}\):

- Selecting a 7 but not the two 5s leaves an unchanged 5 adjacent to
  the reduced 6.
- Selecting only the 1 recreates the same partition, which the
  definition excludes.
- Selecting the two 5s but not the 7 creates a new part 2 or 3,
  according as the 1 is unselected or selected.  It is adjacent to an
  unchanged 1 or a reduced 4, respectively.
- Selecting the two 5s and the 7, but not the 1, creates a 3 adjacent
  to a reduced 4.
- Selecting all four parts gives \((4,4,4,6)\).  This is separated,
  but it has \(p=4\) parts and contains a part of size \(p\), so it is
  not in \(T(18)\).

These exhaust all selections because equal parts larger than one must
be selected together in any separated candidate.  Thus
\(\lambda_{18}\) is an immediate loss.

For \(\lambda_{20}\), selecting just the 6-class leaves reduced 5s
adjacent to unchanged 4s; selecting just the 4-class creates a new 2
adjacent to reduced 3s; and selecting both classes creates a new 4
adjacent to reduced 3s.  Thus \(\lambda_{20}\) is an immediate loss.

This proves immediate losses in both classes that the paper leaves
open, \(n\equiv0,2\pmod 6\), for every \(n>6\).

## Completing the exact scope of the paper's question

The paper already gives these immediate losses:

- If \(n=2m+1>3\), use \((1,m,m)\).  This covers every odd \(n\).
- If \(n=3m+1>4\), use \((1,3^m)\).  In particular, this covers the
  remaining even class \(n\equiv4\pmod6\).

For completeness, the first construction has only three possible
size-class selections.  Selecting only the 1 is the forbidden
identity move; selecting the two \(m\)-parts creates adjacent 1 and 2;
and selecting all three parts creates a part of size \(p=3\).  The
second construction is analogous: selecting only the 1 is the
identity, selecting all 3-parts leaves adjacent 1 and 2, and selecting
everything creates a part of size \(p=m+1\).

Combining those published families with the block construction and
the two exceptional witnesses proves:

**Theorem.**  For every integer \(n>6\), Floridian solitaire has an
immediate-loss position, and therefore a losing position.

## Machine check

`verify.py` is independent of the lemmas above.  It constructs a
witness for every requested \(n\), enumerates every nonempty selection
profile of individual parts (equal copies are compressed only because
they give the same result), applies the paper's literal \(\alpha\)-move
definition, and checks that no result is legal.  By default it checks
all \(n=7,\ldots,500\):

```sh
python3 problems/floridian-solitaire/verify.py
```

The script also cross-checks the paper's criterion for \(T(n)\)
against direct computation of \(\Omega\) whenever the intermediate
partition is separated.

The final 2026-08-11 default run checked 494 witnesses and 334,670
nonempty selection profiles. The independently implemented
`verify_independent.py` checked the same range, including all 165 formerly
open residue-class cases:

```sh
python3 problems/floridian-solitaire/verify_independent.py
```

A separate indexed subset audit checked the new residue classes through
\(n=10000\). These computations support the proof but are not a substitute
for peer review.
