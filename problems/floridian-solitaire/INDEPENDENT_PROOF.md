# An immediate losing position for every `n > 6` in Floridian solitaire

This note answers the second open question in
Meyerowitz--Curran--Locke--Low,
*Floridian Solitaire: A New Variant of Bulgarian Solitaire*,
arXiv:2608.08313v1.  The paper already gives immediate losses for odd `n` and
for `n = 1 (mod 3)`, leaving `n = 0,2 (mod 6)` open.  The construction below
settles those two residue classes.

## A family of immediate losses

Let `r >= 2`, let `delta` be either zero or one, and let `lambda` be a
partition having `r` parts such that its distinct part sizes are exactly

\[
 r+2+2\delta,\ r+4+2\delta,\ldots,\ r+2+2\delta+2h,                 \tag{1}
\]

each with positive multiplicity.  Then `lambda` is an immediate loss.

Indeed, every part in (1) is greater than one.  In a possibly legal
alpha-move, if one copy of a part greater than one is selected, all copies of
that size must be selected; otherwise the output contains both `m-1` and `m`
and is not separated.  Moreover, the selected size classes must form a lower
prefix of (1).  If a class is selected while the class two below it is not,
the output contains two sizes differing by one.  In particular, every
possibly legal selection includes the smallest size class.

No part disappears, and the alpha-move adds one new part, so the resulting
partition has `p=r+1` parts.  Its reduced smallest class has size

\[
 (r+2+2\delta)-1=p+2\delta.
\]

If `delta=0`, the result contains a part of size `p`; if `delta=1`, it contains
a part of size `p+2`.  In either case it is not a member of `T(n)` by the
paper's pre-separated-position lemma.  Thus there is no legal alpha-move from
`lambda`.

## Which totals the family realizes

Fix `r` and `delta`, and put `b=r+2+2 delta`.  Write the `r` parts as
`b+2i_1,...,b+2i_r`, where the set of indices is `{0,...,h}`.  For every

\[
 0\le K\le {r(r-1)\over2},                                      \tag{2}
\]

the indices can be chosen to have sum `K` and consecutive support.  To see
this, choose `h` for which

\[
 {h(h+1)\over2}\le K\le hr-{h(h+1)\over2}.
\]

The intervals in this display cover (2): consecutive intervals overlap or
touch because `hr+1 >= (h+1)^2` for `h <= r-2`.  Begin with one copy of each
index `0,...,h`; the remaining `r-h-1` indices, each lying between zero and
`h`, can realize every remaining sum in the required range.

It follows that the `delta=0` family realizes, in steps of two, every total in

\[
 J_r=[r^2+2r,\ 2r^2+r],                                         \tag{3}
\]

and the `delta=1` family realizes every total of the same parity in

\[
 I_r=[r^2+4r,\ 2r^2+3r].                                       \tag{4}
\]

Take `r` even.  The first intervals are

\[
J_2=[8,10],\quad I_2=[12,14],\quad
J_4=[24,36],\quad I_4=[32,44],\quad J_6=[48,78].
\]

For every even `r >= 6`, `J_r` and `J_(r+2)` overlap or are adjacent on the
even lattice, since

\[
 (2r^2+r)+2-((r+2)^2+2(r+2))=r^2-5r-6\ge0.
\]

Consequently (3)--(4) cover every even integer from 8 onward except
`16,18,20,22,46`.  Of these, only 18 and 20 are congruent to zero or two
modulo six; the other three were already covered by the paper's
`n=1 (mod 3)` construction.

The two remaining immediate losses are

\[
 18=1+5+5+7,\qquad 20=4+4+6+6.                                 \tag{5}
\]

For the first partition, direct consideration of whether the `1`, the two
`5`s, and the `7` are selected shows that every alpha output is either
unchanged, nonseparated, or (when all parts are selected) contains a part of
size `p=4`.  For the second, selecting the `6`s without the `4`s is
nonseparated, selecting just the `4`s creates adjacent sizes 2 and 3, and
selecting all parts creates adjacent sizes 3 and 4.  Hence both are immediate
losses.

Combining (1)--(5) with the constructions already given in the paper proves:

> **Theorem.** Floridian solitaire has a losing position for every integer
> `n > 6`; in fact it has an immediate losing position for every such `n`.

`verify_independent.py` implements the definitions directly and checks the
displayed construction for every `n=7,...,500`, including all 165 formerly
open residue-class cases in that range.
