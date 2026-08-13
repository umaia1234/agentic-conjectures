**English** | [한국어](README.ko.md)

# Let's Prove Goldbach prize problem 2

The official [prize page](https://www.dimostriamogoldbach.it/en/prizes/)
offers **€100** for problem 2. On 2026-08-12 its displayed state was
**“No solutions received”**; on 2026-08-13 it displayed
**“Solution under review.”** The page does not identify the submitter or
publish the submitted solution.

For fixed integers \(1<n_1<n_2<n_3\), let
\(\mathrm{t\_space}_{(n_1,n_2,n_3)}(x)\) be the \(x\)-th positive integer
divisible by none of \(n_1,n_2,n_3\). The advertised problem asks for a
finite-case formula \(f\) satisfying

\[
 \left|f(x)-\mathrm{t\_space}_{(n_1,n_2,n_3)}(x)\right|
 \leq \frac{n_3^2}{2}
 \qquad(x>0).
\]

Its formula-language clause says that the expression

> “includes only operators of sum, difference, product, division and
> distinction between a finite number of cases.”

## Result

There is an exact periodic formula, so its error is zero. Put

\[
 P=n_1n_2n_3
\]

and list in increasing order all allowed residues in one half-open period:

\[
 R=(r_0,r_1,\ldots,r_{A-1})
   =\operatorname{sort}\{r:0\leq r<P,\ r>0,\
       n_1\nmid r,\ n_2\nmid r,\ n_3\nmid r\}.
\]

The list is nonempty because \(r=1\) is allowed. For \(x>0\), set

\[
 m=x-1,\qquad q=\left\lfloor\frac mA\right\rfloor,\qquad
 j=m-Aq=m\bmod A.
\]

Then

\[
 f(x)=Pq+r_j. \tag{1}
\]

Every divisibility predicate has period \(P\). Consequently the allowed
positive integers, in increasing order, are exactly

\[
 r_0,\ldots,r_{A-1},\quad
 P+r_0,\ldots,P+r_{A-1},\quad
 2P+r_0,\ldots .
\]

Formula (1) selects the required entry of this sequence. Thus

\[
 f(x)=\mathrm{t\_space}_{(n_1,n_2,n_3)}(x)
\]

for every positive \(x\), which is stronger than the requested estimate.

## Statement faithfulness and finite-case caveat

The formal `Allowed` predicate is positivity together with nondivisibility
by each of the three moduli, exactly matching the source's description of
`t_space`. The product \(P\), rather than the least common multiple, is used
only as a convenient common period. The source's half-square error bound is
formalized without fractions as

\[
 2\,\operatorname{dist}(f(x),\mathrm{t\_space}(x))\leq n_3^2,
\]

which is equivalent for natural-number values.

There is one specification issue that the mathematical proof cannot decide.
For each fixed triple, (1) is a quotient formula with the finite table
\(r_0,\ldots,r_{A-1}\), hence it is a finite distinction of cases. The
remainder can also be written using only difference, product, and integer
division as \(m-A\lfloor m/A\rfloor\). However, the number and contents of
the residue cases depend on \(n_1,n_2,n_3\). The prize page does not say
whether “a finite number of cases” may depend on the fixed parameters, or
whether it intends a single parameter-independent syntactic bound and
forbids a generated lookup table.

Lean cannot express that informal formula-language restriction in the
proposition `statement`; it verifies the explicit computable residue-list
definition and the claimed bound. Accordingly, this repository records a
proof under the literal per-fixed-triple finite-case interpretation. A
stricter uniform closed-form interpretation would be a different, presently
unformalized specification.

## Machine verification

The sorry-free module
[`GoldbachPrize2.lean`](../../AgenticConjectures/GoldbachPrize2.lean) proves:

- `exact_formula0`: the zero-based residue formula equals `Nat.nth` of the
  allowed predicate;
- `exact_formula`: the source's one-based `formula` equals `tSpace`;
- `proved`: the advertised error bound, with zero distance, for every
  admissible triple and every positive index.

```bash
lake env lean AgenticConjectures/GoldbachPrize2.lean
```

See [DETAILS.md](DETAILS.md) for the proof map and trust boundary.

## Prize and research status

The 2026-08-13 wording **“Solution under review”** is not an acceptance or
prize award. Because the official page gives no submitter or solution
details, this repository makes no inference about who submitted it or
whether it is related to the construction here.

This formalization has not been accepted or reviewed by the sponsor. It
claims neither novelty nor priority, and no external submission was made
from this repository; any such submission requires human approval.
