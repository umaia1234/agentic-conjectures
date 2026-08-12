**English** | [한국어](README.ko.md)

# OEIS A394666 — zero terms of `n! mod (2n-1)`

## Source statement

[OEIS A394666](https://oeis.org/A394666), offset 1, defines

\[
a(n)=n!\bmod(2n-1).
\]

Revision #38 records the following comment:

> “Conjecturally, a(n) = 0 iff n > 5 and 2*n - 1 is not a prime.”

The intended tail statement is therefore that, for every $n>5$, the
remainder vanishes exactly when $2n-1$ is composite.

## Result

The conjectured tail classification is true:

\[
n!\bmod(2n-1)=0
\quad\Longleftrightarrow\quad
2n-1\text{ is composite}
\qquad(n>5).
\]

The source sentence, if read as an unrestricted biconditional, overlooks the
displayed initial value $a(1)=0$. The complete classification at positive
indices is

\[
a(n)=0
\quad\Longleftrightarrow\quad
n=1\ \text{ or }\ (n>5\text{ and }2n-1\text{ is composite}).
\]

Both statements are proved in mathlib-based Lean 4 by
[`a_eq_zero_iff_not_prime`](../../AgenticConjectures/OeisA394666.lean) and
`zero_classification`, without unproved placeholders or non-kernel
computation.

## Proof

Set $m=2n-1$.

If $m$ is prime and $a(n)=0$, then $m\mid n!$. Every prime divisor of
$n!$ is at most $n$, but $m=2n-1>n$ for $n>1$, a contradiction.

Conversely, suppose $n>5$ and $m$ is composite. Write $m=uv$ with
$u,v>1$. Since $m$ is odd, both factors are odd, hence $u,v\ge3$. The
case $u=v=3$ would give $m=9$ and $n=5$, which is excluded. Thus either
$u=3$, $v\ge5$, or $u\ge5$, $v\ge3$. In both cases

\[
(u-2)(v-2)\ge3,
\]

so $2(u+v)\le uv+1=2n$, and therefore $u+v\le n$. It follows that

\[
2n-1=uv\mid u!v!\mid(u+v)!\mid n!.
\]

Hence the remainder is zero. Direct kernel-checked evaluation of
$n=1,\ldots,5$ gives $(0,2,1,3,3)$, establishing the corrected full
classification.

## Statement faithfulness

- The formal sequence uses `Nat.factorial` and `Nat.mod`, matching the OEIS
  factorial and least nonnegative remainder.
- The OEIS offset is 1. The definition is total on natural numbers, but every
  registered claim is about positive indices.
- Natural-number subtraction in `2*n-1` agrees with ordinary integer
  subtraction on the asserted ranges.
- The theorem `a_eq_zero_iff_not_prime` formalizes the coherent $n>5$ tail
  reading of the source comment. The additional theorem `zero_classification`
  records the source's initial exception $a(1)=0$ instead of silently
  discarding it.
- There is no Formal Conjectures Lean snapshot for this sequence; the
  definition, offset, values, and quotation were checked directly against
  OEIS revision #38 on August 12, 2026.

## Reproduction

From the repository root:

```bash
lake env lean AgenticConjectures/OeisA394666.lean
lake build
python3 scripts/check_axioms.py
```

The direct module check takes about 17 seconds on the development machine.
The full repository gates also run the no-placeholder scan and kernel axiom
audit for both registered theorems.

## Research status and prior art

As of August 12, 2026, OEIS revision #38 (last modified May 5, 2026) still
labels the classification conjectural and lists no references. Exact-sequence
and exact-formula searches of the public web, arXiv, and GitHub found sequence
implementations in JOEIS, LODA, and OEIS-Python, but no independent proof.
This negative search is not evidence of novelty.

The proof here is unreviewed, has not been confirmed by an OEIS editor, and
has not been submitted to OEIS or any other external venue.
