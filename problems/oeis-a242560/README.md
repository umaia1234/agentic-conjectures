**English** | [한국어](README.ko.md)

# OEIS A242560 — closed form and even-index conjecture

## Verdict

The conjecture is **proved**, together with a stronger closed form. If $a(N)$
is the least positive integer $k$ for which

\[
\frac{N!-k}{N-k}
\]

is an integer, and $p$ is the least prime factor of $N$, then

\[
a(N)=N-\frac{N}{p} \qquad (N>1).
\]

In particular, $p=2$ at $N=2n$, so $a(2n)=n$ for every $n\ge1$.

The result is formalized in Lean 4 and checked without `sorry`, extra axioms,
or `native_decide`.

## Canonical statement and prior-art check

[OEIS A242560](https://oeis.org/A242560), checked on 2026-08-12, states:

> “Least number k such that (n!-k)/(n-k) is an integer.”

It then says, “It is conjectured that a(2n) = n.” The
[official b-file](https://oeis.org/A242560/b242560.txt) lists $a(N)$ through
$N=70$.

The entry has also asked since 2015 whether $a(N)$ equals
[A060681](https://oeis.org/A060681) for $N>1$. A060681 records the closed
form $N-N/p$, where $p$ is the least prime factor of $N$, and now records its
own even-index identity. The closed form proved here answers that equality
question affirmatively. This is important prior context: the formula itself
is already recorded by OEIS, while the A242560 entry does not supply a proof
that its displayed definition agrees with it.

Targeted searches on 2026-08-12 used the exact OEIS identifier, the displayed
formula, and the conjecture wording across the public web, arXiv, and GitHub.
No earlier proof connecting this exact definition to the closed form was
found. This is only a negative search result, not a literature review or a
claim of novelty. The proof here is unreviewed and has not been submitted to
OEIS or any other external venue.

## Proof

Fix $N>1$ and first consider a positive candidate $k<N$. Put $d=N-k$.
Because $1\le d\le N$, we have $d\mid N!$. Consequently,

\[
d\mid(N!-k) \iff d\mid k \iff d\mid N,
\]

where the last equivalence uses $N=d+k$. Thus admissible candidates below
$N$ correspond exactly to proper divisors $d$ of $N$, via $k=N-d$.

Let $p$ be the least prime factor of $N$. The largest proper divisor of $N$
is $N/p$: if $d<N$ divides $N$, then the complementary divisor $N/d$ is at
least 2, so $p\le N/d$ and hence $d\le N/p$. Minimizing $k=N-d$ therefore
gives

\[
a(N)=N-\frac{N}{p}.
\]

This value is positive and below $N$, so candidates at or above the singular
point $k=N$ cannot affect the minimum. At $N=2n$, the least prime factor is
2, and the formula becomes $a(2n)=2n-n=n$.

## Upstream data discrepancy

Under the displayed definition, $a(25)=20$, not 24 as currently listed in
the official b-file. Indeed, the closed form gives $25-25/5=20$; directly,
the denominator is $25-20=5$ and $5\mid(25!-20)$.

The Lean theorem `AgenticConjectures.OeisA242560.a_25` verifies this value.
The certificate found no other disagreement with the b-file through
$N=70$. A060681 also lists 20 at index 25. This discrepancy is documented
here only; it has not been reported to OEIS because external submissions
require human approval.

## Statement faithfulness

[`AgenticConjectures/OeisA242560.lean`](../../AgenticConjectures/OeisA242560.lean)
defines admissibility using divisibility in $\mathbb Z$, not truncated natural
subtraction. The headline does not literally say “positive”; that convention
is inferred from the data and the PARI loop beginning at $k=1$. We require
$k>0$ and exclude $k=N$, where the displayed quotient has denominator zero,
as the PARI program does. The minimum exists because $k=N+1$ gives
denominator $-1$.

The formal definition follows the unbounded mathematical headline. The PARI
program instead loops only through $k\le N!$ and fails to return its displayed
$a(1)=2$; that implementation defect does not affect the intended sequence or
these theorems. The theorem
`AgenticConjectures.OeisA242560.a_eq_sub_div_minFac` proves the closed form for
every $N>1$. The theorem `AgenticConjectures.OeisA242560.a_two_mul` assumes
$n>0$, so it covers exactly the positive even OEIS indices $N=2,4,6,\ldots$.

## Machine verification and reproduction

The Lean theorems prove the closed form for every $N>1$ and the advertised
claim for every $n\ge1$. The independent Python certificate uses only exact
integer arithmetic and:

- checks all official terms $a(1),\ldots,a(70)$ and confirms that the sole
  discrepancy is the documented value at $N=25$;
- compares the factorial definition, a separately reduced divisibility test,
  and an independently computed least-prime-factor closed form through index
  400; and
- checks $a(2n)=n$ for $1\le n\le200$.

From the repository root, run:

```bash
lake build AgenticConjectures.OeisA242560
python3 problems/oeis-a242560/a242560_certificate.py --limit 400
```

On the 2026-08-12 development run, the certificate completed in under one
second. Repository CI also rebuilds the theorem, audits its axioms, and reruns
the certificate.
