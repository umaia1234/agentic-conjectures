**English** | [한국어](README.ko.md)

# OEIS A396093: both parity conjectures

## Verdict

Let \(A(x)=\sum_{n\geq 0}a(n)x^n\) be the generating function in
[OEIS A396093](https://oeis.org/A396093), defined by

\[
A(x)=B(B(B(x))), \qquad B(x)=\frac{x}{(1-x)^2}.
\]

Both parity conjectures on the entry are **true**:

1. \(a(2n)\) is even for every \(n\geq 1\).
2. For \(n\geq 1\), \(a(2n-1)\) is even if and only if
   \(n=5k-2\) for some \(k\geq 1\).

In fact, the Lean proof establishes the stronger complete classification

\[
a(n)\text{ is even}
\quad\Longleftrightarrow\quad
n\text{ is even or }n\equiv 5\pmod {10}.
\]

## Proof

The OEIS entry gives the rational form

\[
A(x)=
\frac{x(1-x)^2(1-3x+x^2)^2}
     {(1-7x+13x^2-7x^3+x^4)^2}.
\]

Reduce it over \(\mathbf F_2[[x]]\). The numerator and denominator become

\[
N(x)=x(1+x^6), \qquad
D(x)=1+x^2+x^4+x^6+x^8.
\]

Since

\[
(1+x^2)D(x)=1+x^{10},
\]

and all denominators here have constant coefficient one, formal division is
valid and gives

\[
A(x)=\frac{x(1+x^2)(1+x^6)}{1+x^{10}}
    =(x+x^3+x^7+x^9)\sum_{j\geq 0}x^{10j}
    \quad\text{in }\mathbf F_2[[x]].
\]

Thus \(a(n)\) is odd exactly for
\(n\equiv 1,3,7,9\pmod {10}\). This excludes every even index. At an odd
index \(2n-1\), evenness is equivalent to
\(2n-1\equiv 5\pmod {10}\), or \(n\equiv 3\pmod 5\), which is precisely
\(n=5k-2\) with \(k\geq 1\).

## Lean formalization and statement faithfulness

[`AgenticConjectures/OeisA396093.lean`](../../AgenticConjectures/OeisA396093.lean)
copies the entry's initial values \(a(0),\ldots,a(7)\) and its published
order-eight recurrence over \(\mathbb Z\). Reducing the recurrence modulo two
gives

\[
a(n+8)\equiv a(n+6)+a(n+4)+a(n+2)+a(n)\pmod 2.
\]

Using this formula at \(n\) and \(n+2\) proves
\(a(n+10)\equiv a(n)\pmod 2\). A strong induction from the first ten values
then proves the complete classification above and both source statements.

The entry has offset 0 and explicitly prepends \(a(0)=0\); the Lean definition
does the same. Integer-valued recurrence terms are represented in \(\mathbb Z\),
so natural-number subtraction cannot alter them. The first theorem is slightly
stronger than the source because it includes \(n=0\). The hypotheses
\(n,k\geq 1\) make the natural-number expressions `2*n - 1` and
`5*k - 2` identical to their ordinary integer meanings. The formalized
claim was checked directly against the canonical OEIS entry; there was no
A396093 snapshot in the pinned Formal Conjectures sources.

The audited theorems are:

- `AgenticConjectures.OeisA396093.even_a_iff`;
- `AgenticConjectures.OeisA396093.even_index_even`;
- `AgenticConjectures.OeisA396093.odd_index_even_iff`.

They compile without `sorry`, extra axioms, or `native_decide`.

## Independent certificate

[`a396093_certificate.py`](a396093_certificate.py) uses only the Python
standard library and follows the generating-function route independently of
the Lean recurrence proof. It:

- composes \(B(x)=x/(1-x)^2\) three times by exact polynomial arithmetic;
- recovers the displayed rational function and the recurrence signature
  \((14,-75,196,-269,196,-75,14,-1)\);
- checks all 27 terms printed on the entry and the independent published
  double-sum formula through \(n=30\);
- verifies the cross-multiplied polynomial identity over \(\mathbf F_2\) that
  proves the infinite period-10 parity pattern; and
- regression-checks 501 exact recurrence terms.

Run from the repository root:

```bash
python3 problems/oeis-a396093/a396093_certificate.py
lake build AgenticConjectures.OeisA396093
```

On the 2026-08-12 verification machine, the certificate took about 0.04
seconds. The first direct Lean compilation in an isolated linked worktree took
about 44 seconds while sharing the installed mathlib cache.

## Source history, prior art, and external status

The [entry history](https://oeis.org/history?seq=A396093) was checked on
2026-08-12. Paul D. Hanna authored the sequence in May 2026; both conjectures
were added in history revision 3 on May 19. The zero term and offset 0 were
added on May 20, as was the constant recurrence. The latest content revision
shown in the history was revision 31 on May 28, and the live entry still
labelled both statements as conjectures.

Searches by the sequence identifier, exact conjecture text, rational
denominator, and initial terms found the OEIS material and program
implementations, but no proof or duplicate result on OEIS, arXiv, GitHub, or
the public web. The older [OEIS A166482](https://oeis.org/A166482) generating
function gives another short route to the same parity pattern, but no public
parity proof was found there either. This negative search is not evidence of
novelty. The result is unreviewed, no novelty is claimed, and nothing has been
submitted to OEIS or any other external venue.
