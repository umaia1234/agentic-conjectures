**English** | [한국어](README.ko.md)

# OEIS A384162: counterexample at n = 2

## Verdict

The conjectured formula on [OEIS A384162](https://oeis.org/A384162),

\[
a(n)=n\,A342168(n-1),
\]

is **false already at \(n=2\)**.  The A384162 entry itself gives
\(a(2)=6\), both in its data and by listing the six marked words.  Meanwhile
[OEIS A342168](https://oeis.org/A342168) defines

\[
A342168(m)=U_m\!\left(\frac{m+3}{2}\right),
\]

so \(A342168(1)=U_1(2)=4\).  Consequently the conjectured right-hand side is

\[
2\,A342168(1)=2\cdot4=8\ne6=a(2).
\]

## Source and statement faithfulness

The canonical entries were checked on 2026-08-12.  A384162 revision 8
(last modified 2025-05-27) has offset 1 and labels the displayed identity
as a conjecture.  A342168 revision 32 (last modified 2024-06-28) has offset
0.  Thus `n-1` is the literal A342168 index; there is no hidden offset
conversion or boundary case in the counterexample.

The Lean module uses two other formulas printed in those same entries.
For A384162, the rational generating function is

\[
\frac{nx}{1-x(1-x+n)}=\frac{nx}{1-(n+1)x+x^2},
\]

whose coefficients satisfy \(c_0=0\), \(c_1=n\), and
\(c_{k+2}=(n+1)c_{k+1}-c_k\).  For A342168, Lean uses the published finite
binomial sum.  Integer coefficients are used for the first recurrence, so
natural-number subtraction cannot change its meaning.  The Python
certificate deliberately follows different definitions: it enumerates the
marked words and evaluates the Chebyshev recurrence.

The algebra also points to a likely one-digit cross-reference typo, although
that diagnosis is not needed for the refutation.  Coefficient extraction gives

\[
a(n)=n\,U_{n-1}\!\left(\frac{n+1}{2}\right).
\]

[OEIS A342167](https://oeis.org/A342167), rather than A342168, is defined by
\(A342167(m)=U_m((m+2)/2)\).  Substituting \(m=n-1\) therefore produces the
matching expression \(n\,A342167(n-1)\).

## Machine verification

[`a384162_certificate.py`](a384162_certificate.py) uses only the Python
standard library.  It independently obtains each value twice:

- \(A384162(2)=6\) by exhaustive marked-word enumeration and by the rational
  generating-function recurrence;
- \(A342168(1)=4\) by the Chebyshev recurrence and by the finite binomial sum.

Run from the repository root:

```bash
python3 problems/oeis-a384162/a384162_certificate.py
lake build AgenticConjectures.OeisA384162
```

On the 2026-08-12 verification machine, the certificate took 0.01 seconds
and the first targeted Lean build took 5.5 seconds with the mathlib cache
already installed.

The theorem
`AgenticConjectures.OeisA384162.oeis_a384162_conjecture_false` proves the
negation of the universal formula in Lean 4 without `sorry`, extra axioms, or
`native_decide`.

## Prior-art and submission status

On 2026-08-12, searches by both sequence identifiers and by the exact formula
found the canonical OEIS data/program mirrors but no public correction,
proof, or counterexample on the OEIS entries, the public web, arXiv, GitHub
code, or GitHub issues.  This negative search is not evidence of novelty.
The result is unreviewed, no novelty is claimed, and nothing has been
submitted to OEIS or any other external venue.
