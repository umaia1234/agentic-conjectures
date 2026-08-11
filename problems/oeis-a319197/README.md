**English** | [한국어](README.ko.md)

# OEIS A319197 — `I(n,1)=1` normalization counterexample

## Result

The published terms of [OEIS A319197](https://oeis.org/A319197) refute an
explicit assertion in the entry's Formula section:

> “There are no more factors > 1 for all m >= 0 because I(n, 1) = 1.”

The entry defines

\[
I(n;m)=\frac{F(2^{n-2}\,3m)}
 {2^n\prod_{j=3}^{n}a(j)}
\]

and lists

\[
(a(3),a(4),a(5),a(6),a(7))
=(1,9,161,51841,6989569).
\]

At \(n=7,m=1\), exact integer arithmetic gives

\[
\prod_{j=3}^{7}a(j)=525039711220521,
\]

\[
2^7\prod_{j=3}^{7}a(j)=67205083036226688,
\qquad
F(96)=51680708854858323072,
\]

and

\[
F(96)=769\left(2^7\prod_{j=3}^{7}a(j)\right).
\]

Therefore

\[
\boxed{I(7;1)=769\ne1}.
\]

This is a complete counterexample to the universal `I(n,1)=1` supporting
assertion. It is **not** a counterexample to the entry's separate main
conjecture that `I(n,m)` is a nonnegative integer for all `n >= 3` and
`m >= 0`: `769` is a positive integer, so that broader conjecture remains
open here.

## Source audit and prior art

- The formula and the five values above are copied from the current approved
  [OEIS entry](https://oeis.org/A319197), accessed 2026-08-12. The current
  published version is [revision 7](https://oeis.org/history/view?seq=A319197&v=7),
  approved 2018-10-25; per the public history index, the formula was
introduced in revision 2 (2018-10-09, by the author); the per-revision
diff itself sits behind an OEIS login.
- Targeted public-web searches for the sequence ID, the exact normalization
  phrase, and the value `769` found no prior correction or proof. That is only
  a negative search result. This repository does not claim novelty or priority.
- No comment, correction, or other material has been submitted to OEIS. Any
  external submission requires human approval under this repository's policy.

## Machine verification

The [Lean module](../../AgenticConjectures/OeisA319197.lean) formalizes only
the exact `n=7,m=1` instance. It proves both `I(7;1)=769` and the negation of
the claimed equality with `1` using kernel-checked `norm_num`; it uses neither
`sorry` nor `native_decide`.

The independent [Python certificate](a319197_certificate.py) uses two
different Fibonacci algorithms (linear iteration and fast doubling), checks
the source denominator and `F(96)`, and verifies exact quotient and zero
remainder. It is a finite transcription audit; the Lean theorem is the formal
refutation.

From the repository root, reproduce both checks with:

```bash
lake env lean AgenticConjectures/OeisA319197.lean
(cd problems/oeis-a319197 && python3 a319197_certificate.py)
```

Observed on the repository's CI-equivalent environment on 2026-08-12:

- direct Lean module check: 21.57 seconds;
- Python certificate: 0.06 seconds.

## Formalization correspondence

- OEIS uses offset 3; the formal counterexample uses exactly terms `a(3)`
  through `a(7)` and assigns no artificial values outside that range.
- `Nat.fib` has `F(0)=0, F(1)=1`, matching OEIS A000045.
- The source index evaluates without ambiguity as
  `2^(7-2)*3*1 = 96`. Natural subtraction cannot underflow at this literal.
- Lean's natural division introduces no rounding ambiguity for the refutation:
  the Lean theorems prove the floor-quotient value 769 (any exact `I = 1` would
  force the floor quotient to be 1), and the Python certificate independently
  checks that the denominator divides `F(96)` exactly with remainder 0.
- There is no upstream Lean snapshot for this entry.
