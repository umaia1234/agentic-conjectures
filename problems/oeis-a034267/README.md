**English** | [한국어](README.ko.md)

# OEIS A034267 — D-finite recurrence

## Source statement

[OEIS A034267](https://oeis.org/A034267) has offset 0 and is the diagonal
`f(n,n)` of [OEIS A034261](https://oeis.org/A034261), where

\[
f(m,k)=\binom{m+k}{k+1}\frac{mk+m+1}{k+2}.
\]

Its Formula section records Mathar's February 10, 2025 proposal as
“Conjecture D-finite with recurrence”:

\[
-(n+2)(11n-7)a_n
+2(23n^2+44n+30)a_{n-1}
-4(n+5)(2n-3)a_{n-2}=0.
\]

The source does not state a range. Since the sequence begins at index 0 and
the recurrence uses `a(n-2)`, the minimal meaningful range is \(n\ge2\).

## Result

The recurrence holds for every \(n\ge2\). In particular, the closed form
displayed on the same OEIS page,

\[
a_n=\binom{2n}{n+1}\frac{n^2+n+1}{n+2},
\]

satisfies the proposed identity throughout its meaningful range. This is
proved in mathlib-based Lean 4 by
[`a034267_recurrence`](../../AgenticConjectures/OeisA034267.lean), without
unproved placeholders or non-kernel computation.

## Proof idea

Write \(c_n=\binom{2n}{n+1}\). For \(n\ge2\), adjacent binomial coefficients
satisfy

\[
\frac{c_n}{c_{n-1}}
=\frac{2n(2n-1)}{(n-1)(n+1)}.
\]

Substituting this relation and the closed form for the three consecutive
terms reduces the claimed recurrence to a polynomial identity. The Lean
proof checks the boundary \(n=2\) directly. For \(n\ge3\), it rewrites the
three binomial coefficients as factorial quotients, expands them relative to
common factorial factors, clears the nonzero denominators, and lets `ring`
verify the remaining identity.

The module also defines the two-variable source formula and proves
`a_eq_f_diag`, tying the closed form used by the proof directly to the
A034261 diagonal definition.

## Statement faithfulness

- The theorem uses the inferred minimal range \(n\ge2\); \(n=0,1\) would
  require negative sequence indices in the source recurrence.
- Values and coefficients live in \(\mathbb Q\), so division and expressions
  such as \(2n-3\) have their ordinary mathematical meanings. Natural-number
  subtraction is used only for the guarded indices `n-1` and `n-2`.
- This formalization does not separately prove that the rational closed form
  is integral for every \(n\). Integrality is not needed to prove the equality,
  and the initial terms agree with the OEIS integer sequence.
- There is no Formal Conjectures Lean snapshot for this entry; the definitions
  and quotation were checked directly against OEIS revision #23, dated
  September 4, 2025, on August 12, 2026.

## Reproduction

From the repository root:

```bash
lake env lean AgenticConjectures/OeisA034267.lean
lake build
python3 scripts/check_axioms.py
```

The direct module check takes about 6 seconds on the development machine.
The repository's full verification gates also rebuild this module and audit
both registered theorems.

## Research status and prior art

The two-variable formula on A034261 has been public since 2000 and is credited
there to Michael Somos, as recorded in its
[revision history](https://oeis.org/history?seq=A034261&start=30); Eldar
displayed its A034267 diagonal explicitly in September 2025. The contribution
here is only a machine-checked derivation of Mathar's stated recurrence from
that public formula, not discovery of either formula or recurrence.

As of August 12, 2026, A034267 revision #23 still called the recurrence a
conjecture. Exact-formula searches of the public web, arXiv, GitHub/Lean, and
the cited OEIS material found no independent proof. That negative search is
not evidence of novelty. This result is unreviewed, has not been confirmed by
OEIS editors, and has not been submitted externally.
