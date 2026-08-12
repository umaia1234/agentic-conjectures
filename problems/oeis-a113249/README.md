**English** | [한국어](README.ko.md)

# OEIS A113249 — odd terms in the full parameter family are squares

## Source statement

[OEIS A113249](https://oeis.org/A113249),
[revision #29](https://oeis.org/history/view?seq=A113249&v=29), defines the
fourth-order family

\[
a_m(r)=m^4a_m(r-4)+(2m)^2a_m(r-3)-4a_m(r-1) \qquad (r\ge4)
\]

from

\[
\begin{aligned}
a_m(0)&=-1, & a_m(1)&=4,\\
a_m(2)&=-13+6(m-1)+3(m-1)^2, &
a_m(3)&=(-8+m^2)^2.
\end{aligned}
\]

Its exact comment is:

> Conjecture: a(m, 2*n+1) is a perfect square for all m, n.

The entry itself is the $m=3$ row of the family and has offset 0.

## Result

The conjecture holds. More strongly, for every integer parameter $m$ and
every $n ≥ 0$, define

\[
Y_m(0)=2,\qquad Y_m(1)=8-m^2,\qquad
Y_m(n+2)=4Y_m(n+1)-m^2Y_m(n).
\]

Then

\[
\boxed{a_m(2n+1)=Y_m(n)^2.}
\]

The theorem
[`odd_term_eq_aux_square`](../../AgenticConjectures/OeisA113249.lean)
proves this identity in Lean 4 for all $m ∈ ℤ$. The registered theorem
`oeis_a113249_conjecture` gives the natural-parameter interpretation of the
source and supplies an explicit integer square root. Both proofs contain no
`sorry`, extra axiom, or `native_decide`.

## Proof

Write the source recurrence in zero form:

\[
R_k:
a_m(k+4)+4a_m(k+3)-4m^2a_m(k+1)-m^4a_m(k)=0.
\]

The linear combination $R_{k+2}-4R_{k+1}+m^2R_k$ eliminates the odd
shifts and gives the step-six relation

\[
\begin{aligned}
a_m(k+6)={}&(16-m^2)a_m(k+4)
 +m^2(m^2-16)a_m(k+2)+m^6a_m(k).
\end{aligned}
\]

The squares of the auxiliary sequence obey exactly the same relation. If
$A=Y_m(n+1)$ and $B=Y_m(n)$, a polynomial identity verified by Lean's
`ring` tactic is

\[
\begin{aligned}
\bigl(4(4A-m^2B)-m^2A\bigr)^2
={}&(16-m^2)(4A-m^2B)^2\\
&+m^2(m^2-16)A^2+m^6B^2.
\end{aligned}
\]

Direct expansion of the source initial values gives

\[
a_m(1)=Y_m(0)^2,\qquad
a_m(3)=Y_m(1)^2,\qquad
a_m(5)=Y_m(2)^2.
\]

A three-term-window induction using the common recurrence proves the boxed
identity for every $n$.

## Statement faithfulness

- The Lean definition copies all four initial values and the source
  recurrence, shifted forward to index `n+4`; it never uses truncated natural
  subtraction.
- Sequence values and the general parameter are represented in `ℤ` because
  the family has negative even-indexed terms. OEIS does not explicitly state
  the domains of “all m, n”; the registered natural-parameter interpretation
  quantifies over `m n : ℕ` and casts `m` to `ℤ`. The closed-form theorem is
  stronger and permits negative integer parameters too.
- The source suppresses the parameter on some right-hand-side occurrences of
  `a`; the formalization consistently reads them as terms in the same fixed
  $m$-row, which is the only recurrence interpretation compatible with the
  listed rows.
- The source expression for $a_m(2)$ simplifies to $3m^2-16$, but the Lean
  definition keeps the displayed expression verbatim.
- `IsSquare` is witnessed in `ℤ`. Since the theorem identifies each odd term
  with an integer square, it also proves those terms are nonnegative.
- There is no Formal Conjectures snapshot for the full A113249 family. The
  canonical OEIS statement was checked directly on August 12, 2026.

## Independent finite check

[`a113249_certificate.py`](a113249_certificate.py) uses only Python's standard
library and contains two separate exact-integer implementations:

1. the source fourth-order recurrence; and
2. the auxiliary second-order recurrence.

It checks the 29 terms published for the $m=3$ row, then compares 2,091 odd
terms for every integer parameter $-25 ≤ m ≤ 25$. This finite check is only
a sanity check; the Lean theorem proves the unbounded claim.

From the repository root, run:

```bash
python3 problems/oeis-a113249/a113249_certificate.py
lake env lean AgenticConjectures/OeisA113249.lean
```

The certificate took about 0.07 seconds and the direct Lean module check
took about 24 seconds on the development machine. The certificate SHA-256 is:

```text
dd44727de17d1debc92a980cf2985f48c3cca37e4b3f6098e8ce87a1b5007590  problems/oeis-a113249/a113249_certificate.py
```

## Prior art and scope

This result deliberately generalizes known special cases.

- A113249 gives Robert Israel's 2017 formula
  $a_3(2n+1)=b(n)^2$, with $b(n)=4b(n-1)-9b(n-2)$.
- [OEIS A113254](https://oeis.org/A113254) links a public
  [AlphaProof Nexus Lean proof](https://github.com/google-deepmind/alphaproof-nexus-results/blob/42f344cfa9d57154f36e6b9bef1f71760a438c54/APNOutputs/OEIS/oeis_113254_conjecture_0.lean)
  for $m=8$. That proof introduced an auxiliary second-order recurrence and
  a three-term-window induction. The proof here follows that published
  architecture while keeping $m$ symbolic and proving the entire family.

As of August 12, 2026, A113249 revision #29 still labels the all-parameter
claim a conjecture. Exact-statement searches of the public web, arXiv,
GitHub, Formal Conjectures, and the cited OEIS material found no general proof,
but that negative search does not establish novelty. This formalization is
unreviewed, claims no priority, and has not been submitted to OEIS or any
other external venue.
