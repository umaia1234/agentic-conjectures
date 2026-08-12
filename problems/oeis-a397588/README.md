**English** | [한국어](README.ko.md)

# OEIS A397588 — parity conjecture

[OEIS A397588](https://oeis.org/A397588) defines a sequence by

\[
a(1)=1,\qquad
a(n)=(n+1)\sum_{k=1}^{n-1}a(k)a(n-k)\quad(n>1).
\]

The entry's original claim is:

> Conjecture: a(n) is odd iff n is a power of 2 for n >= 1.

## Result

The conjecture is true. For every integer \(n\geq1\),

\[
a(n)\text{ is odd}\quad\Longleftrightarrow\quad n=2^r
\text{ for some }r\geq0.
\]

## Proof

Work modulo 2. If \(n>1\) is odd, then the factor \(n+1\) in the
recurrence is even, so \(a(n)\) is even.

Now let \(n=2m\). In the convolution sum, the involution
\(k\mapsto2m-k\) pairs every summand except the midpoint \(k=m\).
Each pair contributes twice the same product and therefore vanishes modulo
2. The only surviving summand is \(a(m)^2\). Since \(2m+1\) is odd,

\[
a(2m)\equiv a(m)^2\equiv a(m)\pmod2. \tag{1}
\]

Repeatedly applying (1) removes every factor of 2 from the index. If
\(n\) is a power of two, this process reaches \(a(1)=1\), so \(a(n)\)
is odd. Otherwise it reaches an odd index greater than 1, whose term is
even by the first paragraph. This proves both directions.

## Lean verification

[`AgenticConjectures/OeisA397588.lean`](../../AgenticConjectures/OeisA397588.lean)
formalizes the recurrence for an arbitrary function `a : ℕ → ℕ` and proves
the stronger universal theorem

```text
statement :=
  ∀ a, SatisfiesRecurrence a →
    ∀ n, 0 < n → (Odd (a n) ↔ ∃ r, n = 2 ^ r)

odd_iff_power_of_two : statement
```

The convolution cancellation is checked by a finite-sum involution in
`ZMod 2`; no computed term table is trusted. From the repository root,
reproduce the module check with:

```bash
lake env lean AgenticConjectures/OeisA397588.lean
```

The full repository gates also compile this module, reject `sorry` and
nonstandard axioms, and regenerate the dashboard. The standalone command took
41.99 seconds on the local verification machine.

## Statement faithfulness and research status

The formalization uses the second recurrence printed on the OEIS entry,
with `Finset.Icc 1 (n - 1)` representing exactly
\(k=1,\ldots,n-1\) when \(n>1\). It does
not formalize the generating-function equation
\(A(x)=x+(xA(x)^2)'\). Extracting coefficients from that equation gives
the displayed recurrence, as the OEIS entry records, but that derivation is
documented here rather than checked in Lean. The offset is 1, \(n=0\) is
excluded, and natural-number subtraction `n-k` is used only where
\(1\leq k<n\).

The source was checked at revision 18 on 2026-08-12. It still labeled the
parity statement a conjecture and linked only the term table. Targeted
searches for the exact claim, recurrence, functional equation, initial
terms, and repository formalizations found no public proof. That negative
search is not a literature review or evidence of novelty. This proof is
unreviewed, makes no priority claim, and has not been submitted to OEIS.
