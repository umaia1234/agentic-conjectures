**English** | [한국어](README.ko.md)

# OEIS A368633 — parity conjecture

## Verdict

The conjecture is true: if

\[
A(x)=\sum_{n\geq 0}a_nx^n
\quad\text{and}\quad
A(x)=1+2xA(x)^2-xA(-x)^2,
\]

then

\[
a_n\text{ is odd}\quad\Longleftrightarrow\quad
n+1\text{ is a power of }2.
\]

The exact OEIS conjecture is:

> “Conjecture: a(n) is odd when n = 2^k - 1 for k >= 0 and even elsewhere.”

This was checked against canonical [OEIS A368633](https://oeis.org/A368633),
revision 26, on 2026-08-12. The entry has offset 0.

## Proof

Let

\[
b_m=[x^m]A(x)^2=\sum_{i=0}^{m}a_i a_{m-i}.
\]

Every summand contributing to \([x^m]A(-x)^2\) has total sign
\((-1)^{i+m-i}=(-1)^m\), so

\[
[x^m]A(-x)^2=(-1)^m b_m.
\]

The constant coefficient is \(a_0=1\). For \(n\geq1\), coefficient
comparison in the defining equation gives the exact recurrence

\[
a_n=\bigl(2-(-1)^{n-1}\bigr)
    \sum_{i=0}^{n-1}a_i a_{n-1-i}
=
\begin{cases}
\displaystyle\sum_{i=0}^{n-1}a_i a_{n-1-i},&n\text{ odd},\\[6pt]
\displaystyle3\sum_{i=0}^{n-1}a_i a_{n-1-i},&n\text{ even}.
\end{cases}
\]

This recurrence also proves that the formal power series solution is unique.
Both possible multipliers are odd. Thus, writing \(p_n=a_n\bmod2\),

\[
p_0=1,
\qquad
p_n=\sum_{i=0}^{n-1}p_i p_{n-1-i}\pmod2.
\]

This is the Catalan recurrence modulo 2. There is also a short direct
classification. If \(n>0\) is even, all terms pair as \(i\leftrightarrow
n-1-i\), so \(p_n=0\). If \(n=2r+1\), those pairs again cancel except for
the middle term, and \(p_{2r+1}=p_r^2=p_r\). Consequently

\[
p_n=1
\Longleftrightarrow
n=2r+1\text{ and }p_r=1
\Longleftrightarrow
n=2^k-1
\]

by induction, including \(p_0=1\) for \(k=0\). Equivalently, \(n+1\) is a
power of 2.

This is precisely the classical parity classification of the Catalan
numbers ([OEIS A000108](https://oeis.org/A000108)). The argument is a direct
reduction to that standard result, so we make no novelty or priority claim.

## Machine verification

[`a368633_certificate.py`](a368633_certificate.py) uses only the Python
standard library. It independently constructs the coefficients from the two
signed Cauchy products in the functional equation and from the simplified
exact recurrence above. It then:

- checks that the two constructions agree through \(n=600\);
- checks all 25 values in the canonical OEIS JSON `data` field, exactly as
  published for \(n=0,\ldots,24\); and
- checks through \(n=600\) that coefficient parity agrees both with the
  independent Catalan closed form
  \(C_n=\binom{2n}{n}/(n+1)\) and with the power-of-two classification.

Run from the repository root:

```bash
python3 problems/oeis-a368633/a368633_certificate.py
```

On 2026-08-12 repeated runs completed in 0.3–0.7 seconds. The finite check
supports the implementation and source transcription; the all-\(n\) claim is
supplied by the proof above and the Lean theorem.

## Statement faithfulness and Lean scope

The Lean definition directly encodes the displayed equation over integer
formal power series, using `PowerSeries.rescale (-1) A` for \(A(-x)\). The
theorem quantifies over every integer formal power series satisfying that
equation, so it applies to the OEIS sequence and is slightly stronger than the
source's nonnegative-coefficient formulation. It uses the equivalent
subtraction-free condition \(n+1=2^k\) for some natural \(k\). Hence there is
no discrepancy from the OEIS offset-0 phrase \(n=2^k-1\), and no boundary or
natural-subtraction case is lost. “Odd” is integer oddness.

This problem was harvested directly from OEIS. There is no upstream Lean
snapshot in this problem directory; the formalization is new and is audited
against the canonical OEIS statement above.
