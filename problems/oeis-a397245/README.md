**English** | [한국어](README.ko.md)

# OEIS A397245

We prove the two mod 3 if-and-only-if conjectures of
[OEIS A397245](https://oeis.org/A397245). \(A(x)=\sum_{n\ge0}a_nx^n\),
with \(a_0=a_1=1\), is defined by

\[
A(x)=\exp\!\left(
x+\sum_{n\ge2}\frac{(4n^2-1)a_n}{4n^2}x^n
\right).
\]

## Results

For all \(n\ge0\) the following complete classification holds.

- \(a_n\equiv1\pmod3\) if and only if
  \(n+2=3^j\) or \(n+2=2\cdot3^j\).
- \(a_n\equiv2\pmod3\) if and only if
  \(n+2=3^i+3^j\) with \(0\le i<j\).
- In all other cases \(a_n\equiv0\pmod3\).

The proof first establishes \(a_n/n\in\mathbb Z\) via a triangular
recurrence, then proves in \(\mathbb F_3[[x]]\) that

\[
A(x)\equiv\frac{T+T^2-x}{x^2},\qquad
T=\sum_{j\ge0}x^{3^j}
\]

and reads off the coefficients in base 3.

## Documents and certificates

- [Detailed proof](PROOF.md)
- [Verification and reproduction record](VERIFICATION.md)
- [Canonical certificate](a397245_certificate.py)
- [Initial v1 certificate](legacy/a397245_certificate.py)

The certificate at the root, which incorporates the follow-up audit, is
canonical. This certificate uses [SymPy](https://www.sympy.org/); the
initial certificate is left as is for reproducibility and to preserve
the change history.

    python3 -m py_compile problems/oeis-a397245/a397245_certificate.py
    python3 problems/oeis-a397245/a397245_certificate.py

## Research status

As of 2026-08-11 the OEIS Comments section marked both if-and-only-if
statements as "Conjecture". The record from that time — that searches of
the public web and arXiv by the exact wording, the initial terms, and
the key closed form did not find the same proof — is not a confirmation
of novelty. This proof has not yet undergone peer review or confirmation
by the OEIS editors.
