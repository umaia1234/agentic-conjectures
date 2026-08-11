**English** | [한국어](README.ko.md)

# OEIS A340881

We resolve the two modular periodicity conjectures of
[OEIS A340881](https://oeis.org/A340881) for every modulus \(m\ge2\). The
sequence is defined by

\[
A(n)=\sum_{k=0}^{n-1}2^{k(k+1)/2}
       \prod_{j=k+1}^{n-1}(2^j-1),\qquad n\ge1.
\]

## Results

- For odd \(m>1\) and \(L=\operatorname{ord}_m(2)\),
  \(A(n+2L)\equiv A(n)\pmod m\) holds for all \(n\ge1\).
  That is, we obtain an explicit period starting from the beginning, even
  for odd composite moduli.
- For a prime \(p\), the minimal period divides \(2(p-1)\). For \(p=2\),
  \(A(n)\equiv1\pmod2\).
- Writing \(m=2^eu\) with \(u\) odd, we obtain eventual periodicity for
  every \(m\ge2\). When \(u>1\), \(2\operatorname{ord}_u(2)\) is a period
  for \(n\ge\max(1,e)\), and when \(u=1\), period 2 holds for
  \(n\ge e\).

## Documents and certificate

- [Detailed proof](PROOF.md)
- [Verification and reproduction record](VERIFICATION.md)
- [Executable certificate](a340881_certificate.py)

It can be re-checked from the repository root as follows.

    python3 -m py_compile problems/oeis-a340881/a340881_certificate.py
    python3 problems/oeis-a340881/a340881_certificate.py

## Research status

As of 2026-08-11, the OEIS entry marked both statements as a "Conjecture".
The audit record from that time is that the public web, arXiv, and GitHub
were checked against the exact formula, initial terms, and key period
expressions, and no identical public proof was found. This is only a
negative search result, and this proof has not yet undergone peer review or
confirmation by an OEIS editor.

## Upstream Lean formalization

The FormalConjectures [original snapshot and provenance record](upstream/README.md)
is preserved in [`340881_294a5574.lean`](upstream/340881_294a5574.lean).
The theorem recording the period for prime moduli is a `by sorry`
**conjecture statement**, not a formal proof. The stronger result of this
folder for all moduli is not formalized in that Lean snapshot.
