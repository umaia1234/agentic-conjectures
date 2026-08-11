**English** | [한국어](README.ko.md)

# OEIS A060841

## Verdict

\[
R_n:=\frac1{\det M_n}
=\prod_{k=1}^n\frac{k^2}{\varphi(k)}
=\frac{(n!)^2}{\prod_{k=1}^n\varphi(k)}.
\]

The verdicts on the two conjectures recorded together on OEIS are as
follows.

1. **The integrality conjecture is true.** Exactly
   \[
   R_n\in\mathbb Z\iff n\in\{1,2,\ldots,34,36,38\}.
   \]
2. **The conjecture that every reduced denominator is a power of 2 is
   false.** The first index at which an odd prime appears in the
   denominator is \(n=1807\), and
   \[
   \operatorname{den}(R_{1807})=2^{2342}\cdot3.
   \]

The 2-adic bound closing every \(n\ge91\), the finite certification for
\(n\le90\), and two independent computations of the smallest odd
denominator are collected in [PROOF.md](PROOF.md). The second result
also refutes the claim on the related
[OEIS A260897](https://oeis.org/A260897) that "every term is a power of
2".

## Status of the source and scope of the results

- In [OEIS A060841](https://oeis.org/A060841) revision #37, checked on
  2026-08-11, both statements remained as a `Conjecture` dated
  2015-08-02.
- At that time the [official b-file](https://oeis.org/A060841/b060841.txt)
  provided the numerator values for \(n=1,\ldots,400\). We do not
  interpret this term count as the range of the conjecture or as the
  exhaustive-search bound used here.
- The integrality classification is a global result combining a proof
  for \(n\ge91\) with exact certification for \(n\le90\). The smallest
  odd denominator is checked exactly for \(n\le1807\).
- The same public counterexample and proof could not be found on the
  open web, arXiv, math Q&A sites, SeqFan, or GitHub at the time, but
  this is only a negative search result. Since it has not yet gone
  through peer review or an OEIS submission, we do not assert novelty.

## Reproduction

[`a060841_certificate.py`](a060841_certificate.py) uses only the Python
standard library and runs both of the following
two independent paths.

- accumulate and reduce \(R_n\) directly with `fractions.Fraction`;
- accumulate \(v_q(R_n)\) as an integer for each prime \(q\).

Both paths determine the first odd denominator to be
\((n,q)=(1807,3)\). Run from the repository root.

```bash
python3 problems/oeis-a060841/a060841_certificate.py
```

At the recheck on 2026-08-11, the SHA-256 of the file was as follows.

```text
82364fbe79c32c30009ce3193aefc0a1be6e824682cf236e7de80f75ac507464  problems/oeis-a060841/a060841_certificate.py
```

At that time it passed `python3 -m py_compile` and the run time was
about 0.46 seconds.

## Upstream Lean formalization

The FormalConjectures [original snapshot and provenance record](upstream/README.md)
is preserved in [`60841_4cba886e.lean`](upstream/60841_4cba886e.lean). The
`by sorry` theorem in that file is a **statement** recording the two OEIS
conjectures together, not a formal proof. Here we prove the integrality
classification while refuting the denominator statement with `n=1807`.
