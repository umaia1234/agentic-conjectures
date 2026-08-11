**English** | [한국어](README.ko.md)

# OEIS A190363

## Verdict

The following 21-term constant-coefficient recurrence proposed on the OEIS
is **false**.

\[
a(n)=2n+\left\lfloor\frac{n\sqrt5}{2}\right\rfloor+\left\lfloor\frac n4\right\rfloor,
\qquad
a(n+21)=a(n+17)+a(n+4)-a(n).
\]

The first failing base index is \(n=140\), i.e. the first failing output
term is \(a(161)\). Indeed,

\[
a(157)+a(144)-a(140)=541\ne542=a(161).
\]

Furthermore, a Pell equation generates infinitely many failure indices, so
this recurrence does not hold permanently beyond any index. The detailed
minimality certification and the infinite family of counterexamples are in
[PROOF.md](PROOF.md).

## Status of the original entry and scope of the result

- In [OEIS A190363](https://oeis.org/A190363) revision #14, checked on
  2026-08-11, this recurrence was marked as a `Conjecture` dated 2025-01-28.
- At that time the [official b-file](https://oeis.org/A190363/b190363.txt)
  provided \(n=1,\ldots,10000\). The four relevant values of the b-file
  agree with the counterexample here, but we do not interpret the b-file
  length as the intended range of validity of the original claim.
- No public counterexample or proof matching this result was found at the
  time on the public web, arXiv, mathematics Q&A sites, SeqFan, or GitHub,
  but this is only a negative search result. Since it has not yet undergone
  peer review or OEIS submission, we do not assert novelty.

## Reproduction

[`a190363_certificate.py`](a190363_certificate.py) uses only the Python
standard library and, without any floating-point approximation, checks the
following via `math.isqrt` and integer square comparisons.

- That the defects are all 0 for \(1\le n\le139\) and that \(D(140)=1\);
- The shift-17 margin used for minimality and the square certifications of
  the four terms;
- The Pell invariant and the first eight Pell-generated counterexamples.

Run from the repository root.

```bash
python3 problems/oeis-a190363/a190363_certificate.py
```

The SHA-256 of the file at the time of the 2026-08-11 re-check was as
follows.

```text
0cd6f96307f4c0ceb007ec14ff813ba6443c4163328ded3a2df384d55038979e  problems/oeis-a190363/a190363_certificate.py
```

At that time it passed `python3 -m py_compile` and the runtime was about
0.00 seconds.

## Upstream Lean formalization

The FormalConjectures [original snapshot and provenance record](upstream/README.md)
is preserved in [`190363_e4edee15.lean`](upstream/190363_e4edee15.lean). Its
`by sorry` theorem is a **conjecture statement** recording the proposed
recurrence, not a formal proof. This folder disproves that statement via the
first failure and the infinite family of counterexamples.

## Lean formal disproof in this repository

In [`AgenticConjectures/OeisA190363.lean`](../../AgenticConjectures/OeisA190363.lean),
which copies the upstream definitions verbatim, the negation of exactly that
statement

```
oeis_190363_conjecture_0_false : ¬ A190363_LR.IsSolution (fun n => (a (n + 1) : ℤ))
```

is proved without `sorry`. The first failure at solution index 139
(= OEIS base index 140), `542 ≠ -471 + 484 + 528 = 541`, is evaluated via
four exact integer square sandwiches. CI re-verifies `lake build`, the
no-sorry gate, and the axiom audit (standard 3 axioms only).
