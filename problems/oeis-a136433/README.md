**English** | [한국어](README.ko.md)

# OEIS A136433

We derive a 9-lag constant-coefficient linear recurrence from the
periodic-coefficient non-autonomous recurrence of
[OEIS A136433](https://oeis.org/A136433). The sequence is defined by \(a_1=11\) and

\[
a_{n+2}=((n\bmod3)+1)a_{n+1}+((n\bmod2)+1)
\qquad(n\ge0).
\]

## Result

For all \(n\ge10\),

\[
a_n=6a_{n-3}+a_{n-6}-6a_{n-9}
\]

holds. The key fact is that the three-step transition is
\(a_{t+3}=6a_t+B_t\) and the constant term \(B_t\) has period 6.
The values over one period are \((13,9,7,17,6,8)\).

## Documents and certificate

- [Detailed proof](PROOF.md)
- [Verification and reproduction record](VERIFICATION.md)
- [Executable certificate](a136433_certificate.py)

It can be re-checked from the repository root as follows.

    python3 -m py_compile problems/oeis-a136433/a136433_certificate.py
    python3 problems/oeis-a136433/a136433_certificate.py

## Research status

As of 2026-08-11, the OEIS entry marked this formula as a "Conjecture".
Since the constant-coefficient recurrence itself has appeared in the OEIS
"LinearRecurrence" computation code since 2013, the contribution preserved
here is not the discovery of the formula but a universal proof that it holds
for all \(n\ge10\) starting from the original non-autonomous recurrence.
The record that a public search did not find the same proof is not a
confirmation of novelty, and it has not yet undergone peer review or
confirmation by an OEIS editor.

## Lean formal proof

[`AgenticConjectures/OeisA136433.lean`](../../AgenticConjectures/OeisA136433.lean)
proves this universal statement in mathlib-based Lean 4 without `sorry`:

```
a136433_order9 : ∀ n, 10 ≤ n → (a n : ℤ) = 6 * a (n-3) + a (n-6) - 6 * a (n-9)
```

Since this entry has no upstream Lean snapshot, the faithfulness caveats for
the sequence definition itself (offset, recurrence index convention, non-use
of `a 0`) are recorded in the module docstring. CI re-verifies `lake build`,
the no-sorry gate, and the axiom audit.
