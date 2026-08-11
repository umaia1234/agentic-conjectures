**English** | [한국어](README.ko.md)

# OEIS A398189 — 2-adic valuation of generalized Schenker sums

[OEIS A398187](https://oeis.org/A398187) (Peter Luschny, Jul 23 2026) is the
triangle of **generalized Schenker sums**

\[
T(n,k) \;=\; \sum_{j=0}^{n-k} \frac{(n-k)!}{j!}\, n^j , \qquad 0 \le k \le n,
\]

whose column \(k=0\) is the classical Schenker sums
[A063170](https://oeis.org/A063170).
[OEIS A398189](https://oeis.org/A398189) (Peter Luschny, Jul 27 2026) is the
triangle of 2-adic valuations \(v_2(T(n,k))\), and its comment states
(retrieved 2026-08-12):

> We conjecture that:
> &nbsp;&nbsp;T(n, k) =
> &nbsp;&nbsp;&nbsp;&nbsp;= v2((n - k)!), if n is even;
> &nbsp;&nbsp;&nbsp;&nbsp;= 1, if n is odd and k = 0;
> &nbsp;&nbsp;&nbsp;&nbsp;= 0, if n is odd and k is odd;
> &nbsp;&nbsp;&nbsp;&nbsp;= v2(k + 2), if n is odd, k is even, and not k == 14 mod 16.
>
> All other cases arise when n is odd, k is even, and k == 14 mod 16. No
> simple formula is known.

## Result

**All four conjectured cases are proved, for every \(0 \le k \le n\).** In
addition, in the excluded class (\(n\) odd, \(k \equiv 14 \pmod{16}\)) the
valuation is always \(\ge 4\), which explains why no mod-16 pattern exists
there.

The proof (see [PROOF.md](PROOF.md)) uses only the recurrence
\(S_n(m+1) = (m+1) S_n(m) + n^{m+1}\) for the row polynomials
\(T(n,k) = S_n(n-k)\):

- **\(n\) even:** an ultrametric induction — the \(n^{m+1}\) term always
  has strictly larger valuation than \((m+1)S_n(m)\), because
  \(v_2((m+1)!) \le m\) (Legendre) — gives \(v_2 = v_2((n-k)!)\) exactly.
- **\(n\) odd:** all claimed valuations are \(\le 3\), and mod 16 the
  sequence \(m \mapsto S_n(m)\) is periodic with period 16 (odd residues
  satisfy \(a^4 \equiv 1 \bmod 16\), and each coefficient \(16!/j!\),
  \(j < 16\), is divisible by 16). Everything reduces to a finite table
  over the 64 odd residue pairs \((n \bmod 16, m \bmod 16)\).

## Machine verification

Lean 4 (mathlib), sorry-free, in
[`AgenticConjectures/OeisA398189.lean`](../../AgenticConjectures/OeisA398189.lean):

| Theorem | Statement |
|---|---|
| `valuation_even` | \(n\) even → \(v_2(T(n,k)) = v_2((n-k)!)\) (all \(k\)) |
| `valuation_odd_k0` | \(n\) odd → \(v_2(T(n,0)) = 1\) |
| `valuation_odd_odd` | \(n\), \(k\) odd → \(v_2(T(n,k)) = 0\) |
| `valuation_odd_even` | \(n\) odd, \(k\) even, \(k \le n\), \(k \not\equiv 14 \,(16)\) → \(v_2(T(n,k)) = v_2(k+2)\) |
| `sixteen_dvd_excluded` | \(n\) odd, \(k \le n\), \(k \equiv 14 \,(16)\) → \(16 \mid T(n,k)\) |
| `T_eq_oeis_form` | the Lean `T` equals the literal OEIS sum \(\sum_j (n-k)!/j! \cdot n^j\) |

The finite pieces are kernel-checked with `decide` (`native_decide` is
banned repository-wide); CI re-runs `lake build`, the no-`sorry` gate and
the axiom audit on every push.

The executable certificate
[`a398189_certificate.py`](a398189_certificate.py) independently re-checks
(1) two implementations of \(T\) against each other, (2) the 91 published
OEIS DATA terms, (3) all four cases plus the excluded-class bound for
\(n \le 220\) (24,531 pairs), and (4) the mod-16 reduction. From the
repository root:

    python3 problems/oeis-a398189/a398189_certificate.py

Runtime: < 1 s. It is a sanity cross-check of finitely many instances, not
the proof; the proof is the Lean module.

## Research status and prior art

- The \(k = 0\) column is classical: McGarvey's conjecture (2007) on the
  2-adic valuation of Schenker sums A063170 was proved by T. Amdeberhan,
  D. Callan and V. Moll, *Valuations and combinatorics of truncated
  exponential sums*, [Integers 13 (2013), #A21](https://math.colgate.edu/~integers/n21/n21.Abstract.html)
  (see also P. Miska's later work on \(p\)-adic valuations of Schenker
  sums). The even-\(n\)/\(k=0\) statement is also quoted in the A063170
  and A398189 comments.
- The uniform-in-\(k\) statement conjectured in A398189 (Jul 2026) had, as
  of 2026-08-12, no proof recorded in the OEIS entry, and a web search
  found none elsewhere. The contribution preserved here is the uniform
  proof and its machine-checked form; the method (2-adic ultrametric
  estimates + periodicity mod 16) is standard.
- This is unreviewed machine-assisted work: it has not been confirmed by
  OEIS editors or peer review, and **no novelty is claimed**. Nothing has
  been submitted upstream (per this repository's rules, external
  submissions require human approval).
