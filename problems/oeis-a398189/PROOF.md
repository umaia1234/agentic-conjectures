**English** | [한국어](PROOF.ko.md)

# Proof of the A398189 valuation conjecture

Throughout, \(v_2\) denotes the 2-adic valuation. For \(n, m \ge 0\) set

\[
S_n(m) \;=\; \sum_{j=0}^{m} \frac{m!}{j!}\, n^j ,
\]

so that the OEIS A398187 triangle is \(T(n,k) = S_n(n-k)\) for
\(0 \le k \le n\) (column \(k = 0\) is the Schenker sums A063170), and
A398189\((n,k) = v_2(T(n,k))\).

**Theorem** (the conjecture in OEIS A398189, plus a bound in its excluded
class). Let \(0 \le k \le n\) and \(m = n - k\).

1. If \(n\) is even, \(v_2(T(n,k)) = v_2(m!)\).
2. If \(n\) is odd and \(k\) is odd, \(v_2(T(n,k)) = 0\).
3. If \(n\) is odd, \(k\) is even and \(k \not\equiv 14 \pmod{16}\), then
   \(v_2(T(n,k)) = v_2(k+2)\). (For \(k = 0\) this gives
   \(v_2(T(n,0)) = 1\), the case OEIS lists separately.)
4. If \(n\) is odd and \(k \equiv 14 \pmod{16}\), then
   \(v_2(T(n,k)) \ge 4\). (OEIS conjectures no formula here; this bound
   explains why: the valuation escapes every fixed modulus-16 pattern.)

The whole proof rests on the elementary recurrence obtained by splitting
off the \(j = m+1\) term of \(S_n(m+1)\):

\[
S_n(0) = 1, \qquad S_n(m+1) = (m+1)\,S_n(m) + n^{m+1}. \tag{R}
\]

## Case 1: \(n\) even — an ultrametric induction

**Claim.** For even \(n\) (including \(n = 0\)) and every \(m \ge 0\),
\(S_n(m) = 2^{v_2(m!)} c\) with \(c\) odd.

*Proof.* Induction on \(m\). For \(m = 0\), \(S_n(0) = 1 = 2^{v_2(0!)}\cdot 1\).
Assume \(S_n(m) = 2^{v_2(m!)} c\), \(c\) odd. Write \(m+1 = 2^{w} d\) with
\(d\) odd and \(n = 2s\). By (R),

\[
S_n(m+1) = 2^{w} d \cdot 2^{v_2(m!)} c + 2^{m+1} s^{m+1}
        = 2^{v_2((m+1)!)}\left( dc + 2^{\,m+1-v_2((m+1)!)}\, s^{m+1} \right),
\]

using \(v_2((m+1)!) = w + v_2(m!)\). By Legendre's formula
\(v_2((m+1)!) = (m+1) - s_2(m+1) \le m\), so the exponent
\(m+1-v_2((m+1)!)\) is \(\ge 1\), the second summand is even, and the
bracket is odd. ∎

Hence \(v_2(S_n(m)) = v_2(m!)\), which is Case 1. (In the formal proof the
bound \(v_2((m+1)!) < m+1\) is mathlib's
`padicValNat_factorial_lt_of_ne_zero`.)

## Case 2: \(n\) odd, \(m\) even — parity is immediate

If \(m = 0\), \(S_n(0) = 1\) is odd. If \(m \ge 2\) is even, (R) gives
\(S_n(m) = m\,S_n(m-1) + n^{m}\) = even + odd = odd. Since
\(k = n - m\) is odd exactly when \(m\) is even (for odd \(n\)), this is
Case 2 — no induction needed.

## Cases 3–4: \(n\) odd, \(m\) odd — everything happens mod 16

Since the target valuations are at most 3, and \(v_2(x)\) is determined by
\(x \bmod 16\) whenever \(x \not\equiv 0 \pmod{16}\), it suffices to
compute \(S_n(m) \bmod 16\).

**Reduction lemma.** For odd \(n\), \(S_n(m) \bmod 16\) depends only on
\((n \bmod 16,\; m \bmod 16)\).

*Proof.* Dependence on \(n\) only through \(n \bmod 16\) is clear from (R).
Periodicity in \(m\): by induction using (R), from
\(S_n(m+16) \equiv S_n(m)\) follows
\(S_n(m+17) = (m+17) S_n(m+16) + n^{m+17} \equiv (m+1) S_n(m) + n^{m+1}
= S_n(m+1) \pmod{16}\), because \(m+17 \equiv m+1 \pmod{16}\) and
\(n^{16} \equiv 1 \pmod{16}\) (every odd residue mod 16 satisfies
\(a^4 \equiv 1\)). The base case \(S_n(16) \equiv 1 \equiv S_n(0)
\pmod{16}\) holds because in
\(S_n(16) = \sum_{j\le 16} (16!/j!)\, n^j\) every coefficient
\(16!/j!\) with \(j < 16\) is a product of \(16-j\) consecutive integers
ending at 16, hence divisible by 16, leaving
\(S_n(16) \equiv n^{16} \equiv 1\). (In the formal proof this base case is
a finite computation over the 16 residues.) ∎

**Finite verification.** By the reduction lemma, for odd \(n\) and odd
\(m \le n\) the pair
\(\left(S_n(m) \bmod 16,\; (n-m+2) \bmod 16\right)\) only depends on the
residues \((a, b) = (n \bmod 16, m \bmod 16)\) — 8 × 8 odd pairs. The
table of \(S \bmod 16\) values (rows \(a\), columns \(b = 1, 3, \dots, 15\)):

| \(a\) \\ \(b\) | 1 | 3 | 5 | 7 | 9 | 11 | 13 | 15 |
|---|---|---|---|---|---|---|---|---|
| 1  | 2  | 0  | 6  | 4  | 10 | 8  | 14 | 12 |
| 3  | 4  | 14 | 0  | 10 | 12 | 6  | 8  | 2  |
| 5  | 6  | 12 | 10 | 0  | 14 | 4  | 2  | 8  |
| 7  | 8  | 10 | 4  | 6  | 0  | 2  | 12 | 14 |
| 9  | 10 | 8  | 14 | 12 | 2  | 0  | 6  | 4  |
| 11 | 12 | 6  | 8  | 2  | 4  | 14 | 0  | 10 |
| 13 | 14 | 4  | 2  | 8  | 6  | 12 | 10 | 0  |
| 15 | 0  | 2  | 12 | 14 | 8  | 10 | 4  | 6  |

In every cell the entry lies in the same 2-adic class mod 16 as
\(d = (a - b + 2) \bmod 16\): both are \(0\), or both are odd (this column
range has none — odd \(b\) with odd \(a\) gives even \(d\)), or both are
\(2 \cdot \mathrm{odd}\), \(4 \cdot \mathrm{odd}\), \(8 \cdot
\mathrm{odd}\) mod 16. (In the formal proof this is the `decide`-checked
lemma `core`; the certificate script recomputes the same residues in its
step 4.)

Consequently, for odd \(n\), odd \(m \le n\), \(k = n - m\):

- if \((k+2) \bmod 16 \ne 0\), i.e. \(k \not\equiv 14 \pmod{16}\), then
  \(v_2(k+2) \le 3\) and \(S_n(m) \equiv (k+2)\cdot(\text{odd unit})\)
  in the sense above, so \(v_2(S_n(m)) = v_2(k+2)\) — Case 3;
- if \(k \equiv 14 \pmod{16}\), then \(S_n(m) \equiv 0 \pmod{16}\), so
  \(v_2(S_n(m)) \ge 4\) — Case 4. ∎

## Remarks

- Case 1 for \(k = 0\) and the value 1 for odd \(n\), \(k = 0\) are the
  McGarvey conjecture on Schenker sums (A063170), proved by
  Amdeberhan–Callan–Moll, *Valuations and combinatorics of truncated
  exponential sums*, Integers 13 (2013), #A21. The argument above is the
  same standard 2-adic technique, run uniformly in the extra parameter
  \(k\); the point of this directory is the uniform statement and its
  machine-checked form, not the method.
- The bound in Case 4 is sharp in the sense that no fixed formula mod a
  power of two can hold there: computation shows \(v_2\) takes many values
  \(\ge 4\) in the excluded class (see the OEIS entry's "no simple
  formula" remark).
- The full statement is formalized sorry-free in
  [`AgenticConjectures/OeisA398189.lean`](../../AgenticConjectures/OeisA398189.lean);
  the finite pieces (the mod-16 base case and the 64-cell table) are
  kernel-checked by `decide` (not `native_decide`, which this repository
  bans).
