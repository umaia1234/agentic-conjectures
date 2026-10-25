**English** | [한국어](DETAILS.ko.md)

# OEIS A395412: nonvanishing of primorial prime candidates

## 1. Definition

Let \(p_n\) be the \(n\)-th prime, and let

\[
P_n=\prod_{i=1}^np_i
\]

be the \(n\)-th primorial. The sequence is defined by

\[
a(n)=\#\left\{
d:\ 1\le d<p_n,\ d\text{ is squarefree},\
\frac{P_n}{d}+d\text{ is prime}
\right\}.
\]

The conjecture is that \(a(n)>0\) for all \(n\ge1\).

Every prime factor of a squarefree integer \(d<p_n\) is smaller than \(p_n\), so
\(d\mid P_n\). Hence \(P_n/d\) in the formula above is always an integer.

## 2. Lemma on the absence of small prime factors

For an admissible \(d\), set

\[
C_{n,d}=\frac{P_n}{d}+d.
\]

**Lemma.** No prime \(\ell\le p_n\) divides \(C_{n,d}\).

**Proof.** We split into two cases.

- If \(\ell\nmid d\), then the factor \(\ell\) remains in \(P_n/d\), so

  \[
  C_{n,d}\equiv d\not\equiv0\pmod\ell.
  \]

- If \(\ell\mid d\), then since both \(d\) and \(P_n\) are squarefree,
  no factor \(\ell\) remains in \(P_n/d\). Hence

  \[
  C_{n,d}\equiv P_n/d\not\equiv0\pmod\ell.
  \]

Therefore \(\ell\nmid C_{n,d}\). \(\square\)

By this lemma, the least prime factor of a composite candidate is necessarily
larger than \(p_n\). However, this does not mean that a candidate is prime, nor
does it yield the conclusion that a prime candidate exists for every \(n\).

## 3. Why a single witness proves nonvanishing

For a fixed \(n\), it suffices to exhibit a single \(d_n\) satisfying the
following three conditions.

\[
d_n<p_n,
\]

\[
d_n\text{ is squarefree},
\]

\[
C_n=\frac{P_n}{d_n}+d_n\text{ is prime}.
\]

Then, by definition, \(d_n\) is an element of the set being counted, so

\[
\boxed{a(n)\ge1}.
\]

That is, there is no need to compute the exact value of \(a(n)\) in full.

## 4. Explicit witnesses for \(85\le n\le200\)

For each \((n,d_n)\) in the table below, the conditions \(d_n<p_n\) and
squarefreeness, together with the primality of \(P_n/d_n+d_n\), were verified
by deterministic primality testing. This section is a computer-assisted finite
theorem that uses a deterministic procedure of the APRCL/ECPP family as its
final step. The values \(d_n\) in the table are the mathematical witness data
that uniquely regenerate each enormous integer candidate via the formula
\(P_n/d_n+d_n\); the primality of a candidate does not become self-evident
merely by looking at the small integers in the table. Each row of the table
contains four \((n,d_n)\) pairs.

| \(n\) | \(d_n\) | \(n\) | \(d_n\) | \(n\) | \(d_n\) | \(n\) | \(d_n\) |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 85 | 38 | 86 | 66 | 87 | 58 | 88 | 2 |
| 89 | 46 | 90 | 71 | 91 | 42 | 92 | 103 |
| 93 | 157 | 94 | 74 | 95 | 31 | 96 | 33 |
| 97 | 231 | 98 | 47 | 99 | 66 | 100 | 77 |
| 101 | 110 | 102 | 13 | 103 | 43 | 104 | 77 |
| 105 | 34 | 106 | 11 | 107 | 71 | 108 | 58 |
| 109 | 7 | 110 | 33 | 111 | 23 | 112 | 26 |
| 113 | 10 | 114 | 7 | 115 | 85 | 116 | 74 |
| 117 | 87 | 118 | 65 | 119 | 137 | 120 | 78 |
| 121 | 39 | 122 | 23 | 123 | 133 | 124 | 137 |
| 125 | 159 | 126 | 66 | 127 | 31 | 128 | 93 |
| 129 | 74 | 130 | 149 | 131 | 6 | 132 | 86 |
| 133 | 122 | 134 | 34 | 135 | 110 | 136 | 14 |
| 137 | 46 | 138 | 7 | 139 | 109 | 140 | 82 |
| 141 | 59 | 142 | 86 | 143 | 73 | 144 | 13 |
| 145 | 393 | 146 | 101 | 147 | 103 | 148 | 113 |
| 149 | 142 | 150 | 69 | 151 | 26 | 152 | 105 |
| 153 | 3 | 154 | 85 | 155 | 102 | 156 | 113 |
| 157 | 107 | 158 | 74 | 159 | 23 | 160 | 19 |
| 161 | 187 | 162 | 546 | 163 | 101 | 164 | 190 |
| 165 | 87 | 166 | 158 | 167 | 217 | 168 | 11 |
| 169 | 43 | 170 | 66 | 171 | 1 | 172 | 1 |
| 173 | 19 | 174 | 85 | 175 | 57 | 176 | 15 |
| 177 | 229 | 178 | 113 | 179 | 137 | 180 | 29 |
| 181 | 238 | 182 | 431 | 183 | 94 | 184 | 57 |
| 185 | 35 | 186 | 158 | 187 | 2 | 188 | 638 |
| 189 | 41 | 190 | 2 | 191 | 131 | 192 | 141 |
| 193 | 331 | 194 | 479 | 195 | 41 | 196 | 13 |
| 197 | 102 | 198 | 65 | 199 | 3 | 200 | 82 |

Therefore, as a finite statement,

\[
\boxed{85\le n\le200\Longrightarrow a(n)>0}
\]

is proved. This is a finite proof giving a separate witness for each \(n\); it
is not a single construction of \(d_n\) that works for all \(n\). Section 5
re-proves this range with ECPP certificates and extends it to
\(n\le 478\); the full A395412 conjecture remains open.

## 5. ECPP certificates for \(85\le n\le 478\)

For every \(85\le n\le 478\), the data file `ecpp_witnesses.json` records one
\(d_n\): the least squarefree \(d<p_n\) for which \(C_n=P_n/d_n+d_n\) passes
the BPSW probable-prime test. BPSW only selects \(d_n\); it is not part of the
proof. The witnesses agree with the original run for \(85\le n\le400\) (proved
there for \(n\le200\), only BPSW-screened for \(201\le n\le400\)).

The primality of \(C_n\) is proved by an Atkin–Morain ECPP certificate, a list
of steps \((N_i,t_i,s_i,a_i,x_i,y_i)\), \(1\le i\le\ell\), with \(N_1=C_n\).
Put

\[
m_i=N_i+1-t_i,\qquad q_i=\frac{m_i}{s_i},\qquad
b_i\equiv y_i^2-x_i^3-a_ix_i\pmod{N_i},
\]

\(E_i:\ y^2=x^3+a_ix+b_i\) and \(P_i=(x_i,y_i)\in E_i(\mathbb Z/N_i\mathbb Z)\).
The certificate requires \(q_i=N_{i+1}\) for \(i<\ell\) and \(q_\ell<2^{64}\).

**Theorem (Goldwasser–Kilian, Atkin–Morain).** Let \(N>1\) with
\(\gcd(N,6)=1\), let \(E:\ y^2=x^3+ax+b\) with \(\gcd(4a^3+27b^2,N)=1\), let
\(P\) be a point of \(E\) modulo \(N\), let \(s\ge1\), and let \(q\) be a
prime with \(q>(N^{1/4}+1)^2\). If for every prime \(p\mid N\) the reduction
\(Q_p\) of \(Q=[s]P\) satisfies \(Q_p\ne O\) and \([q]Q_p=O\), then \(N\) is
prime.

**Proof.** Let \(p\mid N\) be prime. Since \(q\) is prime, \(Q_p\) has order
exactly \(q\) in \(E(\mathbb F_p)\), so Hasse's bound gives
\(q\le\#E(\mathbb F_p)\le(\sqrt p+1)^2\). Hence \(\sqrt p>N^{1/4}\), that is,
\(p>\sqrt N\). A composite \(N\) has a prime factor at most \(\sqrt N\), so
\(N\) is prime. \(\square\)

Applying the theorem to the steps from \(i=\ell\) down to \(i=1\) proves every
\(N_i\), in particular \(C_n\), prime, once \(q_\ell<2^{64}\) is known to be
prime. The latter is a Miller–Rabin test to the prime bases \(2,\dots,37\),
which is deterministic below \(3.18\cdot10^{23}\) (Sorenson–Webster, 2017).

Each certificate was produced by PARI/GP `primecert` and accepted by PARI's
`primecertisvalid` after being written to disk and read back. It was then
re-checked by `verify_witnesses.py`, a checker written independently of PARI.
That checker works in Jacobian coordinates \((X:Y:Z)\) modulo \(N\). The
doubling and the mixed-addition formulas give the correct group law modulo a
prime \(p\mid N\) whenever their inputs are affine modulo \(p\) and the
operation is not exceptional (an addition of points with equal
\(x\)-coordinates, or the doubling of a point with \(y=0\)). An exceptional
operation outputs \(Z\equiv0\pmod p\), and each later \(Z\) is a multiple of
the previous one, so it stays \(0\) modulo \(p\). The checker computes
\(Q=[s]P\) and \(R=[q-1]Q\) by double-and-add and requires
\(\gcd(Z_Q,N)=\gcd(Z_R,N)=1\) and \(R=-Q\). As these final \(Z\) are units
modulo \(N\), no intermediate \(Z\) vanished modulo any prime \(p\mid N\), so no
operation was exceptional and each one computed the group law of
\(E(\mathbb F_p)\). Hence \(Q_p\ne O\) and \([q]Q_p=R_p+Q_p=O\), as the theorem
requires. The checker also verifies
\(\gcd(N,6)=1\), the discriminant condition, \(s_iq_i=m_i\), and the sufficient
integer inequality \(q>(\lfloor N^{1/4}\rfloor+2)^2\). Therefore

\[
\boxed{85\le n\le 478\Longrightarrow a(n)>0}.
\]

For \(85\le n\le200\) this is a second proof of Section 4 with the same
witnesses; for \(201\le n\le400\) it turns the earlier BPSW screen into a
proof; \(401\le n\le 478\) extends the range previously recorded in this
repository (no novelty is claimed). Nothing is claimed for \(n>478\), and the
full A395412 conjecture remains open.
