**English** | [한국어](PROOF.ko.md)

# OEIS A136433 — Detailed proof of the 9-lag linear recurrence

This document is the canonical proof, consolidating on a per-problem basis
the detailed proof written on 2026-08-11 and the subsequent mathematical
audit. The finite computational certificate does not replace the proof; its
only role is to independently re-check the definitions, boundaries, and
derived identities.

## 2.1. Definition and one-step transition

The sequence is defined by

\[
a_1=11
\]

and, for all \(n\ge0\),

\[
a_{n+2}
=((n\bmod3)+1)a_{n+1}+((n\bmod2)+1).
\tag{2.1}
\]

Substituting \(t=n+1\), we have \(t\ge1\) and

\[
a_{t+1}=c_ta_t+d_t,
\tag{2.2}
\]

where

\[
c_t=((t-1)\bmod3)+1,\qquad
d_t=((t-1)\bmod2)+1.
\tag{2.3}
\]

The two coefficient sequences satisfy \(c_{t+3}=c_t\) and \(d_{t+2}=d_t\),
respectively. Writing out the first six values gives the following.

| \(t\bmod6\) | \(c_t\) | \(d_t\) |
|---:|---:|---:|
| \(1\) | \(1\) | \(1\) |
| \(2\) | \(2\) | \(2\) |
| \(3\) | \(3\) | \(1\) |
| \(4\) | \(1\) | \(2\) |
| \(5\) | \(2\) | \(1\) |
| \(0\) | \(3\) | \(2\) |

Therefore the pair \((c_t,d_t)\) has period
\(\operatorname{lcm}(3,2)=6\).

## 2.2. Three-step transition

**Lemma 2.1.** For all \(t\ge1\),

\[
a_{t+3}=6a_t+B_t,
\tag{2.4}
\]

where

\[
B_t=
c_{t+2}c_{t+1}d_t+
c_{t+2}d_{t+1}+
d_{t+2}.
\tag{2.5}
\]

Moreover \(B_{t+6}=B_t\).

**Proof.** Composing (2.2) twice gives

\[
\begin{aligned}
a_{t+2}
&=c_{t+1}a_{t+1}+d_{t+1}\\
&=c_{t+1}c_ta_t+c_{t+1}d_t+d_{t+1}.
\end{aligned}
\]

Applying it once more gives

\[
\begin{aligned}
a_{t+3}
&=c_{t+2}a_{t+2}+d_{t+2}\\
&=c_{t+2}c_{t+1}c_t\,a_t\\
&\quad+c_{t+2}c_{t+1}d_t
 +c_{t+2}d_{t+1}+d_{t+2}.
\end{aligned}
\tag{2.6}
\]

Since \(c_t\) cycles periodically through \(1,2,3\), the product of any
three consecutive values is

\[
c_{t+2}c_{t+1}c_t=1\cdot2\cdot3=6.
\]

Therefore (2.4) and (2.5) hold. \(B_t\) is determined only by
\((c_t,d_t),(c_{t+1},d_{t+1}),(c_{t+2},d_{t+2})\), and all of these pairs
are unchanged when shifted by 6, so
\(B_{t+6}=B_t\). \(\square\)

Directly computing \(B_t\) over one period gives

\[
\begin{aligned}
B_1&=3\cdot2\cdot1+3\cdot2+1=13,\\
B_2&=1\cdot3\cdot2+1\cdot1+2=9,\\
B_3&=2\cdot1\cdot1+2\cdot2+1=7,\\
B_4&=3\cdot2\cdot2+3\cdot1+2=17,\\
B_5&=1\cdot3\cdot1+1\cdot2+1=6,\\
B_6&=2\cdot1\cdot2+2\cdot1+2=8.
\end{aligned}
\]

That is, \((B_1,\ldots,B_6)=(13,9,7,17,6,8)\), and these six values
repeat.

## 2.3. The 9-lag recurrence

**Theorem 2.2.** For all \(n\ge10\),

\[
a_n=6a_{n-3}+a_{n-6}-6a_{n-9}
\tag{2.7}
\]

holds.

**Proof.** Applying (2.4) at \(t\) gives

\[
B_t=a_{t+3}-6a_t.
\tag{2.8}
\]

Applying the same identity at \(t+6\) gives

\[
a_{t+9}=6a_{t+6}+B_{t+6}.
\tag{2.9}
\]

Substituting \(B_{t+6}=B_t\) into (2.8) and (2.9) gives

\[
\begin{aligned}
a_{t+9}
&=6a_{t+6}+B_t\\
&=6a_{t+6}+a_{t+3}-6a_t.
\end{aligned}
\]

Setting \(n=t+9\), we have

\[
t+6=n-3,\qquad t+3=n-6,\qquad t=n-9,
\]

which yields (2.7). Since the range of the original transition is
\(t\ge1\), we have \(n=t+9\ge10\). Conversely, for all \(n\ge10\) we have
\(t=n-9\ge1\), so the argument applies. \(\square\)

At the first boundary value \(n=10\),

\[
a_{10}=6a_7+a_4-6a_1,
\]

and with the actual values,

\[
2959=6\cdot491+79-6\cdot11
\]

holds. At \(n=9\), the right-hand side would involve \(a_0\), which is not
defined in the original setup, so \(n=10\) is the natural first position at
which the recurrence can be used in this indexing.
