**English** | [한국어](DETAILS.ko.md)

# OEIS A076141: Complete Binary-Geometry Reduction for \(n<2^{40}\)

## 1. Definition and the Finite-Range Theorem

Let \(L\) be the length of the standard binary representation of a positive
integer \(n\).

\[
2^{L-1}\le n<2^L.
\]

Define the integer obtained by shifting a window of length \(L\) upward by
\(u\) places from the least significant bit of \(n^2\) as

\[
W_u(n^2;L)=
\left\lfloor\frac{n^2}{2^u}\right\rfloor\bmod2^L
\]

A076141 counts the number of positions \(u\) with \(W_u(n^2;L)=n\).
Overlapping occurrences are also allowed.

The finite proposition proved in this work is

\[
\boxed{
1\le n<2^{40}
\Longrightarrow
\#\{u:W_u(n^2;L)=n\}\le1
}
\tag{A076-1}
\]

## 2. Bit Length of the Square and Occurrences at the Two Ends

Let \(M\) be the bit length of \(n^2\). Then

\[
2^{2L-2}\le n^2<2^{2L}
\]

so

\[
M=2L-\varepsilon,\qquad\varepsilon\in\{0,1\}.
\]

### The Lowest Window

An occurrence at position 0 means

\[
n^2\equiv n\pmod{2^L},
\]

i.e., \(2^L\mid n(n-1)\). Two consecutive integers are coprime, and exactly
one of them is even.

- If \(n\) is even, we would need \(2^L\mid n\), contradicting
  \(0<n<2^L\).
- If \(n\) is odd, then \(2^L\mid n-1\), so \(n=1\).

The word of \(n=1\) appears only once in \(n^2=1\). Therefore an occurrence
in a counterexample cannot be the lowest window.

### The Highest Window

Let \(t=M-L\) be the starting position of the highest window. If this window
equals \(n\), then

\[
n2^t\le n^2<(n+1)2^t,
\]

so

\[
2^t\le n<2^t+\frac{2^t}{n}.
\]

If \(M=2L\), then \(t=L\), which yields the contradiction \(n\ge2^L\).
If \(M=2L-1\), then \(t=L-1\) and \(n\ge2^t\), so

\[
2^t\le n<2^t+1.
\]

Therefore \(n=2^{L-1}\). In this case \(n^2=2^{2L-2}\) has only one bit
equal to 1, so the word \(10\cdots0\) likewise appears only once, in the
highest window. Therefore, if there is a number with two or more occurrences,
all of its occurrences are internal.

## 3. The Geometry of Two Internal Occurrences

Take the starting positions of two distinct occurrences to be

\[
s<s+d
\]

Since neither is the lowest or the highest window, \(s\ge1\), and the length
of the prefix remaining above the second window,

\[
p=M-(s+d+L)
\]

also satisfies \(p\ge1\).

Let the overlap length of the two windows be

\[
r=L-d
\]

Since the two windows and the nonempty parts at both ends all lie within
\(M\le2L\) bits, \(1\le r<L\). Counting bits,

\[
M=p+(L+d)+s.
\]

Substituting \(M=2L-\varepsilon\) and \(r=L-d\),

\[
\boxed{p+s=r-\varepsilon}.
\tag{A076-2}
\]

Therefore the enumeration range is exactly

\[
r\ge\varepsilon+2,\qquad
1\le s\le r-\varepsilon-1,\qquad
p=r-\varepsilon-s
\]

## 4. The Period Forced by the Overlap

Writing the binary bits of \(n\) from the most significant as
\(w_0w_1\cdots w_{L-1}\), the overlap of the two identical windows gives

\[
w_i=w_{i+d},\qquad 0\le i<r=L-d.
\]

That is, the word has period \(d\) on the overlapping interval. Letting
\(q\) denote the common \(r\)-bit integer,

\[
\boxed{
q=\left\lfloor\frac n{2^d}\right\rfloor
=n\bmod2^r
}.
\tag{A076-3}
\]

The first expression means that \(q\) is the top \(r\) bits of \(n\); the
second means that the same \(q\) is the bottom \(r\) bits. In particular,

\[
q2^d\le n\le(q+1)2^d-1.
\tag{A076-4}
\]

The possible \(q\) are completely parameterized as follows.

- If \(r\le d\), take every \(r\)-bit word whose leading bit is 1.
- If \(r>d\), repeat periodically every \(d\)-bit seed whose leading bit
  is 1 and take its first \(r\) bits.

Therefore, for each \((L,r,d)\), the number of \(q\) candidates is

\[
2^{\min(r,d)-1}
\]

## 5. Reduction to a Quadratic Equation

Define the following.

\[
E=L+d+s.
\]

Let \(A\) be the most significant \(p\)-bit prefix of \(n^2\) and \(B\)
the least significant \(s\)-bit suffix. Then

\[
A=\left\lfloor\frac{n^2}{2^E}\right\rfloor,
\qquad
B=n^2\bmod2^s.
\]

Since \(A\) has exactly \(p\) bits,

\[
2^{p-1}\le A\le2^p-1.
\]

Moreover, since \(s<r\) and \(n\equiv q\pmod{2^r}\),

\[
\boxed{B=q^2\bmod2^s}.
\tag{A076-5}
\]

Adding the two occurrences as \(n2^s\) and \(n2^{s+d}\), the common \(r\)
bits \(q\) enter twice at position \(s+d\). Subtracting this once yields the
exact place-value decomposition

\[
n^2=A2^E+n2^s+n2^{s+d}-q2^{s+d}+B
\]

Therefore, setting

\[
C=2^s(2^d+1),
\]

\[
D_0=A2^E-q2^{d+s}+B
\]

we obtain

\[
\boxed{n^2-Cn-D_0=0}.
\tag{A076-6}
\]

Here \(D_0>0\). Indeed, since \(q<2^r\) and \(d\ge1\),

\[
q2^{d+s}<2^{r+d+s}=2^{L+s}<2^{L+d+s}=2^E\le A2^E.
\]

Therefore the only possible positive root is

\[
n=\frac{C+\sqrt{\Delta}}2,
\qquad
\Delta=C^2+4D_0
\]

That is, \(\Delta\) must be a perfect square and the parity of the numerator
must match.

### The Exact Range of \(A\)

Set \(N_-=q2^d\) and \(N_+=(q+1)2^d-1\). By (A076-4) and the
monotonicity of the squaring function,

\[
\left\lfloor\frac{N_-^2}{2^E}\right\rfloor
\le A\le
\left\lfloor\frac{N_+^2}{2^E}\right\rfloor.
\]

Intersecting this with the \(p\)-bit condition on \(A\),

\[
\max\left(
\left\lfloor\frac{N_-^2}{2^E}\right\rfloor,2^{p-1}
\right)
\le A\le
\min\left(
\left\lfloor\frac{N_+^2}{2^E}\right\rfloor,2^p-1
\right).
\tag{A076-7}
\]

This interval contains every actually possible \(A\). Since there may be
surplus candidates, for each recovered root we directly verify again at the
end that

\[
\operatorname{bitlen}(n)=L,
\]

\[
\operatorname{bitlen}(n^2)=2L-\varepsilon,
\]

\[
W_s(n^2;L)=W_{s+d}(n^2;L)=n
\]

## 6. Why the Enumeration Is Complete

Suppose a counterexample exists and pick one pair of distinct occurrences.

1. By the exclusion of occurrences at the two ends, \(s,p\ge1\).
2. The bit length of the square uniquely determines
   \(\varepsilon\in\{0,1\}\).
3. The two starting positions determine \(d\) and \(r=L-d\) and satisfy
   (A076-2).
4. The overlap determines \(q\), and this \(q\) is necessarily included in
   the periodic-seed enumeration above.
5. The actual prefix \(A\) is necessarily contained in (A076-7).
6. The quadratic equation for that \((A,q)\) has the original \(n\) as a
   positive integer root.
7. The recovered \(n\) also passes the final two-window checks.

Therefore, if a counterexample exists, it is necessarily detected in at least
one geometry. A counterexample with three or more occurrences may correspond
to several occurrence pairs, so the proposition needed is not the uniqueness
of the geometry but this **coverage**.

## 7. Finite Enumeration Results and Exact Ranges

The number of geometries for a fixed \(L\) is

\[
\sum_{r=2}^{L-1}(r-1)+
\sum_{r=3}^{L-1}(r-2)
=(L-2)^2.
\]

Therefore the total number of geometries for \(2\le L\le40\) is

\[
\sum_{k=0}^{38}k^2=19019
\]

In these geometries,

\[
181{,}402{,}314
\]

\(q\) candidates and

\[
99{,}006{,}717
\]

quadratic equations that passed the prefix range were examined exactly. No
number passed all of the perfect-square discriminant, integer-root, bit-length,
and two-window conditions.

If \(L\le40\), then \(n^2<2^{80}\), and in this reduction
\(C<2^{40}\), \(D_0<2^{80}\), and \(\Delta<2^{83}\). Therefore every
quantity used in the enumeration lies within a fixed exact integer range.
This proves (A076-1), but the infinite remaining range \(n\ge2^{40}\) is
still open.

## 8. Extension (2026-10): Single-Occurrence Enumeration

This section belongs to the second, independent method. It comes with the
Lean module `AgenticConjectures/OeisA076141.lean` and the programs
`a076141_occ_closed.cpp` (P) and `a076141_occ_hensel.cpp` (Q).

The method does not enumerate pairs of occurrences. Instead it enumerates
every *single* occurrence at a prescribed set of positions, then counts all
occurrences of each number it finds. It proves

\[
\boxed{
1\le n<2^{64}
\Longrightarrow
\#\{u:W_u(n^2;L)=n\}\le1
}
\tag{A076-8}
\]

from every position, so §8.1–§8.2 suffice and the pair lemmas of §8.3 are
not needed. It also proves

\[
\boxed{
1\le n<2^{100}
\Longrightarrow
\#\{u:W_u(n^2;L)=n\}\le1
}
\tag{A076-9}
\]

from the positions allowed by the Lean-checked pair lemmas of §8.3–§8.4.
The same lemmas also give the unconditional bound (A076-15) of §8.4,
\(a(n)\le2\) for every \(n\), which uses no computation.

### 8.1 Reductions

**Even numbers.** Suppose \(1\le n<2^L\) and
\(W_t((2n)^2;L+1)=2n\). Then \(t\ge1\) and \(W_{t-1}(n^2;L)=n\).

- If \(t=0\), then \(4n^2\equiv2n\pmod{2^{L+1}}\), so
  \(2^L\mid n(2n-1)\). Since \(2n-1\) is odd, this forces \(2^L\mid n\),
  which is impossible.
- If \(t\ge1\), put \(z=\lfloor4n^2/2^t\rfloor\). Then
  \(z\bmod2^{L+1}=2n\), so
  \(\lfloor z/2\rfloor\bmod2^L=n\) and
  \(\lfloor z/2\rfloor=\lfloor n^2/2^{t-1}\rfloor\).

Hence \(a(2n)\le a(n)\), and below every counterexample there is an odd one.
Since \(a(1)=1\), that odd counterexample is at least \(3\).

**Positions.** For odd \(n\ge3\), every occurrence position \(t\) satisfies
\(3\le t\le L-1\).

- An occurrence gives \(n\le\lfloor n^2/2^t\rfloor\), so \(2^t\le n<2^L\).
- Position \(0\) is excluded by §2.
- For \(t\in\{1,2\}\), the lowest window bit is bit \(t\) of \(n^2\). That
  bit is \(0\), since \(n^2\equiv1\pmod8\). The lowest bit of \(n\) is \(1\),
  so the window cannot equal \(n\).

### 8.2 One Occurrence at a Fixed Position

Fix an odd \(n\) of bit length \(L\) and a position \(3\le t\le L-1\). Then
\(W_t(n^2;L)=n\) is equivalent to

\[
n^2=A\,2^{t+L}+n\,2^t+B,\qquad
A=\left\lfloor\frac{n^2}{2^{t+L}}\right\rfloor,\quad
B=n^2\bmod2^t\equiv1\pmod8 .
\tag{A076-10}
\]

With \(x=n-2^{t-1}\), so that \(0\le x<2^L\), this reads

\[
x^2=A\,2^{t+L}+B+4^{t-1}.
\tag{A076-11}
\]

**Bottom method (given \(B\)).** By (A076-11),
\(x^2\equiv c:=B+4^{t-1}\pmod{2^{L+2}}\), with \(c\equiv1\pmod8\). The
square roots of \(c\) modulo \(2^{L+2}\) reduce modulo \(2^{L+1}\) to a
pair \(\pm y_0\). Their representatives in \([0,2^{L+1})\) are odd and sum to
\(2^{L+1}\), so exactly one of them lies in \([0,2^L)\). That one is \(x\).
Each of the \(2^{t-3}\) residues \(B\equiv1\pmod8\) therefore gives at most
one candidate.

**Top method (given \(A\)).** Put \(X=A\,2^{t+L}+4^{t-1}\). By (A076-11),
\(X\le x^2<X+2^t\), so \(x\ge y_0:=\lceil\sqrt X\rceil\). If
\(x\ge y_0+1\), then \(x^2\ge X+2y_0+1>X+2^t\), because
\(y_0\ge2^{t-1}\). Hence \(x=y_0\). Each

\[
A\in\left[\left\lfloor\frac{4^{L-1}}{2^{t+L}}\right\rfloor,
\left\lfloor\frac{(2^L-1)^2}{2^{t+L}}\right\rfloor\right]
\]

therefore gives at most one candidate.

Each candidate is accepted only after an exact check of the window of
\(n^2\) at \(t\). For each accepted \(n\), the program counts all
occurrences directly, and a count of at least \(2\) is a counterexample. The
search is complete for occurrences at the examined positions, because each
such \(n\) is the candidate of its own \(B\) and of its own \(A\). At
position \(t\), the bottom method costs \(2^{t-3}\) candidates and the top
method about \(3\cdot2^{L-t-2}\).

The second program Q reaches the same candidates without taking square
roots.

- **Bottom.** It lifts \(r=n\bmod2^{t-1}\) one bit at a time using
  \(F(n)=n^2-2^tn-B\). For odd \(n\) and \(j\ge2\),
  \(F(n+2^j)-F(n)\equiv2^{j+1}\pmod{2^{j+2}}\), so each bit is forced. The
  identity \(F(2^t-n)=F(n)\) pairs the lift of \(r\) with the lift of
  \(-r\).
- **Top.** On \([2^{L-1},2^L)\), the function \(f(n)=n^2-2^tn\) increases by
  more than \(2^t\) at each step. So \(n\) is the least \(n\ge2^{L-1}\) with
  \(f(n)\ge A\,2^{t+L}\), and Q finds it by an exact galloping search.

Both programs use the same index sets, so their candidate counts agree
exactly.

### 8.3 Two Lemmas on Pairs

Suppose \(W_s(n^2;L)=W_{s+d}(n^2;L)=n\) with \(d\ge1\) and \(s+d\le L\).
Write \(L=s+d+u\) and put

\[
P=2^s,\quad D=2^d,\quad U=2^u,\quad E=PDU=2^L,\quad g=D-1.
\]

Consider the window of length \(d+L\) at position \(s\). Its upper \(L\)
bits and its lower \(L\) bits both equal \(n\). Therefore

\[
n^2=A\,P^2D^2U+n\,PD+mP+B,\qquad nD+m=Eb+n,
\tag{A076-12}
\]

where \(A=\lfloor n^2/2^{s+d+L}\rfloor\), \(B=n^2\bmod P\),
\(m=n\bmod D\) and \(b=\lfloor(nD+m)/E\rfloor\). Eliminating \(n\) gives

\[
PD\,E\,(Ub^2-gb-g^2A)=g^2B-gPm-m^2+2Ebm .
\tag{A076-13}
\]

Also \(m\ge1\). Otherwise \(ng=Eb\), and \(\gcd(E,g)=1\) gives \(E\mid n\),
which is impossible for \(0<n<E\).

**Lemma 1 (close pairs).** If \(2d+s+1\le L\), the pair is impossible.

*Proof.* Put \(X=g^2B-gPm-m^2\). By (A076-13), \(X\equiv0\pmod E\). The
bounds \(1\le m\le g\), \(0\le B\le P-1\) and \(U\ge2D\) give \(|X|<E\), so
\(X=0\). Then \((2m+gP)^2=g^2(P^2+4B)\), hence \(g\mid 2m+gP\) and
\(g\mid 2m\). Since \(g\) is odd, \(g\mid m\), so \(m=g\). Substituting
gives \(X=g^2(B-P-1)=0\), that is, \(B=P+1>P-1\), a contradiction.
\(\square\)

**Lemma 2 (far lower occurrence).** If \(2^{L-1}\le n\), \(d<s\) and
\(s+d<L\), the pair is impossible.

*Proof.* The hypotheses give \(P\ge2D\) and \(U\ge2\). From \(ng+m=Eb\)
with \(2^{L-1}\le n<2^L\) and \(1\le m\le g\), we get \(D\le2b\) and
\(b\le g\). Put \(Y=X+2Ebm\). By (A076-13), \(Y\) is a multiple of
\(PD\,E\). The same bounds give \(0<Y<PD\,E\), a contradiction. \(\square\)

### 8.4 Pair Geometry and the Reduced Position Plan

Let \(s<t\) be two occurrences of an odd \(n\ge3\). By §8.1,
\(3\le s\) and \(t\le L-1\). Lemma 2 with \(d=t-s\) gives \(2s\le t\), and
Lemma 1 gives \(L+s\le2t\). Together,

\[
3\le s,\qquad 2s\le t,\qquad L+s\le2t,\qquad t\le L-1 .
\tag{A076-14}
\]

Put \(\sigma=\lfloor L/3\rfloor+1\) and
\(\tau=\max\bigl(2\sigma+2,\lceil(L+\sigma+1)/2\rceil\bigr)\). If
\(s\ge\sigma+1\), then \(t\ge2s\ge2\sigma+2\) and
\(2t\ge L+s\ge L+\sigma+1\), so \(t\ge\tau\). Every counterexample of bit
length \(L\) therefore has an occurrence at a position in
\([3,\sigma]\cup[\tau,L-1]\).

**Corollary (at most two occurrences).** An odd \(n\ge3\) has no three
occurrences \(s_1<s_2<s_3\). Applying (A076-14) to the pairs
\((s_1,s_2)\) and \((s_2,s_3)\) gives \(L+s_1\le2s_2\le s_3\le L-1\),
which is impossible. By §8.1, the occurrences of \(2n\) shift injectively to
occurrences of \(n\), so \(n\ge1\) has at most as many occurrences as its
odd part. Since \(a(0)=a(1)=1\),

\[
a(n)\le2\qquad(n\ge0).
\tag{A076-15}
\]

This bound uses no computation.

The two position plans are as follows.

- **Reduced plan.** It examines exactly \([3,\sigma]\cup[\tau,L-1]\), with
  the bottom method on \([3,\sigma]\) and the top method on \([\tau,L-1]\).
  It costs about \(2^{\sigma-2}+3\cdot2^{L-\tau-1}=O(2^{L/3})\) candidates
  per \(L\).
- **Full plan.** It examines every position \(3\le t\le L-1\), with the
  bottom method for \(t\le\lfloor(L+2)/2\rfloor\) and the top method above.
  It costs \(O(2^{L/2})\) per \(L\) and relies only on §8.1–§8.2.

### 8.5 What the Lean Module Checks

The Lean module proves the following, with no `sorry`, no extra axioms and
no `native_decide`.

- §8.1: `occ_of_occ_two_mul`, `occ_descent`, `exists_odd_of_two_occ`,
  `three_le_of_occ` and `occ_lt`.
- Lemmas 1 and 2: `not_occ_pair_of_close` and `not_occ_pair_of_far`.
- (A076-14) and the coverage statement: `pair_geometry` and
  `pair_covered`.
- (A076-15): `a_le_two`, stated for the upstream `a` itself.
- `a_eq_countP`: the upstream count `a n` equals the number of window
  positions with \(W_u(n^2;L)=n\).
- `reduction` and `a_le_one_of_search`, which combine all of the above.

`a_le_one_of_search` derives \(a(n)\le1\) for all \(n<2^N\) from one
hypothesis. For every \(L\le N\), every odd \(k\) of bit length \(L\) that
occurs at a reduced-plan position must occur nowhere else.

The module does not formalize the following:

- the completeness of the bottom and top methods (§8.2);
- the programs;
- their outputs.

### 8.6 Results

The committed logs in [`logs/`](logs/) record the following runs. The
enumerators used 3 threads and the brute-force run used 1 thread, on a shared
Apple M5 Max (arm64) with a load average of 60–90 on 18 cores.

| Log | Program | Mode | `L` | Bottom candidates | Top candidates | Occurrences | Counterexamples | Wall (s) | User CPU (s) |
|---|---|---|---|---:|---:|---:|---:|---:|---:|
| [`p_full_L3-64.log`](logs/p_full_L3-64.log) | P | full | 3–64 | 6,442,450,879 | 6,442,450,878 | 514 | 0 | 433.23 | 800.10 |
| [`q_full_L3-64.log`](logs/q_full_L3-64.log) | Q | full | 3–64 | 6,442,450,879 | 6,442,450,878 | 514 | 0 | 331.35 | 581.79 |
| [`p_red_L3-96.log`](logs/p_red_L3-96.log) | P | reduced | 3–96 | 8,589,934,495 | 3,221,225,378 | 737 | 0 | 422.68 | 658.38 |
| [`q_red_L3-96.log`](logs/q_red_L3-96.log) | Q | reduced | 3–96 | 8,589,934,495 | 3,221,225,378 | 737 | 0 | 1026.44 | 1585.17 |
| [`p_red_L97-100.log`](logs/p_red_L97-100.log) | P | reduced | 97–100 | 12,884,901,884 | 4,831,838,204 | 73 | 0 | 571.47 | 993.95 |
| [`q_red_L97-100.log`](logs/q_red_L97-100.log) | Q | reduced | 97–100 | 12,884,901,884 | 4,831,838,204 | 73 | 0 | 1099.56 | 2498.56 |
| [`bf_L3-34.log`](logs/bf_L3-34.log) | BF | brute force | 3–34 | 8,589,934,590 odd `n` | — | 146 | 0 | 1067.06 | 551.09 |

Every run exited with status \(0\) and reported `counterexamples=0`, and
every \(n\) found has exactly one occurrence. In each mode, P and Q print
identical per-\(L\) lines and identical occurrence lists. The full-mode lists
for \(L\le34\) equal the brute-force list (146 occurrences). On
\(3\le L\le64\), the reduced-mode lists equal the full-mode lists restricted
to the reduced positions. `python3 a076141_crosscheck.py --logs logs/*.log`
re-checks all of these facts, including the SHA-256 of each occurrence list.
