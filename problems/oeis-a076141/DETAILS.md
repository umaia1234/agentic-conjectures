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
