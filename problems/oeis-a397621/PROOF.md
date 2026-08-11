**English** | [한국어](PROOF.ko.md)

# OEIS A397621 — Detailed Proof of the Pascal mod 2 Linear Complexity

This document is the canonical proof, consolidated per problem, of the
detailed proof written on 2026-08-11 together with the follow-up
mathematical audit. The finite computational certificate does not
replace the proof; its only role is to independently recheck the
definitions, boundary values, and derived identities.

## 3.1. Linear complexity of a finite binary word

Let a finite binary word be

\[
\mathbf{s}=(s_0,s_1,\ldots,s_n)\in\mathbf F_2^{\,n+1}.
\]

Here \(\mathbf F_2=\{0,1\}\) and all additions and multiplications are
computed mod \(2\).

That this word satisfies a linear recurrence of length, or span, \(L\)
means that there exist some

\[
c_1,\ldots,c_L\in\mathbf F_2
\]

such that

\[
s_i+c_1s_{i-1}+c_2s_{i-2}+\cdots+c_Ls_{i-L}=0
\tag{3.1}
\]

holds for all \(i=L,L+1,\ldots,n\). The linear complexity
\(\operatorname{LC}(\mathbf s)\) of the word is the smallest such \(L\).

When \(L=0\), (3.1) is simply the condition

\[
s_i=0\qquad(0\le i\le n).
\]

Hence only the zero word has linear complexity \(0\), and the linear
complexity of a nonzero word is at least \(1\).

The characteristic polynomial of the recurrence (3.1) is

\[
\chi_L(z)=z^L+c_1z^{L-1}+\cdots+c_L,
\]

and the reciprocal connection polynomial, convenient when using
multiplication, is

\[
C_L(x)=1+c_1x+\cdots+c_Lx^L
      =x^L\chi_L(x^{-1}).
\tag{3.2}
\]

For a finite word we may have \(c_L=0\), so the actual polynomial degree
of \(C_L(x)\) can be smaller than \(L\). The quantity minimized here is
the recurrence span \(L\) returned by the Berlekamp--Massey algorithm.
The lower bound below places no condition on \(c_L\) and rules out all
\(L<d\), and the polynomial used for the upper bound also has actual
degree exactly \(d\), so this matter of convention does not affect the
final conclusion.

## 3.2. Exact equivalence of the recurrence and the polynomial product condition

Let the position generating polynomial of the word \(\mathbf s\) be

\[
S(x)=\sum_{i=0}^{n}s_ix^i.
\tag{3.3}
\]

Setting \(c_0=1\),

\[
\begin{aligned}
[x^i]\bigl(C_L(x)S(x)\bigr)
 &=\sum_{j=0}^{\min(i,L)}c_js_{i-j}.
\end{aligned}
\]

In particular, if \(L\le i\le n\), then

\[
[x^i]\bigl(C_LS\bigr)
 =s_i+c_1s_{i-1}+\cdots+c_Ls_{i-L}.
\tag{3.4}
\]

Therefore the recurrence (3.1) of length \(L\) holds if and only if

\[
[x^i]\bigl(C_L(x)S(x)\bigr)=0
\qquad(L\le i\le n).
\tag{3.5}
\]

It is important here that the range is exactly \(L\le i\le n\).

- The coefficients with \(i<L\) involve the first \(L\) initial values,
  so they need not be 0.
- The coefficients with \(i>n\) concern how the given finite word is
  extended beyond its end, so they carry no condition either.
- Therefore all of \(C_LS\) need not be 0; only the coefficients of the
  middle range \(L,\ldots,n\) corresponding to the observed word must
  be 0.

## 3.3. The binary word of A001317 and the Pascal coefficient polynomial

Set the following.

\[
b_k=\binom nk\bmod 2,\qquad 0\le k\le n.
\]

The \(n\)-th term of A001317 is the integer obtained by reading these
bits as a binary number, and can be written as

\[
\operatorname{A001317}(n)=\sum_{k=0}^{n}b_k2^k.
\tag{3.6}
\]

The two end coefficients are

\[
b_0=b_n=1,
\]

so the binary representation of this integer has no leading zeros and
has length exactly \(n+1\).

The MSB-first binary word of the integer is originally

\[
(b_n,b_{n-1},\ldots,b_0).
\]

However, by the symmetry of the binomial coefficients,

\[
b_{n-k}=\binom n{n-k}\bmod2
       =\binom nk\bmod2=b_k,
\]

so this word is exactly equal to

\[
(b_0,b_1,\ldots,b_n).
\]

Therefore, writing the position generating polynomial (3.3) for the word
in the MSB-first orientation that A397621 requires,

\[
S_n(x)=\sum_{k=0}^{n}b_kx^k=(1+x)^n
\quad\text{in }\mathbf F_2[x].
\tag{3.7}
\]

That is, using \(S_n(x)=(1+x)^n\) below is not a reversal of the bit
order. Because the Pascal row itself is a palindrome, the MSB-first word
coincides with the coefficient sequence listed from the lowest degree.

## 3.4. Main theorem

**Theorem 3.1.** For all \(n\ge1\),

\[
\operatorname{A397621}\bigl(\operatorname{A001317}(n)\bigr)
 =2^{\lfloor\log_2n\rfloor+1}-n.
\tag{3.8}
\]

Therefore

\[
\operatorname{A397621}\bigl(\operatorname{A001317}(n)\bigr)
 =\operatorname{A080079}(n).
\tag{3.9}
\]

**Proof.** Fix \(n\ge1\) and set

\[
h=\lfloor\log_2n\rfloor,\qquad q=2^h.
\]

Then

\[
q\le n<2q.
\]

For a unique \(r\) we can write

\[
n=q+r,\qquad 0\le r<q.
\tag{3.10}
\]

Denote the linear-complexity value to be proved by

\[
d=q-r=2q-n.
\tag{3.11}
\]

Since \(0\le r<q\),

\[
1\le d\le q\le n.
\tag{3.12}
\]

Hence the recurrence of length \(d\) constructed below is not a
recurrence holding vacuously, but one actually applied within the given
word.

### 3.4.1. The zero run appearing in the Pascal row

In characteristic \(2\), by the Frobenius identity,

\[
(1+x)^q=1+x^q.
\tag{3.13}
\]

Indeed, since \(q=2^h\), the middle binomial coefficients are all even.
Using (3.7), (3.10), (3.13),

\[
\begin{aligned}
S_n(x)
  &=(1+x)^n\\
  &=(1+x)^{q+r}\\
  &=(1+x)^q(1+x)^r\\
  &=(1+x^q)(1+x)^r.
\end{aligned}
\tag{3.14}
\]

Writing \(P_r(x)=(1+x)^r\), we have \(\deg P_r=r<q\) and

\[
S_n(x)=P_r(x)+x^qP_r(x).
\tag{3.15}
\]

The support of the first block \(P_r\) lies within degrees
\(0,\ldots,r\), and the support of the second block \(x^qP_r\) lies
within degrees \(q,\ldots,q+r=n\). Therefore, between the two blocks,

\[
[x^i]S_n(x)=0\qquad(r+1\le i\le q-1).
\tag{3.16}
\]

Moreover, since the constant term of \(P_r\) is 1, the first coefficient
of the second block is

\[
[x^q]S_n(x)=1.
\tag{3.17}
\]

That is, immediately before the 1 at position \(q\) there are
consecutive 0s at positions

\[
r+1,r+2,\ldots,q-1.
\]

The length of this zero run is

\[
q-r-1=d-1.
\tag{3.18}
\]

### 3.4.2. Lower bound \(\operatorname{LC}(S_n)\ge d\)

Suppose, to the contrary, that a recurrence with \(L<d\) exists. Since
\(L\) is an integer,

\[
0\le L\le d-1.
\tag{3.19}
\]

Also, since \(d\le q\le n\),

\[
L\le q\le n.
\]

Hence the recurrence (3.1) can be applied at position \(i=q\).

For each \(j=1,\ldots,L\), from (3.19),

\[
q-j\ge q-L\ge q-(d-1)=r+1,
\]

and trivially \(q-j\le q-1\). Therefore, by (3.16),

\[
s_{q-j}=0\qquad(1\le j\le L).
\tag{3.20}
\]

On the other hand, by (3.17), \(s_q=1\). At position \(q\) the left-hand
side of the recurrence would be

\[
s_q+c_1s_{q-1}+\cdots+c_Ls_{q-L}
 =1+c_1\cdot0+\cdots+c_L\cdot0
 =1,
\]

but the recurrence requires this to be 0. Since \(1\ne0\) also in
\(\mathbf F_2\), this is a contradiction.

This argument includes \(L=0\) as well. In that case the sum is empty
and the condition at position \(q\) is precisely \(s_q=0\), whereas in
fact \(s_q=1\). Therefore all \(L<d\) are ruled out and

\[
\operatorname{LC}(S_n)\ge d.
\tag{3.21}
\]

### 3.4.3. Upper bound \(\operatorname{LC}(S_n)\le d\)

Now we explicitly choose the following connection polynomial.

\[
C_d(x)=(1+x)^d.
\tag{3.22}
\]

Since both the constant term and the leading term are 1, this is a
legitimate connection polynomial of actual degree exactly \(d\). By
(3.7) and (3.11),

\[
\begin{aligned}
C_d(x)S_n(x)
  &=(1+x)^d(1+x)^n\\
  &=(1+x)^{n+d}\\
  &=(1+x)^{(q+r)+(q-r)}\\
  &=(1+x)^{2q}.
\end{aligned}
\tag{3.23}
\]

Since \(2q=2^{h+1}\) is also a power of 2, applying the Frobenius
identity again gives

\[
C_d(x)S_n(x)=1+x^{2q}.
\tag{3.24}
\]

But

\[
n=q+r\le2q-1,
\]

so the coefficients of degrees \(d,d+1,\ldots,n\) of \(1+x^{2q}\) are
all 0. That is,

\[
[x^i]\bigl(C_dS_n\bigr)=0
\qquad(d\le i\le n).
\tag{3.25}
\]

By the equivalence of Section 3.2, the coefficient sequence of \(S_n\)
satisfies a recurrence of length \(d\). The coefficients of the concrete
recurrence are

\[
c_j=\binom dj\bmod2,\qquad 1\le j\le d.
\]

Therefore

\[
\operatorname{LC}(S_n)\le d.
\tag{3.26}
\]

Combining (3.21) and (3.26),

\[
\operatorname{LC}(S_n)=d=2q-n
 =2^{\lfloor\log_2n\rfloor+1}-n.
\tag{3.27}
\]

Finally, A080079 is the distance to the nearest power of 2 greater than
\(n\). From \(q\le n<2q\) that power of 2 is \(2q\), so

\[
\operatorname{A080079}(n)=2q-n=d.
\tag{3.28}
\]

Therefore (3.9) holds for all \(n\ge1\). \(\square\)

## 3.5. Boundary case checks

That there are no exceptions hidden in the above proof can be confirmed
directly as follows.

### (i) Minimal input \(n=1\)

In this case

\[
q=1,\qquad r=0,\qquad d=1.
\]

The Pascal row is \((1,1)\) and

\[
S_1(x)=1+x.
\]

A recurrence of length \(0\) is impossible for a nonzero word, and

\[
(1+x)S_1(x)=(1+x)^2=1+x^2,
\]

so a recurrence of length \(1\) exists. Therefore the complexity is
exactly 1.

### (ii) The case where \(n\) is a power of 2

If \(n=q\), that is \(r=0\), then

\[
d=q,\qquad S_q(x)=1+x^q.
\]

Positions \(1,\ldots,q-1\) are all 0 and position \(q\) is 1, so a
recurrence of length \(L<q\) cannot produce the 1 at position \(q\). On
the other hand,

\[
(1+x)^qS_q(x)
 =(1+x^q)^2
 =1+x^{2q},
\]

so length \(q\) is possible. Therefore

\[
\operatorname{LC}(S_q)=q.
\]

In particular, in A080079 the next power of 2 **strictly greater** than
\(q\) is \(2q\), so this agrees with
\(\operatorname{A080079}(q)=2q-q=q\).

### (iii) The right end of the interval, \(n=2q-1\)

In this case

\[
r=q-1,\qquad d=1.
\]

The zero run \(r+1,\ldots,q-1\) is an empty interval, but the
lower-bound argument is unaffected. The only value to be ruled out is
\(L<1\), i.e. \(L=0\), which is impossible because the word is nonzero.

Also,

\[
(1+x)S_{2q-1}(x)
 =(1+x)^{2q}
 =1+x^{2q},
\]

so a recurrence of length \(1\) exists. Indeed,

\[
S_{2q-1}(x)=1+x+x^2+\cdots+x^{2q-1},
\]

so the bits are all 1 and satisfy the recurrence \(s_i+s_{i-1}=0\).
Therefore the complexity is exactly 1.

### (iv) MSB-first orientation and leading zeros

Each term of A001317 has \(b_n=1\), so the binary number has length
exactly \(n+1\) and deletion of leading zeros does not change the word
length. Moreover, since \(b_k=b_{n-k}\), the MSB-first and the reverse
orientation are identical. Hence there is no exception due to the choice
of orientation either.

### (v) \(n=0\)

The range of the theorem is \(n\ge1\). This is because the official
starting index of A080079 is 1, and \(n\ge1\) is also needed in the
proof to define \(q=2^{\lfloor\log_2n\rfloor}\). Therefore \(n=0\) is
not a missing boundary but outside the range of the original statement.

## 3.6. Example: \(n=5\)

If \(n=5\), then

\[
q=4,\qquad r=1,\qquad d=3.
\]

Therefore

\[
S_5(x)=(1+x)^5=1+x+x^4+x^5.
\]

The coefficient sequence is

\[
(1,1,0,0,1,1),
\]

and immediately before the 1 at position \(4\) there are \(d-1=2\)
zeros. Hence recurrences of lengths \(0,1,2\) all fail at position
\(4\). On the other hand, for

\[
C_3(x)=(1+x)^3=1+x+x^2+x^3
\]

we have

\[
C_3(x)S_5(x)=(1+x)^8=1+x^8.
\]

The coefficients of degrees \(3,4,5\) are all 0, so a recurrence of
length \(3\) exists. Therefore the linear complexity is exactly

\[
3=8-5=\operatorname{A080079}(5).
\]
