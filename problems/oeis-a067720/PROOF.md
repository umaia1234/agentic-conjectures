**English** | [한국어](PROOF.ko.md)

# A prime-power partial theorem for OEIS A067720

## Problem and theorem

Consider the following equation.

\[
\varphi(k^2+1)=k\varphi(k+1). \tag{1}
\]

**Theorem.**

Assume

\[
k+1=p^a,\qquad p\text{ prime},\qquad a\ge2
\]

1. If \(p=2\), then (1) has no solution.
2. If \(p\) is odd and
   \[
   V:=v_2(p^a-1)+v_2(p-1)\le5
   \]
   then the unique solution is
   \[
   (p,a,k)=(3,2,8)
   \]

This theorem does not treat every composite \(k+1\), and it also leaves
the cases with odd \(p\) and \(V\ge6\).

## Excluding \(p=2\)

\[
k=2^a-1
\]

is odd, and in

\[
M:=k^2+1=2N
\]

\(N\) is odd. Hence

\[
\varphi(M)=\varphi(2N)=\varphi(N)\le N=\frac{k^2+1}{2}.
\]

Since \(a\ge2\), we have \(k>1\) and

\[
\frac{k^2+1}{2}<\frac{k(k+1)}2=k\varphi(2^a).
\]

Hence (1) cannot hold.

## Structure of \(M=k^2+1\) for odd \(p\)

Now let \(p\) be odd. If \(M=k^2+1\) were prime, then

\[
\varphi(M)=M-1=k^2.
\]

Dividing (1) by \(k\),

\[
p^a-1=p^{a-1}(p-1),
\]

i.e. \(p^{a-1}=1\), a contradiction. Hence \(M\) is composite.

Moreover \(\gcd(M,k)=1\). Since \(k\equiv-1\pmod p\),

\[
M=k^2+1\equiv2\pmod p,
\]

so \(\gcd(M,p)=1\). Since \(p-1\mid k\),

\[
M\equiv1\pmod{p-1},
\]

so \(\gcd(M,p-1)=1\). Meanwhile the right-hand side of (1) is

\[
k\varphi(p^a)=kp^{a-1}(p-1).
\]

Therefore

\[
\gcd(M,\varphi(M))=1. \tag{2}
\]

If \(q^2\mid M\) for some prime \(q\), then \(q\mid\varphi(M)\) also
holds, contradicting (2). Hence \(M\) is squarefree.

Since \(p\) is odd, \(k=p^a-1\) is even and \(M\) is odd. Also, if
\(q\mid M\), then

\[
k^2\equiv-1\pmod q.
\]

Since \(q\) is odd and \(-1\) is a quadratic residue modulo \(q\),

\[
q\equiv1\pmod4. \tag{3}
\]

Hence, writing \(\omega(M)\) for the number of distinct prime factors
of \(M\),

\[
v_2(\varphi(M))
=\sum_{q\mid M}v_2(q-1)
\ge2\omega(M). \tag{4}
\]

On the other hand, from (1),

\[
v_2(\varphi(M))
=v_2(k)+v_2(p-1)
=v_2(p^a-1)+v_2(p-1)=V. \tag{5}
\]

Since \(V\le5\), \(2\omega(M)\le5\). \(M\) is a composite squarefree
number, so \(\omega(M)\ge2\), and consequently \(\omega(M)=2\). Hence
for distinct odd primes \(q\le r\),

\[
M=qr. \tag{6}
\]

## Sum and product of the two prime factors

Set

\[
h:=p^{a-1}-1,\qquad S:=q+r
\]

From (6),

\[
\varphi(M)=(q-1)(r-1)=qr-q-r+1=k^2+2-S.
\]

Using (1) and \(k=p^a-1\),

\[
k^2+2-S=kp^{a-1}(p-1).
\]

Therefore

\[
\begin{aligned}
S
&=k^2-kp^{a-1}(p-1)+2\\
&=k\bigl((p^a-1)-p^{a-1}(p-1)\bigr)+2\\
&=k(p^{a-1}-1)+2=kh+2.
\end{aligned}
\]

Consequently

\[
q+r=kh+2,
\qquad qr=k^2+1. \tag{7}
\]

## Inequalities between the integer roots

Set

\[
f(x):=x(S-x)
\]

Then \(f(q)=qr=k^2+1\). Since \(q\le r\), we have \(q\le S/2\), and
\(f\) is strictly increasing on \([0,S/2]\).

Since \(p\ge3, a\ge2\), we have \(k\ge p^2-1\), \(h\ge p-1\), and

\[
\begin{aligned}
S-2(p+2)
&=kh+2-2(p+2)\\
&\ge(p^2-1)(p-1)+2-2(p+2)\\
&=p^3-p^2-3p-1>0.
\end{aligned} \tag{8}
\]

Hence \(p,p+1,p+2\) are all smaller than \(S/2\).

Setting

\[
z:=p^{a-1}
\]

we have \(k=pz-1\), \(h=z-1\). Direct expansion gives

\[
f(p)-(k^2+1)=-(p-1)(pz+p-2)<0. \tag{9}
\]

### The case \(a\ge3\)

In this case \(z\ge p^2\) and

\[
f(p+1)-(k^2+1)=pz^2-p^2z-z-p^2+p. \tag{10}
\]

Writing \(g(z)\) for the right-hand side,

\[
g'(z)=2pz-p^2-1>0\qquad(z\ge p^2,\ p\ge3).
\]

Hence \(g\) is increasing on this range, and

\[
g(p^2)=p(p^4-p^3-2p+1)>0.
\]

Therefore

\[
f(p)<k^2+1<f(p+1).
\]

Since \(f\) is strictly increasing on \([0,S/2]\) and \(f(q)=k^2+1\),
we would need \(p<q<p+1\), which is impossible for an integer \(q\).

### The case \(a=2\)

In this case \(z=p\), and direct expansion gives

\[
f(p+1)-(k^2+1)=-p^2<0, \tag{11}
\]

\[
f(p+2)-(k^2+1)=p(p-3)(p+1). \tag{12}
\]

If \(p>3\), then

\[
f(p+1)<k^2+1<f(p+2),
\]

so \(p+1<q<p+2\), a contradiction. If \(p=3\), then (12) is \(0\), so

\[
q=5,\qquad r=13,\qquad k=3^2-1=8.
\]

Indeed,

\[
\varphi(8^2+1)=\varphi(65)=48=8\varphi(9).
\]

This proves the theorem.
