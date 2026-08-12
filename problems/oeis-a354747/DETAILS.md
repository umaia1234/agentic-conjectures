**English** | [한국어](DETAILS.ko.md)

# OEIS A354747: \(a(100943)=39101\)

## 1. Closed Form of the Recurrence

Let the initial value and the recurrence be

\[
x_0=2n-1,\qquad x_{m+1}=3x_m+2
\]

Setting \(y_m=x_m+1\) gives

\[
y_{m+1}=3y_m,\qquad y_0=2n
\]

so

\[
\boxed{x_m=2n3^m-1}.
\]

Therefore, for \(n=100943\), the numbers to be examined are

\[
T_m=201886\cdot3^m-1
\]

The proposition to be proved is that

\[
T_{39101}\text{ is prime},\qquad
T_m\text{ is composite for all }1\le m<39101
\]

## 2. The Prime Candidate and the Lucas Sequence

We set the following.

\[
N=T_{39101}=201886\cdot3^{39101}-1,
\]

\[
A=N+1=2\cdot100943\cdot3^{39101}.
\]

Since \(\sqrt{100943}<318\) and trial division by every prime up to 317
yields no divisor, \(100943\) is prime. Therefore

\[
\boxed{A=2^1\,3^{39101}\,100943^1}
\]

is the complete prime factorization of \(A\).

We define the Lucas sequence by

\[
U_0=0,\qquad U_1=1,\qquad
U_{k+2}=8U_{k+1}-5U_k
\]

The parameters are \((P,Q)=(8,5)\), and the discriminant is

\[
\Delta=P^2-4Q=44
\]

## 3. Lucas Rank Lemma

**Lemma.** Suppose an odd prime \(\ell\) does not divide \(2Q\Delta\).
If \(z_\ell\) denotes the smallest positive integer \(k\) such that
\(\ell\mid U_k\), then

\[
\boxed{z_\ell\mid \ell-\left(\frac{\Delta}{\ell}\right)}.
\]

Here the parenthesized symbol is the Legendre symbol. In particular,
\(z_\ell\le\ell+1\).

**Proof.** Let \(\alpha,\beta\) be the two roots in
\(\mathbb F_{\ell^2}\) of the polynomial

\[
X^2-PX+Q
\]

Since \(\ell\nmid Q\Delta\), the two roots are distinct and nonzero. In the
Binet formula

\[
U_k=\frac{\alpha^k-\beta^k}{\alpha-\beta}
\]

setting \(\gamma=\alpha/\beta\) gives

\[
U_k\equiv0\pmod\ell
\quad\Longleftrightarrow\quad
\gamma^k=1.
\]

Therefore \(z_\ell\) is the multiplicative order of \(\gamma\) in the finite
group \(\mathbb F_{\ell^2}^{\times}\).

- If \(\left(\frac{\Delta}{\ell}\right)=1\), both roots lie in
  \(\mathbb F_\ell\), so \(\gamma^{\ell-1}=1\).
- If \(\left(\frac{\Delta}{\ell}\right)=-1\), the Frobenius map swaps the
  two roots, so

  \[
  \gamma^\ell=\frac{\beta}{\alpha}=\gamma^{-1},
  \]

  and therefore \(\gamma^{\ell+1}=1\).

Combining the two cases yields the claimed divisibility relation. \(\square\)

## 4. Deterministic Primality Certification

The following relations were verified by exact integer modular arithmetic.

\[
\gcd(2Q\Delta,N)=1,
\]

\[
U_A\equiv0\pmod N,
\]

\[
\gcd(U_{A/2},N)=
\gcd(U_{A/3},N)=
\gcd(U_{A/100943},N)=1.
\tag{A354-1}
\]

Let us see why these four Lucas relations prove the primality of \(N\). Let
\(\ell\) be an arbitrary prime factor of \(N\). From
\(U_A\equiv0\pmod N\) we have \(\ell\mid U_A\), so

\[
z_\ell\mid A.
\]

On the other hand, because of the gcd conditions,

\[
z_\ell\nmid A/2,\qquad
z_\ell\nmid A/3,\qquad
z_\ell\nmid A/100943.
\]

For a divisor \(z_\ell\) of \(A=2^1 3^{39101}100943^1\) to satisfy all three
conditions above, it must carry the exponents of 2, 3, and 100943 exactly as
in \(A\). That is,

\[
z_\ell=A=N+1.
\]

Applying the Lucas rank lemma,

\[
N+1=z_\ell
\mid \ell-\left(\frac{44}{\ell}\right),
\]

so \(N+1\le\ell+1\), i.e., \(\ell\ge N\). But a prime with \(\ell\mid N\)
always satisfies \(\ell\le N\), so \(\ell=N\). Since an arbitrary prime
factor of \(N\) is \(N\) itself,

\[
\boxed{N=201886\cdot3^{39101}-1\text{ is prime}.}
\]

This is not a pseudoprime test saying that \(N\) is likely prime, but a
deterministic proof applying the rank argument above to every possible prime
factor of \(N\).

### Identities for Computing Congruences at Enormous Indices

Defining the companion Lucas sequence by

\[
V_0=2,\qquad V_1=P,\qquad
V_{k+2}=PV_{k+1}-QV_k
\]

the identities

\[
U_{2k}=U_kV_k,
\]

\[
U_{3k}=U_k\bigl(V_k^2-Q^k\bigr),
\]

\[
V_{3k}=V_k\bigl(V_k^2-3Q^k\bigr)
\]

hold. First, the state at index \(100943\) can be computed exactly using the
general Lucas addition formulas or binary exponentiation of the companion
matrix

\[
\begin{pmatrix}P&-Q\\1&0\end{pmatrix}
\]

From that state, applying the tripling formulas above 39,101 times and using
the doubling formula at the end yields the values needed for \(A\),
\(A/2\), and \(A/3\). For \(A/100943\), one starts the same
tripling-and-doubling procedure from index 1. Since only the residues of all
values modulo \(N\) are kept, (A354-1) is an exact statement inside the
finite ring \(\mathbb Z/N\mathbb Z\) that does not depend on approximations
of enormous Lucas integers.

## 5. Proof That \(39101\) Is the First Index

Primality alone tells us only \(a(100943)\le39101\), not
\(a(100943)=39101\). Therefore all of

\[
T_m=201886\cdot3^m-1,\qquad 1\le m\le39100
\]

must be excluded.

### Exclusion by Small Prime Factors

For each prime \(p\le10^6\), considering

\[
r_m\equiv201886\cdot3^m\pmod p
\]

we have

\[
r_{m+1}\equiv3r_m\pmod p.
\]

Therefore every \(m\) can be examined without omission using only a finite
recurrence. If \(r_m=1\), then

\[
p\mid T_m.
\]

For \(m\ge2\), \(T_m>10^6\), so this \(p\) is a proper divisor. The case
\(m=1\) is handled separately:

\[
T_1=605657=13\cdot46589
\]

This exact sieve provided proper divisors for 37,482 of the 39,100 indices
and left 1,618.

### Fermat Compositeness Witnesses for the Remaining Terms

Each remaining \(T_m\) is odd, so \(\gcd(2,T_m)=1\). If \(T_m\) were
prime, then by Fermat's little theorem it would necessarily satisfy

\[
2^{T_m-1}\equiv1\pmod{T_m}
\]

However, exact modular exponentiation for each of the 1,618 remaining terms
verified that

\[
\boxed{2^{T_m-1}\not\equiv1\pmod{T_m}}
\]

Since this is the failure of a necessary condition, it is a deterministic
witness that each \(T_m\) is composite. The terms eliminated by small prime
factors and these 1,618 terms exactly partition \(1\le m\le39100\), so
there is no smaller prime term.

Consequently,

\[
\boxed{a(100943)=39101}.
\]
