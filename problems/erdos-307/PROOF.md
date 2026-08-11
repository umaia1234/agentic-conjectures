# Audited necessary conditions for Erdős problem #307

Let

\[
 \sigma(S)=\sum_{s\in S}\frac1s,\qquad
 M(S)=\prod_{s\in S}s,\qquad
 A(S)=\sum_{s\in S}\frac{M(S)}s.
\]

Unless explicitly labelled as a composite toy, every set below is a finite set
of primes.  Put `U=P union Q` and `N=M(U)`.

## 1. Reduced fractions and forcing

For every prime `r` in `S`, reduction modulo `r` gives

\[
 A(S)\equiv \frac{M(S)}r\not\equiv0\pmod r.
\]

Indeed, every summand indexed by `s != r` contains the factor `r`, while the
remaining summand does not.  Since the prime divisors of `M(S)` are precisely
the members of `S`, this proves

\[
 \gcd(A(S),M(S))=1.
\]

Thus `sigma(S)=A(S)/M(S)` is already reduced.  If
`sigma(P)sigma(Q)=1`, then

\[
 A(P)A(Q)=M(P)M(Q).
\]

Coprimality gives `A(P)|M(Q)` and `A(Q)|M(P)`.  Write
`M(Q)=A(P)a` and `M(P)=A(Q)b` with positive integers `a,b`.  Substitution
gives `ab=1`, hence

\[
 \boxed{A(P)=M(Q),\qquad A(Q)=M(P).}
\]

Conversely these identities imply the original equation.  If a prime `r`
belonged to both sets, then `r|M(Q)=A(P)`, contradicting
`gcd(A(P),M(P))=1`; consequently `P` and `Q` are disjoint.

This forcing result is not new: it appears as Theorem 4.1 in Bado's May 2026
author-uploaded preprint cited in `README.md`.

## 2. The local square condition

Fix `r in P`.  Reducing `A(P)=M(Q)` modulo `r` yields

\[
 M(Q)\equiv \frac{M(P)}r\pmod r.
\]

Multiplication by `M(Q)` gives the stronger partition-free statement

\[
 \frac Nr\equiv M(Q)^2\pmod r.
\]

For `r in Q` the same argument gives `N/r congruent M(P)^2 (mod r)`.
Therefore, for every odd `r in U`,

\[
 \boxed{\left(\frac{N/r}{r}\right)=1.}\tag{L_r}
\]

Here the symbol is Legendre's.  Its numerator is nonzero modulo `r` because
`N` is squarefree.

There is **no Legendre symbol at `r=2`**.  If `2 in U`, the corresponding
cross-product congruence merely says that two odd integers are congruent
modulo 2; equivalently `N/2 congruent 1 (mod 2)`.  It supplies no sign.

The family `(L_r)` is substantially stronger than either aggregate condition
in the next section and is the filter used by `enumerate_59.py`.

## 3. Quadratic-reciprocity product, with the `p=2` audit

Let

\[
 u=\#\{r\in U\setminus\{2\}:r\equiv3\pmod4\},
\]

and, when `2 in U`, let

\[
 v=\#\{r\in U\setminus\{2\}:r\equiv3\text{ or }5\pmod8\}.
\]

Multiply `(L_r)` over all odd `r in U`.  For each unordered pair of distinct
odd primes `{r,s}`, quadratic reciprocity contributes

\[
 \left(\frac{s}{r}\right)\left(\frac{r}{s}\right)
 =(-1)^{((r-1)/2)((s-1)/2)}.
\]

This is `-1` exactly when both primes are `3 mod 4`, so all odd--odd pairs
contribute `(-1)^(binom(u,2))`.

If `2 notin U`, there are no further factors.  Hence

\[
 1=(-1)^{\binom u2},
\]

or equivalently

\[
 \boxed{u\equiv0\text{ or }1\pmod4.}
\]

If `2 in U`, the numerator `N/r` in every odd-denominator symbol also
contains 2.  The supplementary law

\[
 \left(\frac2r\right)=(-1)^{(r^2-1)/8}
\]

is negative exactly for `r congruent 3,5 (mod 8)`.  Thus these factors
contribute `(-1)^v`, and

\[
 \boxed{v+\binom u2\equiv0\pmod2.}
\]

This derivation is also valid, with Jacobi symbols, for pairwise-coprime odd
composite moduli.  `test_identities.py` checks both versions independently.

## 4. Parity and stronger mod-8 conditions

The forcing identities immediately give the known parity restrictions.

- If `2 notin U`, every summand of `A(P)` and `A(Q)` is odd, while both
  opposite products are odd.  Hence both `|P|` and `|Q|` are odd.
- If `2 in P`, then `A(Q)=M(P)` is even and every summand of `A(Q)` is odd,
  so `|Q|` is even.  The case `2 in Q` is symmetric.  No parity for the set
  containing 2 follows from this argument.

Every odd residue is its own inverse modulo 8.  If `2 notin U`, put
`T=M(U) mod 8`.  Dividing `A(P)=M(Q)` by the odd number `M(P)` modulo 8 gives

\[
 \boxed{\sum_{p\in P}p\equiv T\pmod8,qquad
        \sum_{q\in Q}q\equiv T\pmod8.}\tag{8a}
\]

In particular, the following union-only condition is necessary:

\[
 \boxed{\sum_{r\in U}r\equiv2M(U)\pmod8.}\tag{8b}
\]

Now suppose `2 in P` (the other orientation is symmetric), set
`P_0=P-{2}`, and put `T=M(U-{2}) mod 8`.  Expanding the term indexed by 2
separately gives

\[
 \boxed{1+2\sum_{p\in P_0}p\equiv T\pmod8,qquad
        \sum_{q\in Q}q\equiv2T\pmod8.}\tag{8c}
\]

After adding these relations in the appropriate doubled form, if
`S=sum_{r in U-{2}} r`, then

\[
 \boxed{2S\equiv5T-1\pmod8.}\tag{8d}
\]

An equivalent audit comes from the exact union identity

\[
 A(U)=M(P)^2+M(Q)^2.
\]

When 2 is absent the right side is `2 mod 8`; when 2 is present it is
`4+1=5 mod 8`.  Computing `A(U)` term by term gives exactly `(8b)` and
`(8d)`.

## 5. A mod-24 lift when 3 is absent

Every unit modulo 24 is self-inverse.  Therefore the preceding calculation
lifts verbatim from modulo 8 to modulo 24 whenever `3 notin U`.

- If neither 2 nor 3 is in `U`, with `T=M(U) mod 24`,

  \[
  \sum_{p\in P}p\equiv\sum_{q\in Q}q\equiv T\pmod{24},
  \qquad \sum_{r\in U}r\equiv2T\pmod{24}.
  \]

- If `2 in U` but `3 notin U`, put
  `T=M(U-{2}) mod 24` and `S=sum_{r in U-{2}}r`.  Then

  \[
  1+2S\equiv5T\pmod{24}.
  \]

  More precisely, the side not containing 2 has sum congruent to `2T`, and
  if `H` is the odd part of the side containing 2 then
  `1+2 sum_{h in H}h congruent T (mod 24)`.

The exclusion of 3 is essential: division modulo 24 would otherwise be
invalid.

## 6. Exact exclusion of a 59-prime union

For positive `x,y` with `xy=1`, AM--GM gives `x+y>=2`.  Consequently any
solution satisfies

\[
 \sum_{r\in U}\frac1r\ge2.
\]

The sum of the reciprocals of the first 58 primes (through 271) is
approximately `1.9987400431470443`, whereas the first 59 (through 277) sum
to approximately `2.0023501514502935`.  Thus the analytic argument alone
only gives `|U|>=59`.  A 59-prime candidate must contain 2, since the largest
possible reciprocal sum of 59 primes not containing 2 (the primes from 3
through 281) is less than 2.

`enumerate_59.py` rigorously excludes equality.  Let `B` be the first 59
primes and `Delta=sum(B^{-1})-2`.  Every 59-prime set is uniquely obtained
by deleting `k` members of `B` and adding `k` primes greater than 277.  The
smallest possible reciprocal loss for `k` replacements is obtained by
deleting the `k` largest primes of `B` and adding the `k` smallest primes
outside `B`.  The loss is strictly increasing in `k`, and its value for
`k=6` already exceeds `Delta`; hence only `0<=k<=5` are possible.

For each such `k`, the code derives an exact finite upper bound on the largest
added prime.  If the added primes are `a_1<...<a_k`, their first `k-1`
reciprocals are at most those of the first `k-1` primes after 277.  The
remaining required reciprocal mass therefore gives an explicit positive
lower bound on `1/a_k`.  All comparisons and all subset sums use Python's
arbitrary-precision `Fraction`, not floating point.

The exhaustive counts are:

| replacements | sum at least 2 | mod 8 | aggregate QR | all local symbols |
|---:|---:|---:|---:|---:|
| 0 | 1 | 0 | 0 | 0 |
| 1 | 701 | 176 | 89 | 0 |
| 2 | 11,902 | 2,967 | 1,462 | 0 |
| 3 | 27,071 | 6,783 | 3,356 | 0 |
| 4 | 9,915 | 2,485 | 1,205 | 0 |
| 5 | 371 | 82 | 37 | 0 |
| total | 49,961 | 12,493 | 6,149 | 0 |

No candidate satisfies every `(L_r)`.  Therefore

\[
 \boxed{|P\cup Q|\ge60.}
\]

The current Erdős Problems page already states this bound, so it is not
claimed here as new.  The computation supplies a reproducible exact route
that also resolves the apparent gap between the raw reciprocal-sum threshold
59 and the stated bound 60.

### Bounded support

The cardinality result makes a second finite check possible.  If every prime
in `U` were at most 317, then `U` would be a subset of the first 66 primes;
since `|U|>=60`, it would be obtained by removing at most six of them.
Moreover its reciprocal sum can be at least 2 only when the removed reciprocal
mass is at most the exact excess of the full 66-prime sum over 2.

`enumerate_bounded_union.py` enumerates all 644,666 such subsets exactly.
Of these, 161,106 pass the union mod-8 condition and 58,389 also pass the
aggregate reciprocity condition.  None of the latter passes every individual
local Legendre condition.  Therefore the computation also gives

\[
\boxed{\max(P\cup Q)\ge331,}
\]

because 331 is the next prime after 317.

The same argument can be extended.  `enumerate_bounded_support_fast.py`
caches, for every possible removed numerator, the bitset of odd denominators
whose Legendre sign it toggles.  This is exactly the identity

\[
 \prod_{s\in F\setminus(R\cup\{r\})}\left(\frac{s}{r}\right)
 =\prod_{s\in F\setminus\{r\}}\left(\frac{s}{r}\right)
  \prod_{s\in R}\left(\frac{s}{r}\right),
\]

since every factor is `+1` or `-1`.  For the first 68 primes, through 337,
the reciprocal and cardinality conditions leave 9,926,250 subsets.  Of these,
2,482,194 pass mod 8 and 1,140,196 also pass aggregate reciprocity.  None
passes all local symbols.  As 347 is the next prime after 337, this gives the
stronger finite computational bound

\[
 \boxed{\max(P\cup Q)\ge347.}
\]

At 66 primes the cached implementation reproduces every count from the slow
product-based implementation; at 67 it reproduces a complete slow run, and
5,000 deterministic 68-prime subsets were checked by both symbol formulas.
This remains a finite, inspectable computer exclusion, not a nonexistence
theorem and not a claim of novelty.

## 7. Scope

None of these conditions proves nonexistence, and no solution was found.
The individual local square conditions are stronger than their reciprocity
product, while the mod-8/mod-24 conditions are independent inexpensive
filters.  The literature search in `README.md` did not locate these exact
Legendre or mod-24 formulations, but a negative search is not a novelty
proof.
