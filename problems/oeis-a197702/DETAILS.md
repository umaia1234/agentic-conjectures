**English** | [한국어](DETAILS.ko.md)

# Mathematical details for OEIS A197702

## 1. Normalizing the signs

Write \(w_i=2i+1\) for \(0\le i<k\). Since

\[
\sum_{i=0}^{k-1}w_i=k^2,
\]

choosing a subset \(S\) of the indices to carry a minus sign gives

\[
\sum_{i\notin S}w_i-\sum_{i\in S}w_i
=k^2-2\sum_{i\in S}w_i.
\]

Thus \(n\) is representable at length \(k\) if and only if

\[
n+2\sum_{i\in S}w_i=k^2. \tag{2}
\]

Lean proves both the odd-sum identity and this equivalence; it does not merely
take (2) as an informal interpretation of the source.

## 2. The small subset-sum lemma

For \(k\ge1\), every \(t\) satisfying

\[
0<t<2k+1,\qquad t\ne2,
\]

is a sum of distinct elements of \(\{1,3,\ldots,2k-1\}\).

- If \(t=2r+1\), then \(r<k\), so \(t\) itself is available.
- If \(t=2r\), then \(t\ne2\) gives \(r>1\), while the upper bound gives
  \(r\le k\). Hence \(1\) and \(2r-1\) are distinct available elements and
  sum to \(t\).

The exceptional value really is impossible. If a distinct odd subset had sum
2, it could have at most two elements. It cannot be empty or a singleton. If
it had two elements, positivity forces both to be 1, contradicting
distinctness. The Lean proof carries out this cardinality argument over
`Finset (Fin k)`.

## 3. Existence in each gap class

Fix \((k-1)^2<n\le k^2\) and let \(d=k^2-n\). Equivalently,
\(0\le d<2k-1\).

### Gap zero

For \(d=0\), equation (2) holds with the empty subset, so length \(k\) works.

### Nonexceptional even gap

Suppose \(d=2r\), with \(d\ne0,4\). Then \(r>0\), \(r\ne2\), and the gap
bound puts \(r<2k+1\). The subset-sum lemma supplies sum \(r\), and (2) holds
at length \(k\).

### Odd gap

Write \(d=2r+1\). Length \(k\) is impossible because the right side of (2)
differs from \(n\) by an even number. At length \(k+1\), the needed subset
sum is

\[
t=\frac{(k+1)^2-n}{2}=k+r+1.
\]

The gap bound gives \(0<t<2(k+1)+1\), and the boundary conditions force
\(t\ne2\). The lemma therefore constructs the representation at length
\(k+1\).

### Exceptional gap four

At length \(k\), equation (2) would require subset sum 2, which is impossible.
At length \(k+1\), the total square difference is \(2k+5\), which is odd and
therefore cannot equal twice a subset sum. At length \(k+2\), the required
subset sum is

\[
\frac{(k+2)^2-n}{2}=2k+4=1+(2k+3).
\]

Both summands are among the first \(k+2\) odd numbers, so this length works.

## 4. Minimality

Every signed sum of the first \(j\) positive odd numbers is at most their
all-positive sum \(j^2\). If \(j<k\), then

\[
j^2\le(k-1)^2<n,
\]

so no such \(j\) can represent \(n\). This proves minimality immediately in
the gap-zero and nonexceptional-even cases. The parity exclusion supplies the
extra step in the odd case, and parity plus the missing subset sum 2 supply
the two extra steps in the gap-four case.

## 5. Boundary audit

- For \(k=1\), the interval permits only \(d=0\).
- For \(k=2\), it permits \(d=0,1,2\).
- The exceptional gap \(d=4\) first becomes possible at \(k=3\).

Thus the construction never calls for an unavailable index in a small case.
The Lean theorem uses natural-number inequalities throughout and checks these
boundaries in the same proof, without a separate finite computation.
