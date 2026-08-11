**English** | [한국어](README.ko.md)

# OEIS A072780: a counterexample to the Goldbach-like equivalence

## Verdict

The Goldbach-like statement on [OEIS A072780](https://oeis.org/A072780) is
**false**. The entry says, after setting \(n=m^2-r^2\), that

> “\(m-r\) and \(m+r\) are primes that add to \(2m\) if and only if
> \(a(n)=2\).”

Take \(m=8\) and \(r=7\). Then

\[
m^2-r^2=64-49=15,\qquad m-r=1,\qquad m+r=15.
\]

The positive divisors of 15 give

\[
\sigma(15)=24,\qquad \sigma_2(15)=260,\qquad \varphi(15)=8,
\]

and therefore

\[
a(15)=260+8\cdot24-2\cdot15^2=2.
\]

However, neither 1 nor 15 is prime. Thus the sequence-value side of the
claimed equivalence is true while its primality side is false.

The failure comes from nonuniqueness of a difference-of-squares
factorization. The same \(15\) is \(4^2-1^2=3\cdot5\), which explains its
sequence value, but it is also \(8^2-7^2=1\cdot15\). Knowing that a number is
a product of two distinct primes does not force every chosen factorization
\((m-r)(m+r)\) to use those primes.

## Scope and statement faithfulness

The canonical entry was checked on 2026-08-12. Revision 23 has offset 1 and
defines

\[
a(n)=\sigma_2(n)+\varphi(n)\sigma(n)-2n^2.
\]

The counterexample uses the positive input \(n=15\), so it is not an offset
or zero-boundary artifact. It also has \(m>r\), as the source requires, so
natural-number subtraction agrees with ordinary integer subtraction in both
\(m-r\) and \(m^2-r^2\).

The upstream Formal Conjectures
[source snapshot](upstream/README.md) computes the outer subtraction in
\(\mathbb Z\) and applies `Int.toNat`; the local Lean module preserves that
definition verbatim. At \(n=15\) the integer expression is positive, so this
conversion does not affect the result.

This result refutes only the Goldbach-like equivalence and the corresponding
upstream theorem `oeis_72780_goldbach_conjecture`. It does **not** refute the
entry's separate claims that \(a(n)=0\) characterizes primes (and 1), that
\(a(n)=2\) characterizes products of two distinct primes, or its twin-prime
specialization.

## Machine verification

[`a072780_certificate.py`](a072780_certificate.py) uses only the Python
standard library and evaluates the same counterexample in two independent
ways:

- direct divisor enumeration, with \(\varphi(15)\) counted by gcd tests;
- trial factorization followed by the multiplicative formulas for
  \(\sigma\), \(\sigma_2\), and \(\varphi\).

It also independently checks primality and the two factorizations of 15.
Run from the repository root:

```bash
python3 problems/oeis-a072780/a072780_certificate.py
lake build AgenticConjectures.OeisA072780
```

On the 2026-08-12 verification machine, the certificate ran in 0.05 seconds.
The theorem
`AgenticConjectures.OeisA072780.goldbach_conjecture_false` proves the
negation of the exact universal upstream proposition in Lean 4. Its
arithmetic evaluation uses kernel `decide`; it contains no `sorry`, extra
axioms, or `native_decide`.

## Prior-art and submission status

On 2026-08-12, the OEIS entry still stated the equivalence above. Searches
by the sequence identifier, the exact claim, and the counterexample values
found no public correction, proof, or counterexample on OEIS, the public
web, arXiv, GitHub code, or the Formal Conjectures issues and pull requests.
This negative search is not evidence of novelty. The result is unreviewed,
no novelty is claimed, and nothing has been submitted to OEIS or any other
external venue.
