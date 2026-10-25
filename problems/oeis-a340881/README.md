**English** | [한국어](README.ko.md)

# OEIS A340881

We resolve the two modular periodicity conjectures of
[OEIS A340881](https://oeis.org/A340881) for every modulus \(m\ge2\). The
sequence is defined by

\[
A(n)=\sum_{k=0}^{n-1}2^{k(k+1)/2}
       \prod_{j=k+1}^{n-1}(2^j-1),\qquad n\ge1.
\]

## Results

- For odd \(m>1\) and \(L=\operatorname{ord}_m(2)\),
  \(A(n+2L)\equiv A(n)\pmod m\) holds for all \(n\ge1\).
  That is, we obtain an explicit period starting from the beginning, even
  for odd composite moduli.
- For a prime \(p\), the minimal period divides \(2(p-1)\). For \(p=2\),
  \(A(n)\equiv1\pmod2\).
- Writing \(m=2^eu\) with \(u\) odd, we obtain eventual periodicity for
  every \(m\ge2\). When \(u>1\), \(2\operatorname{ord}_u(2)\) is a period
  for \(n\ge\max(1,e)\), and when \(u=1\), period 2 holds for
  \(n\ge e\).

## Documents and certificate

- [Detailed proof](PROOF.md)
- [Verification and reproduction record](VERIFICATION.md)
- [Executable certificate](a340881_certificate.py)

It can be re-checked from the repository root as follows.

    python3 -m py_compile problems/oeis-a340881/a340881_certificate.py
    python3 problems/oeis-a340881/a340881_certificate.py

## Lean formal proof

[`AgenticConjectures/OeisA340881.lean`](../../AgenticConjectures/OeisA340881.lean)
proves, without `sorry`, extra axioms, or `native_decide`:

```text
statement1_holds : statement1     -- conjecture 1, minimum-period clause included
statement2_holds : statement2     -- conjecture 2
oeis_340881_conjecture_0 :        -- the upstream statement, verbatim
  ∀ p, p.Prime → ∀ n ≥ 1, a (n + 2 * (p - 1)) % p = a n % p
period_odd :
  Odd m → 0 < ord m ∧ ∀ n ≥ 1, a (n + 2 * ord m) ≡ a n [MOD m]
modEq_two_pow_mul_odd :
  Odd u → max 1 e ≤ n → a (n + 2 * ord u) ≡ a n [MOD 2 ^ e * u]
eventually_periodic :
  0 < m → ∃ N T, 0 < T ∧ ∀ n ≥ N, a (n + T) % m = a n % m
```

Here `ord m` abbreviates `orderOf (2 : ZMod m)`. The proof follows
[PROOF.md](PROOF.md): Lemma 1.1 is `A_add_two_mul`, Lemma 1.2 is
`dvd_of_minimal`, Lemma 1.4 is `A_succ`, Lemma 1.5 is `A_succ_two_pow` and
`modEq_two_pow`, and Theorem 1.6 is `modEq_two_pow_mul_odd`. Two steps of
§1.4 are shortened. For odd \(p\), \(2^{p-1}=1\) feeds Lemma 1.1 directly, so
\(2(p-1)\) is itself a period and Lemma 1.2 bounds the minimum period without
\(\operatorname{ord}_p(2)\mid p-1\). For \(p=2\), period 2 comes from Lemma
1.5 with \(e=1\) instead of from \(A(n)\equiv1\pmod2\).

    lake build AgenticConjectures.OeisA340881
    python3 scripts/check_axioms.py

## Statement faithfulness

- OEIS conjecture 1 says that modulo a prime \(p\) the sequence is "purely
  periodic with minimum period dividing 2*(p - 1)". `statement1` reads purely
  periodic as periodic from the offset \(n=1\), and states that a positive
  period exists and that every positive period with no smaller positive
  period divides \(2(p-1)\).
- OEIS conjecture 2 concerns eventual periodicity modulo composite \(n\).
  `statement2` keeps that restriction; `eventually_periodic` proves the claim
  for every \(m\ge1\).
- `a` is the upstream definition, term for term:
  `Nat.choose (k + 1) 2` is \(k(k+1)/2\), and the natural subtraction
  `2 ^ j - 1` is exact because \(2^j\ge1\). Its first ten values match the
  OEIS data \(1,3,17,183,3769,\ldots\). `a 0 = 0` lies before the offset and
  is never constrained.
- `orderOf (2 : ZMod m)` is the multiplicative order of 2 modulo odd \(m\);
  `orderOf_two_pos` shows it is positive.
- For \(m=2^e\) with \(e\ge1\), PROOF.md states period 2 from \(n\ge e\).
  `modEq_two_pow_mul_odd` with \(u=1\) gives the same, since
  \(\operatorname{ord}_1(2)=1\) and \(\max(1,e)=e\).

## Research status

As of 2026-08-11, the OEIS entry marked both statements as a "Conjecture".
The audit record from that time is that the public web, arXiv, and GitHub
were checked against the exact formula, initial terms, and key period
expressions, and no identical public proof was found. This is only a
negative search result, and this proof has not yet undergone peer review or
confirmation by an OEIS editor.

## Upstream Lean formalization

The FormalConjectures [original snapshot and provenance record](upstream/README.md)
is preserved in [`340881_294a5574.lean`](upstream/340881_294a5574.lean).
The theorem recording the period for prime moduli is a `by sorry`
**conjecture statement**, not a formal proof. The stronger result of this
folder for all moduli is not formalized in that Lean snapshot. This
repository's own module, described [above](#lean-formal-proof), proves the
upstream statement verbatim as `oeis_340881_conjecture_0`; the snapshot file
itself is unchanged.
