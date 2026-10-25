**English** | [한국어](README.ko.md)

# OEIS A397621

We prove the Pascal mod 2 row linear-complexity conjecture of
[OEIS A397621](https://oeis.org/A397621). [A001317](https://oeis.org/A001317)
is the number obtained by reducing the \(n\)-th row of Pascal's triangle
mod 2 and reading it as a binary number, and A397621 is the GF(2) linear
complexity of that MSB-first binary word.

## Results

For all \(n\ge1\),

\[
\operatorname{A397621}(\operatorname{A001317}(n))
=2^{\lfloor\log_2n\rfloor+1}-n
=\operatorname{A080079}(n).
\]

The lower bound is obtained from the run of consecutive zeros arising
between the two blocks of the Pascal row, and the upper bound is
obtained by explicitly constructing the connection polynomial
\(C(x)=(1+x)^d\).

## Documents and certificates

- [Detailed proof](PROOF.md)
- [Verification and reproduction record](VERIFICATION.md)
- [Canonical certificate](a397621_certificate.py)
- [Initial v1 certificate](legacy/a397621_certificate.py)

The certificate at the root, which incorporates the follow-up audit, is
canonical. The initial certificate is left as is for reproducibility and
to preserve the change history.

    python3 -m py_compile problems/oeis-a397621/a397621_certificate.py
    python3 problems/oeis-a397621/a397621_certificate.py

## Lean formal proof

[`AgenticConjectures/OeisA397621.lean`](../../AgenticConjectures/OeisA397621.lean)
proves, without `sorry`, extra axioms, or `native_decide`:

```text
a_A001317_eq_A080079 : statement
  -- ∀ n ≥ 1, a (A001317 n) = A080079 n, where A080079 n = 2 * 2 ^ Nat.log 2 n - n
linearComplexity_pascal :
  1 ≤ n → linearComplexity (fun i => (n.choose i : ZMod 2)) (n + 1) = A080079 n
a_two : a 2 = 1
```

The proof follows [PROOF.md](PROOF.md). `binWord_A001317` is §3.3: the
MSB-first binary word of A001317(n) is the coefficient sequence of
\((1+x)^n\) over \(\mathbf F_2\). `not_hasRecurrence` is the zero-run lower
bound of §3.4.1–3.4.2, and `hasRecurrence` is the \((1+x)^d\) upper bound of
§3.4.3. The Frobenius identity \((1+x)^{2^h}=1+x^{2^h}\) comes from
mathlib's `add_pow_char_pow`.

    lake build AgenticConjectures.OeisA397621
    python3 scripts/check_axioms.py

## Statement faithfulness

- `a` follows the OEIS name: the linear complexity over GF(2) of the binary
  expansion of \(n\), most significant bit first, as computed by
  Berlekamp–Massey. `HasRecurrence s N L` asks for
  \(s_i+c_1s_{i-1}+\cdots+c_Ls_{i-L}=0\) for \(L\le i<N\) with no condition
  on \(c_L\), and `linearComplexity` takes the least such \(L\). This is the
  recurrence span of §3.1 and the length that the certificate's brute-force
  solver searches.
- A comment in the entry describes \(a(n)\) as the degree of the minimal
  connection polynomial. Read literally, that differs at \(n=2\): the word
  `10` has span 1 (\(c_1=0\)), but no connection polynomial of degree below 2
  generates it. The data has \(a(2)=1\), and `a_two` checks that our
  definition gives 1. On the words of the conjecture the two readings agree,
  because the span lower bound rules out every polynomial of degree below
  \(d\) and the witness \((1+x)^d\) has degree exactly \(d\). This last
  remark is not formalized.
- `A001317 n` is \(\sum_{k=0}^{n}(\binom nk \bmod 2)\,2^k\), row \(n\) of
  Pascal's triangle mod 2 read in binary. `A080079 n` is the closed form
  \(2\cdot2^{\lfloor\log_2n\rfloor}-n\) from its OEIS Formula section, not
  its carry-sequence name. The statement starts at \(n=1\), the offset of
  A080079.
- There is no upstream FormalConjectures snapshot for this entry.

## Research status

As of 2026-08-11 the Formula section of A397621 marked this identity as
"Conjecture". The record from that time — that public searches did not
find the same proof — is not a confirmation of novelty. The adjacent
literature on linear complexity of binomial sequences deals with
infinite diagonal sequences of Pascal's triangle, which is distinct from
the fixed finite-row problem here. This proof has not yet undergone peer
review or confirmation by the OEIS editors.
