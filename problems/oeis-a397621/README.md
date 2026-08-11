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

## Research status

As of 2026-08-11 the Formula section of A397621 marked this identity as
"Conjecture". The record from that time — that public searches did not
find the same proof — is not a confirmation of novelty. The adjacent
literature on linear complexity of binomial sequences deals with
infinite diagonal sequences of Pascal's triangle, which is distinct from
the fixed finite-row problem here. This proof has not yet undergone peer
review or confirmation by the OEIS editors.
