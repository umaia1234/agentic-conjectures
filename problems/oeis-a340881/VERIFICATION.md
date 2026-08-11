**English** | [한국어](VERIFICATION.ko.md)

# OEIS A340881 verification and reproduction record

This document is the record of an independent finite-computation re-check
of the definition, the first-order recurrence, the pure period for odd
moduli, and the eventual period for general moduli used in the
[detailed proof](PROOF.md). The finite check does not substitute for the
universal proof.

## Audit history

- Final consolidated audit run time: 2026-08-11T23:09:20+09:00
- Python syntax check at that time: passed
- Independent mathematical audit at that time: passed a separate agent audit
- Certificate re-run on 2026-08-12 during per-problem document consolidation: passed

## Reproduction

Run from the repository root.

    python3 -m py_compile problems/oeis-a340881/a340881_certificate.py
    python3 problems/oeis-a340881/a340881_certificate.py

The recorded output is as follows.

    A340881 certificate: PASS
      odd-modulus pure-period checks: 35255
      prime advertised-period checks: 12648
      general eventual-period/sign checks: 62106

## What the certificate checks

- It compares the official initial terms against values computed by the
  recurrence, and for \(n=1,\ldots,12\) it directly computes the double
  product-sum of the definition and compares it with the recurrence.
- For odd moduli \(3\le m<300\), it checks the
  \(2\operatorname{ord}_m(2)\) period and the exponent-shift identity.
- For primes \(p<252\), it checks the advertised period \(2(p-1)\).
- For \(2\le m\le300\), it checks the eventual period according to the
  \(m=2^eu\) decomposition, and for the \(2^e\) component it also
  separately checks \(A(n+1)\equiv-A(n)\pmod{2^e}\).

## Integrity

The certificate SHA-256 left in the final verification record of
2026-08-11 is as follows.

    18d5347ff49eb2eb5b0c974334ac0a4879dbf84d90ee9cf38b0d3dd4b16589e6  a340881_certificate.py

After the per-problem consolidation, only the proof document name in the
code docstring was changed from the deleted `RESULTS.md` to the current
`PROOF.md`. The executable code was not changed, and after this path
cleanup the current SHA-256 is as follows.

    17d7095390071e1e79d686aded5656c5135f7b558ca0a49b14e87253204ccffd  a340881_certificate.py

The SHA-256 recorded in the four-problem consolidated summary document
before the per-problem split is as follows. This value only identifies the
historical provenance of the deleted consolidated original; the current
reproduction targets are the certificate above and the proof in this
directory.

    166b0cd51374e5e2f247f086c2d9b6e448dd879342131f86300ba8c2eb640da1
