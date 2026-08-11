**English** | [한국어](VERIFICATION.ko.md)

# OEIS A397245 Verification and Reproduction Record

This document is the record of recomputing, along independent paths, the
integer triangular recurrence, the GF(3) algebraic recurrence, the
base-3 coefficient classification, and the differential identity of the
[detailed proof](PROOF.md). Finite checks do not substitute for a
universal proof.

## Canonical and legacy

The [canonical certificate](a397245_certificate.py) incorporates the
follow-up audit. The [initial v1 certificate](legacy/a397245_certificate.py)
is preserved as is in order to reproduce the computation as of the
initial report. Both scripts require SymPy.

## Audit history

- Final consolidated audit run time: 2026-08-11T23:09:20+09:00
- Python syntax check at that time: passed
- Independent mathematical audit at that time: integrality, GF(3)
  reduction, uniqueness, and the algebraic and differential identities
  passed
- Re-ran canonical and legacy on 2026-08-12 during the per-problem
  document consolidation: all passed

## Reproduction

Run from the repository root.

    python3 -m py_compile \
      problems/oeis-a397245/a397245_certificate.py \
      problems/oeis-a397245/legacy/a397245_certificate.py
    python3 problems/oeis-a397245/a397245_certificate.py
    python3 problems/oeis-a397245/legacy/a397245_certificate.py

The canonical output is as follows.

    A397245 certificate: PASS
      exact integer recurrence: n=0..140
      independent GF(3) algebraic recurrence: n=0..2000
      symbolic differential identity: verified over GF(3)

The legacy output is as follows.

    A397245 certificate checks passed

## What the certificate checks

- Computes \(a_0,\ldots,a_{140}\) as exact big integers via the integer
  triangular recurrence, and compares against the first nine terms and
  the mod 3 classification.
- Independently computes the coefficient recurrence of
  \(B=1+xB^2+x^3B^3\) for \(n=0,\ldots,2000\) and compares against the
  base-3 classification.
- Checks by GF(3) Gröbner reduction that \(xD'=B-1\) follows from
  \(B'=B^2/(1+xB)\) and
  \(D=x+x(B-1)B'/B\).

The initial report also records, separately from the above, that all
terms \(0,\ldots,400\) of the then-current official OEIS b-file were
compared and matched. The two certificates preserved now do not download
the b-file from the network, so this item is a historical external
comparison record as of 2026-08-11 and not a check that is re-performed
by the commands above.

## Integrity

    be2b3a0f3f2f2d167f502210f0180b5cdbda48b830a925909c476c0683812d3a  a397245_certificate.py
    4c946fd309c1638129d04096fcd78f52c356fb605a055fa5547aa1a9f7a4185e  legacy/a397245_certificate.py

The first value agrees between the 2026-08-11 final verification record
and the current file. The second is a value newly recorded for the
current legacy file during the per-problem consolidation.

The historical SHA-256 of the consolidated four-problem summary document
before the per-problem split is as follows.

    166b0cd51374e5e2f247f086c2d9b6e448dd879342131f86300ba8c2eb640da1
