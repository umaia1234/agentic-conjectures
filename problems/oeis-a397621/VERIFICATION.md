**English** | [한국어](VERIFICATION.ko.md)

# OEIS A397621 Verification and Reproduction Record

This document is the record of recomputing, with different algorithms,
the connection-polynomial orientation, the zero run of the lower bound,
the explicit upper bound, and the boundary cases of the
[detailed proof](PROOF.md). Finite checks do not substitute for a
universal proof.

## Canonical and legacy

The [canonical certificate](a397621_certificate.py) incorporates the
follow-up audit. The [initial v1 certificate](legacy/a397621_certificate.py)
is preserved as is in order to reproduce the computation as of the
initial report. The canonical version keeps all the initial checks
while, for \(n=1,\ldots,512\), also explicitly checking the convolution
condition of the \((1+x)^d\) connection polynomial used in the proof and
the zero run.

## Audit history

- Final consolidated audit run time: 2026-08-11T23:09:20+09:00
- Python syntax check at that time: passed
- Independent mathematical audit at that time: connection-polynomial
  orientation, lower bound, and the \(n=1\) boundary passed
- Re-ran canonical and legacy on 2026-08-12 during the per-problem
  document consolidation: all passed

## Reproduction

Run from the repository root.

    python3 -m py_compile \
      problems/oeis-a397621/a397621_certificate.py \
      problems/oeis-a397621/legacy/a397621_certificate.py
    python3 problems/oeis-a397621/a397621_certificate.py
    python3 problems/oeis-a397621/legacy/a397621_certificate.py

The canonical output is as follows.

    A397621 certificate: PASS
      Berlekamp--Massey: n=1..512 plus 12 boundary values
      independent GF(2) system solver: n=1..80

The legacy output is as follows.

    A397621 certificate checks passed

## What the certificate checks

- Checks \(n=1,\ldots,512\) and the large boundary values
  1000, 1023, 1024, 1025, 2047, 2048, 4095, 4096, 8191, 8192,
  9999, 10000 with an independent Berlekamp--Massey implementation.
- Checks the consistency of all possible recurrence lengths for
  \(n=1,\ldots,80\) with a separate GF(2) Gaussian elimination
  implementation.
- The canonical certificate also confirms that positions
  \(r+1,\ldots,q-1\) of the Pascal polynomial are 0 and position \(q\)
  is 1, and that
  \([x^i](1+x)^d(1+x)^n=0\) (\(d\le i\le n\)).

## Integrity

    93bfbc68f744f25703683aba69e25d46ce02fa13bcef51183ba579faa70c3c2f  a397621_certificate.py
    5ced56c1afd2f6b5158059c69c17d64adefee0791fa7bd48945a622be00970ed  legacy/a397621_certificate.py

The first value agrees between the 2026-08-11 final verification record
and the current file. The second is a value newly recorded for the
current legacy file during the per-problem consolidation.

The historical SHA-256 of the consolidated four-problem summary document
before the per-problem split is as follows.

    166b0cd51374e5e2f247f086c2d9b6e448dd879342131f86300ba8c2eb640da1
