**English** | [한국어](README.ko.md)

# OEIS A395412: certified finite nonvanishing extension

For the full definitions, lemma, and finite-witness interpretation, see
[the problem-local details](DETAILS.md).

## Status

This is **partial progress, not a solution of the infinite conjecture**.

[OEIS A395412](https://oeis.org/A395412) defines `a(n)` as the number of
squarefree integers `d < p_n` for which

```text
P_n / d + d
```

is prime, where `P_n` is the `n`-th primorial.  The OEIS entry publishes 84
terms and conjectures that `a(n)` is never zero.

The recorded results, each labelled separately:

1. all 84 published terms are reproduced (original run, below);
2. `a(n) > 0` is **proved for every `85 <= n <= 478`**: for each `n` one
   witness `d` is recorded and its candidate `P_n/d + d` has an ECPP primality
   certificate checked by PARI/GP `primecertisvalid` and by an independent
   Python checker (next section);
3. for `85 <= n <= 200` the same witnesses had already been proved in the
   original run with PARI/GP `isprime`;
4. the original run only BPSW-screened `201 <= n <= 400`; that range is now
   covered by item 2 with the same witnesses, so **no range is left that is
   only probable-prime screened**.  Nothing is claimed for `n > 478`.

## ECPP certificates for 85 <= n <= 478

**Statement.**  For every `85 <= n <= 478`, the row for `n` in
[`ecpp_witnesses.json`](ecpp_witnesses.json) gives a squarefree `d < p_n`
such that `P_n/d + d` is prime; hence `a(n) >= 1`.  The theorem behind the
certificates and the soundness argument of the independent checker are in
[Section 5 of the details](DETAILS.md).

**Method.**

- *Witness choice.*  `d` is the least squarefree `d < p_n` whose candidate
  passes PARI's BPSW test `ispseudoprime`.  BPSW only selects `d`; it is not
  part of the proof.  For `85 <= n <= 400` the witnesses coincide with the
  original run's `result.json` (proved there up to 200, screened 201..400).
- *Proof.*  [`a395412_ecpp.gp`](a395412_ecpp.gp) runs PARI/GP 2.19.0
  `primecert` on the candidate, writes the Atkin–Morain certificate to a file
  (one step `[N, t, s, a, [x, y]]` per line), reads the file back and accepts
  it only if `primecertisvalid` returns 1.
  [`ecpp_certify.py`](ecpp_certify.py) runs one single-threaded `gp` process
  per `n` (four in parallel) and records the rows.
- *Independent check.*  [`verify_witnesses.py`](verify_witnesses.py) needs no
  PARI.  It regenerates every candidate from `(n, d)`, compares bit length and
  SHA-256 of the decimal expansion with the row, and checks ECPP certificates
  with its own elliptic-curve arithmetic.  It re-checked every certificate of
  the run (with gmpy2 integers), and in CI it checks the three committed sample
  certificates in pure Python and confirms that a tampered certificate is
  rejected.

**Data.**  `ecpp_witnesses.json` has one row per `n`: `n`, `p_n`, `d`,
candidate bit length, SHA-256 of the decimal candidate, number of ECPP steps,
SHA-256 of the certificate file, PARI CPU seconds for `primecert` and for the
write/read/`primecertisvalid` check, and wall seconds.  The certificates take
79 MB in total (11 KB for `n = 85` up to 523 KB for
`n = 478`), so only three samples are committed in
[`certificates/`](certificates/) (`n = 85, 201, 300`); `ecpp_certify.py`
regenerates the rest.  With `nbthreads = 1`, PARI 2.19.0 produced
byte-identical certificates when we regenerated them in separate runs
(`n = 201` four times, `n = 337` twice).

**Measured runtimes** (Apple M5 Max, PARI/GP 2.19.0, four single-threaded
`gp` processes; CPU time is the sum of PARI's per-`n` `getabstime` figures
recorded in the rows):

| run | range | CPU time | wall time |
|---|---|---:|---:|
| `ecpp_certify.py` (interrupted once at `n = 337`, resumed) | 85..400 | 8980 s | 24.4 + 44.8 min |
| `ecpp_certify.py --budget-minutes 85` (budget stop) | 401..478 | 15457 s | 80.8 min |
| `verify_witnesses.py --cert-dir ... --backend gmpy2 --jobs 4` | 85..478 | 1331 s | 6.9 min |
| `verify_witnesses.py` (CI mode, pure Python) | rows + 3 samples | | 20.4 s |

The two certification runs shared the machine with other jobs (load average
about 60 to 100 on 18 cores), which inflates their times: `primecert` for
`n = 400` took 106.5 s of CPU time in the run against 73.0 s in a separate
lightly loaded test.  The hardest single proof was `n = 467` (4654-bit
candidate, 168 ECPP steps, 306 s of `primecert` CPU time, 325 s wall).  The
CI-mode verifier ran on an idle machine; the full independent check started on
an idle machine, but other jobs loaded it again before it ended.  The
interruption at `n = 337` was a `gp` process that ended without output or
PARI error (most likely killed from outside); `n = 337` alone then succeeded,
`ecpp_certify.py` now reruns such a process, and the resumed run started at
`n = 335`.  The `runs` list in `ecpp_witnesses.json` records all three
segments.

**Reproduce** (from this directory):

```bash
# CI-feasible: rows, legacy agreement, three sample certificates (stdlib only)
python3 verify_witnesses.py

# Local only (PARI/GP 2.19+): regenerate and PARI-check every certificate
python3 ecpp_certify.py --from 85 --to 478 --jobs 4 --expect ecpp_witnesses.json

# Local only (gmpy2): independent re-check of every regenerated certificate
python3 verify_witnesses.py --cert-dir build/certificates --backend gmpy2 --jobs 4
```

`ecpp_certify.py` writes to `build/` (git-ignored), resumes if its output
file already has rows, and with `--budget-minutes` stops starting new `n`
when the next one is unlikely to finish in time.

**Not claimed.**  Nothing for `n > 478`; no exact values of `a(n)` for
`n > 84`; the infinite conjecture remains open.  The run found no `n` without
a probable-prime candidate.  We did not look for computations of this
sequence beyond the OEIS entry, so no novelty is claimed for the range.

## A small structural lemma

Every candidate has no prime factor at most `p_n`.  Indeed, let `ell <= p_n`
be prime.  If `ell` does not divide squarefree `d`, then `ell` divides `P_n/d`
but not `d`.  If `ell` divides `d`, squarefreeness implies that `ell` does not
divide `P_n/d`, while it does divide `d`.  In either case
`P_n/d + d` is nonzero modulo `ell`.

This lemma is not enough to prove the conjecture, but explains why ordinary
small-prime trial division cannot settle these candidates.

## Original run: reproduce

The original run reproduced the 84 published terms, proved `85 <= n <= 200`
with PARI/GP `isprime`, and BPSW-screened `201 <= n <= 400`; its output is
[`result.json`](result.json).

[PARI documents `isprime`](https://pari.math.u-bordeaux.fr/dochtml/html-stable/Arithmetic_functions.html#isprime)
as a rigorous primality decision procedure.  It uses APRCL/ECPP after fast
compositeness screening.  The result file stores `n`, `p_n`, `d`, bit length,
and a SHA-256 digest of the decimal candidate.  The candidate itself is
regenerated exactly as `P_n // d + d`.

Requirements: Python 3, `gmpy2`, and PARI/GP 2.15 or later.

```bash
cd /home/user/projects/agentic-conjectures/problems/oeis-a395412
python3 search_and_certify.py \
  --gp /path/to/gp \
  --prove-through 200 \
  --screen-through 400 \
  --output result.json
```

On Ubuntu, `gp` is supplied by the `pari-gp` package.  Increasing
`--prove-through` is valid but becomes substantially slower because rigorous
primality proofs dominate the running time.

## Interpretation

A future run which reports a zero candidate would still need a compositeness
certificate (for example, a proper factor) for every admissible `d` before it
could refute the conjecture decisively.  No run so far found such a
candidate.  Therefore the correct conclusion is a certified finite extension,
not a complete resolution.
