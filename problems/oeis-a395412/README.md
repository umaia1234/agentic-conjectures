# OEIS A395412: certified finite nonvanishing extension

## Status

This is **partial progress, not a solution of the infinite conjecture**.

[OEIS A395412](https://oeis.org/A395412) defines `a(n)` as the number of
squarefree integers `d < p_n` for which

```text
P_n / d + d
```

is prime, where `P_n` is the `n`-th primorial.  The OEIS entry publishes 84
terms and conjectures that `a(n)` is never zero.

The accompanying computation does three separately labelled things:

1. reproduces all 84 published terms;
2. rigorously proves `a(n) > 0` for every `85 <= n <= 200`, by recording one
   witness `d` and checking its candidate with PARI/GP `isprime`;
3. screens `201 <= n <= 400` with GMP's BPSW probable-prime test, to look
   quickly for a possible zero.  This last range is explicitly **not** claimed
   as a proof.

[PARI documents `isprime`](https://pari.math.u-bordeaux.fr/dochtml/html-stable/Arithmetic_functions.html#isprime)
as a rigorous primality decision procedure.  It uses APRCL/ECPP after fast
compositeness screening.  The result file stores `n`, `p_n`, `d`, bit length,
and a SHA-256 digest of the decimal candidate.  The candidate itself is
regenerated exactly as `P_n // d + d`.

## A small structural lemma

Every candidate has no prime factor at most `p_n`.  Indeed, let `ell <= p_n`
be prime.  If `ell` does not divide squarefree `d`, then `ell` divides `P_n/d`
but not `d`.  If `ell` divides `d`, squarefreeness implies that `ell` does not
divide `P_n/d`, while it does divide `d`.  In either case
`P_n/d + d` is nonzero modulo `ell`.

This lemma is not enough to prove the conjecture, but explains why ordinary
small-prime trial division cannot settle these candidates.

## Reproduce

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
could refute the conjecture decisively.  The present run found no such
candidate.  Therefore the correct conclusion is a certified finite extension,
not a complete resolution.
