# Computational progress on OEIS A076141

Checked on 2026-08-11.  This is a rigorous bounded verification, not a proof of
the full conjecture.

For the complete occurrence-geometry argument, see
[the problem-local details](DETAILS.md).

## Problem and result

OEIS A076141 counts the occurrences of the base-2 word for `n` inside the
base-2 word for `n^2`, with overlaps allowed.  Its open question asks whether
this count is always at most one.  The OEIS page records verification only for
`n <= 10^6`.

The exact exhaustive program `a076141_pair_geometry.cpp` found no
counterexample for

```text
0 < n < 2^40 = 1,099,511,627,776.
```

This enlarges the recorded checked interval by a factor of about 1.1 million.

OEIS source: <https://oeis.org/A076141>

## Exhaustive reduction used by the program

Let `L` be the bit length of `n`.  A direct scan of all `n` would be too large,
so the program enumerates every possible geometry of two occurrences.

* An occurrence at the least-significant end forces `n=1`.
* An occurrence at the most-significant end forces a power of two and is
  unique.
* Otherwise, two length-`L` occurrences in the `2L`- or `(2L-1)`-bit word
  `n^2` must overlap.  If their start positions differ by `d`, the binary word
  for `n` has period `d` on the overlap of length `r=L-d`.

For every `L`, overlap, square length, and nonempty prefix/suffix geometry, the
program enumerates the periodic overlap word `q`.  The remaining unknown
prefix `A` is restricted to the exact interval allowed by the square bounds.
The occurrence equations then reduce to

```text
n^2 - C*n = A*2^E - q*2^(d+s) + B,
C = 2^s*(2^d+1),
```

where `B` is fixed by the low `s` bits of `q^2`.  Thus a candidate exists only
if the discriminant is a perfect square.  Every such root is reconstructed and
both occurrences are checked directly against `n^2`.

All arithmetic is exact unsigned 128-bit arithmetic; at `L<=40`, every square
is below `2^80`, far inside the supported range.

The run through `L=40` examined

```text
q candidates:          181,402,314
quadratic candidates:   99,006,717
counterexamples:                 0
```

Reproduction from this directory:

```bash
g++ -O3 -std=c++20 -o a076141_pair_geometry \
  a076141_pair_geometry.cpp
./a076141_pair_geometry 40
```

Source SHA256:

```text
b56136ab951c075e8542a3d32d32572b67d5089e2ab428964c3bc517fe3e3240
```

## Independent audit

An independently written periodic-word enumerator checked the same bit-length
range using a different traversal.  It examined 137,443,246,808 word/offset
candidates and also found no duplicate.  A separate brute-force scan through
all odd `n<2^32` agreed with both structural implementations.

The independent sources are `a076141_independent_periodic.cpp`,
`a076141_independent_pair.cpp`, and `a076141_independent_audit.py`, with
SHA256 hashes respectively

```text
1e7dfe9f85d70c9f8010b4982c0990a305c1d509058b9aae0318e49894a7bca2
d93597625a5b6a1f967d19ff6f3d0f9460eb6d8f8a423edbc8e002118cf379f9
77ce04b9b4f4e372af06cac165c60875db9b925e49c3def7c4b6e2911ba3e2c7
```

`A076141_RUN.txt` preserves the output of the primary `L=40` rerun.

## Limitation

This proves only the finite statement `n<2^40`.  It does not settle the OEIS
question for arbitrarily large `n`, and no novelty or priority claim is made
without external review.

## Upstream Lean statement

The exact FormalConjectures [snapshot and provenance](upstream/README.md) are
preserved in [`76141_34382c19.lean`](upstream/76141_34382c19.lean). Its
universal theorem closes with `by sorry`: it is a conjecture statement, not a
formal proof. The work here verifies only the finite range stated above.
