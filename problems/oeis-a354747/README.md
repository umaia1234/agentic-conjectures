# Resolution of the first unknown case of OEIS A354747

Checked on 2026-08-11.

For the full derivation of the mathematical claims, see
[the problem-local details](DETAILS.md).

## Result

Let

```text
P = 201886*3^39101 - 1 = 2*100943*3^39101 - 1.
```

Then `P` is prime, and every number `201886*3^m - 1` with
`1 <= m < 39101` is composite.  Consequently

```text
a(100943) = 39101.
```

This disproves the conjectural value `a(100943)=0` recorded in the formal
conjecture corpus and answers the first unknown case on the current OEIS page.
At the time of this computation, OEIS stated only that a value, if it existed,
was greater than 30000.

OEIS source: <https://oeis.org/A354747>

FormalConjectures source: [local snapshot](upstream/354747_c4bbc149.lean) and
[provenance](upstream/README.md).

## Why this is the relevant expression

Starting from `x_0=2n-1` and applying `x -> 3x+2` gives

```text
x_m = 3^m*(2n-1) + 2*(3^(m-1)+...+1)
    = 2*n*3^m - 1.
```

For `n=100943`, this is `201886*3^m-1`.

## Deterministic primality proofs

### Independent Lucas-rank certificate

The source `a354747_lucas_certificate.cpp` uses only GMP integer arithmetic.
Put

```text
A = P+1 = 2*100943*3^39101
```

and take the coprime-parameter Lucas sequence `U_k(8,5)`, with discriminant
`D=44`.  It
computes, modulo `P`,

```text
U_A                         = 0,
gcd(U_(A/2),P)              = 1,
gcd(U_(A/3),P)              = 1,
gcd(U_(A/100943),P)         = 1.
```

Here `gcd(8,5)=1`, `gcd(2*Q*D,P)=1`, `(D/P)=-1`, and `100943` is prime by
trial division through its square root.  For completeness, the reason this
proves primality is short.
For any prime `ell` dividing `P`, let `z_ell` be the rank of apparition in the
Lucas sequence.  The four computed relations and the complete factorization
of `A` force `z_ell=A`.  The standard Lucas rank theorem gives

```text
z_ell | ell - (D/ell),
```

so `A <= ell+1`.  Since `A=P+1`, this forces `ell>=P`; hence `ell=P` and `P`
is prime.  This is a direct deterministic certificate independent of
OpenPFGW's implementation.

Reproduction from this directory:

```bash
# On a Debian/Ubuntu system with administrator access:
sudo apt-get install libgmp-dev
g++ -O3 -std=c++17 -pthread a354747_lucas_certificate.cpp \
  -lgmpxx -lgmp -o a354747_lucas_certificate
./a354747_lucas_certificate
```

The exact no-root fallback used for this audit was:

```bash
mkdir -p /tmp/a354747-gmp
cd /tmp/a354747-gmp
apt-get download libgmp-dev
dpkg-deb -x libgmp-dev_*.deb root
cd /home/user/projects/agentic-conjectures/problems/oeis-a354747
A354747_GMP_ROOT=/tmp/a354747-gmp/root
g++ -O3 -march=native -std=c++20 -pthread \
  -I"$A354747_GMP_ROOT/usr/include" \
  -I"$A354747_GMP_ROOT/usr/include/x86_64-linux-gnu" \
  a354747_lucas_certificate.cpp \
  "$A354747_GMP_ROOT/usr/lib/x86_64-linux-gnu/libgmpxx.a" \
  "$A354747_GMP_ROOT/usr/lib/x86_64-linux-gnu/libgmp.a" \
  -o /tmp/a354747_lucas_certificate
/tmp/a354747_lucas_certificate
```

`A354747_LUCAS_TRANSCRIPT.txt` records the exact successful output of an
additional clean rebuild and rerun from the saved source.

### OpenPFGW BLS proof

OpenPFGW 4.1.8 was run with its combined Brillhart--Lehmer--Selfridge
primality test:

```bash
pfgw64 -tc -q'201886*3^39101-1'
```

The decisive output was:

```text
PFGW Version 4.1.8.64BIT.20260508.x86_Dev [GWNUM 31.5]
Primality testing 201886*3^39101-1 [N-1/N+1, Brillhart-Lehmer-Selfridge]
Running N+1 test using discriminant 11, base 1+sqrt(11)
Running N+1 test using discriminant 11, base 4+sqrt(11)
Calling N+1 BLS with factored part 100.00% and helper 0.03% (300.03% proof)
201886*3^39101-1 is prime!
```

The complete factorization needed on the `N+1` side is immediate:

```text
P + 1 = 2 * 100943 * 3^39101,
```

and `100943` is prime.  Thus this is a deterministic BLS result, not merely a
probable-prime report.  It independently agrees with the direct Lucas-rank
certificate above.  As a further sanity check, Python/gmpy2 returned true for
its strong BPSW probable-prime test.

The number has 61,992 bits and 18,662 decimal digits.  Reproducibility
fingerprints are:

```text
SHA256(decimal expansion of P)
12c2474a1742cfc52f03c033af9e8835f3186bf8772d8f58fa165e29c7279209

first 64 decimal digits
1672195294060207980901446301441052720940850826276618687926585697

last 64 decimal digits
8909124893148009648825515014435963009367758790198507323395721657
```

OpenPFGW project: <https://sourceforge.net/projects/openpfgw/>

The BLS criteria are from J. Brillhart, D. H. Lehmer, and J. L. Selfridge,
"New Primality Criteria and Factorizations of 2^m +/- 1," Mathematics of
Computation 29 (1975), 620--647.

## Exhaustive minimality check

`a354747_exponent_sieve.cpp` exhaustively generated every exponent in
`1..39100` not eliminated by a prime divisor at most 100000.  Its modular
recurrence is exact: for each prime `p`, it advances
`201886*3^m (mod p)` from one exponent to the next and removes `m` precisely
when that residue is 1.

The sieve left 1,991 exponents.  Every survivor was then submitted to
OpenPFGW's PRP test.  None returned PRP/prime status.  OpenPFGW's process exit
semantics were separately checked with the known prime 17 (exit 0) and
composite 15 (exit 1).

Reproduction commands, from this directory, are:

```bash
g++ -O3 -std=c++17 -o a354747_exponent_sieve \
  a354747_exponent_sieve.cpp

./a354747_exponent_sieve 1 39100 100000 | \
  xargs -P4 -I{} sh -c \
  'if pfgw64 -q"201886*3^{}-1" >/dev/null 2>&1; then echo PRP_m={}; fi'
```

The sieve reports

```text
range=1..39100 prime_bound=100000 survivors=1991
```

and the second command produces no `PRP_m` line.  A separate discovery scan
over `30001..40000` produced exactly one PRP exponent, `39101`, which was then
upgraded to the deterministic BLS proof above.

An independent back-end audit did not rely on OEIS's older check through
30000.  The same exact recurrence sieve was rerun with its prime bound raised
to one million over the entire interval `1..39100`.  It eliminated 37,482
exponents by an explicit prime divisor and left 1,618.
`a354747_minimality_audit.py` then used a different test from the discovery
run: every survivor received two base-2 Fermat tests, once at OpenPFGW's
default FFT length and once at the next larger length.  Every exponent
produced the same non-one `RES64` in both runs:

```text
1..30000:      SUMMARY tested=1237 anomalies=0
30001..39100:  SUMMARY tested=381  anomalies=0

SHA256(a354747_survivors_1m.txt)
05afbb41940e339a93eb71c7eba602f64164f908ffbdcd9f3c9ec55e14d8e8e1

SHA256(a354747_base2_dualfft_1_30000.tsv)
1549d0850ad5a5f9b24879ee472505f7d490c892e2e3501e6f1fcbe0ea6d718d

SHA256(a354747_base2_dualfft_30001_39100.tsv)
7e5ac803819963d8d1d9eb3fd542aee8c837e515d782210517eb349b3b105972
```

The million-prime-bound audit can be reproduced with:

```bash
./a354747_exponent_sieve 1 39100 1000000 > a354747_survivors_1m.txt
python3 a354747_minimality_audit.py a354747_survivors_1m.txt \
  --pfgw /path/to/pfgw64 --workers 12
```

A third independently written audit (`a354747_minimality_a1_audit.py`)
recomputed discrete-log divisor classes for every prime at most 100000,
again obtained exactly 1,991 survivors, and retested all of them with
OpenPFGW's next-larger FFT (`-a1 -f0`).  All 1,991 were composite; the
SHA256 of the sorted `m:RES64` records was
`70189bdcbc983ec662f3934b8a40bc7e7ba240b2c363cb0a37a24c117a52733c`.

Hashes of the exact binaries/sources used in this run:

```text
ebd9357b769c73b62e1e7b35620d6a1ea84e068c6284b23b463378cadf771b5b  pfgw64
a25712a6faf2c720707a6e5731371796252f66c06ad198c462e61e92a7654d23  a354747_exponent_sieve.cpp
26be3ebebe59f2b8c52840e514dbd74e8c4f599a09b67b8afd031c6b50a9c549  a354747_lucas_certificate.cpp
fcce4c9cbba0b2f0fd5d2ea763a585562523aa864242dd750a9b5030cd5eb90b  a354747_minimality_audit.py
a5a2856f80d5c5f58d3781403b04790ea62a01e4143eb6f3ce2476196dff2d55  a354747_minimality_a1_audit.py
```

## Scope and novelty caveat

The mathematical conclusion follows from the deterministic primality proof
and exhaustive smaller-exponent check.  The current official OEIS record still
labels `n=100943` unknown as of the check date.  This directory records the
computation and makes it reproducible; it does not by itself establish
publication priority.  External review and submission to OEIS remain separate
steps.

## Upstream Lean statement

The preserved theorem `oeis_a354747_conjecture_0` closes with `by sorry`: it is
a conjecture statement, not a formal proof. It asserts `a354747 100943 = 0`,
whereas the deterministic certificates in this directory prove the value is
`39101` and therefore refute that upstream statement.
