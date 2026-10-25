**English** | [한국어](README.ko.md)

# OEIS A297707 — certified previous-prime gaps

## Status

**Partial: a certified finite range, not the upstream bound.** For every
integer $n$ with $2<n\le 175$, the gap

\[
g(n)=a(n)-\operatorname{prevprime}(a(n))
\]

is proved to be $1$ (only at $n=3$) or a prime, so it is never composite.
For $176\le n\le 250$ the same computation proves every integer strictly
between $a(n)-g(n)$ and $a(n)$ composite, but the endpoint $a(n)-g(n)$ is
only a BPSW probable prime. So there the true gap is proved to be at least
the recorded $g(n)$, and every recorded $g(n)$ is prime, but **it is not
proved that the recorded value is the gap**. The upstream statement (bound
$250$) is therefore not certified.

## Statement and upstream correspondence

[OEIS A297707](https://oeis.org/A297707) defines

\[
a(n)=\prod_{k=1}^{n-1} n!_k,\qquad
n!_k=\prod_{j=0}^{\lfloor (n-1)/k\rfloor}(n-jk),
\]

so $a(1),\dots,a(7)=1,2,18,768,90000,44789760,30494620800$. The
FormalConjectures snapshot [`297707_fd3973db.lean`](upstream/297707_fd3973db.lean)
asks for the least $n>2$ for which $a(n)-\operatorname{prevprime}(a(n))$ is
composite and states, as a `by sorry` conjecture,

```lean
theorem oeis_297707_conjecture_0 :
  ∀ n, 2 < n → IsComposite (a n - Nat.prevPrime (a n)) → 250 < n
```

with `IsComposite m := 1 < m ∧ ¬ m.Prime` and `Nat.prevPrime m` the largest
prime strictly below `m`. The upstream `A297707` uses natural-number
subtraction `n - j * k`, which never truncates because $jk\le n-1$; it agrees
with the product above. Since $a(n)\ge 18$ for $n\ge3$, `Nat.prevPrime (a n)`
is the genuine previous prime and `a n - Nat.prevPrime (a n)` is exactly
$g(n)\ge1$. The certified range therefore settles, computationally and
outside Lean, the instances $2<n\le 175$ of `oeis_297707_conjecture_0`
(their hypothesis is false); it says nothing about $n>175$. No Lean
statement is added: reducing those instances to this data inside Lean would
need a formally verified ECPP-certificate checker run by the kernel on
numbers of up to 2028 digits, plus about 42,700 kernel-checked compositeness
witnesses, which this work does not attempt (and `native_decide` is not
allowed here).

## A structural remark

Every prime $p\le n$ divides $n!=n!_1\mid a(n)$, and every prime factor of
$a(n)$ is at most $n$, because $a(n)$ is a product of integers in $[1,n]$.
Hence, if a prime $p\le n$ divides $h$ with $1\le h<a(n)-n$, then $p$
divides $a(n)-h>p$ and $a(n)-h$ is composite. Call the other $h$ (that is,
$h=1$ or all prime factors of $h$ exceed $n$) *admissible*. Since
$a(n)-g(n)$ is a prime larger than $n$, $g(n)$ is admissible, so a
composite $g(n)$ would have to be at least $q^2$, where $q$ is the least
prime above $n$. In the computed range $g(n)\ge q^2$ happens only for
$n=17,52,61,108$ (with the prime gaps $433,3209,4691,13001$); the largest
gap is $g(241)=24359<251^2$. This explains why composite gaps are rare, but
it is not a proof; the proof below is computational.

## Method

[`certify_a297707.py`](certify_a297707.py) (gmpy2 + PARI/GP) does, for each
$n$:

1. computes $a(n)$ exactly;
2. walks $h=1,2,\dots$: inadmissible $h$ are composite by the remark; for each
   admissible $h$ it stores a witness that $a(n)-h$ is composite, either a
   sieve prime $q\in(n,10^7]$ dividing $a(n)-h$ or the failure
   $2^{N-1}\not\equiv1\pmod N$ of Fermat's test for $N=a(n)-h$. The first
   admissible $h$ for which $a(n)-h$ passes GMP's BPSW test is $g(n)$;
3. proves $a(n)-g(n)$ prime with a PARI/GP 2.19.0 ECPP certificate
   (`primecert`, one thread, split into resumable partial certificates for
   large inputs) and checks it at once with `primecertisvalid`;
4. records that $g(n)$ is $1$ or prime (trial division).

The case $g(n)=1$, where $a(n)-1$ has the fully factored $N+1=a(n)$ and an
$N+1$ (Lucas) proof would be cheaper, occurs only at $n=3$, so ECPP is used
throughout. A Fermat witness was found for every admissible $h$ that the
sieve did not settle (no base other than 2 was ever needed).

[`verify_a297707.py`](verify_a297707.py) is an independent checker that
needs only the Python standard library (it uses gmpy2 for speed when
available). For each record it recomputes $a(n)$ with its own product
routine and compares SHA-256 digests; re-checks every integer of the gap
(inadmissible $h$ by their small prime factor, admissible $h$ by the stored
factor or Fermat witness, requiring the witness lists to cover exactly the
admissible $h<g(n)$); proves the endpoint prime by deterministic
Miller–Rabin when it is below $3.3\cdot10^{24}$ and, given the certificate,
by its **own affine elliptic-curve check of the PARI ECPP certificate**
(every step: $\gcd(N_i,6)=1$, nonsingular curve, $q_i>(N_i^{1/4}+1)^2$,
$[s_i]P_i\ne O$, $[q_i][s_i]P_i=O$ with every modular inversion valid, and
$q_{\text{last}}<2^{64}$ proved by Miller–Rabin), optionally also by PARI's
`primecertisvalid` (`--pari gp`); and checks that $g(n)$ is $1$ or prime.

## Data and certificates

- [`a297707_gaps.jsonl`](a297707_gaps.jsonl): one line per $3\le n\le250$
  with `g`, digit counts, SHA-256 digests of $a(n)$ and of the endpoint, the
  witnesses (`factor`: pairs `[h, q]`; `fermat2`: the $h$ with a base-2
  Fermat witness; `fermat_other`: empty), and `endpoint`. For
  $n\le 175$, `endpoint.method` is `ecpp-pari` with the certificate's
  SHA-256, size, number of steps and PARI wall time (one thread, on a shared
  and heavily loaded machine; for $n=53,54,120$, whose first attempt was
  interrupted and resumed from a saved partial certificate, only the final
  attempt is timed); for larger $n$ it is `bpsw-only`.
- [`certs/`](certs/): the ECPP certificates `n<n>.gp` for $3\le n\le50$
  (PARI output format, 441 KB in total). These are re-checked in CI.
- Certificates for $51\le n\le 175$ are **local-only** (46 MB in total,
  the largest 882 KB for $n=173$); their SHA-256 digests are in the data
  file. With PARI/GP 2.19.0 and one thread the generator is deterministic:
  regenerating the certificates for $n=40,53,54,120,150$ reproduced the
  recorded SHA-256 digests exactly. A certificate obtained differently (for example
  with another PARI version) may differ byte-wise; the verifier still accepts
  it if it is valid and reports that it is not the recorded one.

Summary of the data: $g(3)=1$ and the recorded $g(n)$ is prime for every
$4\le n\le250$ (proved to be the gap for $n\le175$); the largest certified
gap is $g(147)=17827$, the largest recorded one $g(241)=24359$. The
certified range uses 29,960 factor witnesses and 12,712 base-2 Fermat
witnesses (65,857 and 30,952 for all $n\le250$). The endpoint for $n=175$
has 2028 digits and its certificate 213 ECPP steps.

## Reproduce

Requirements: Python 3 with `gmpy2`, PARI/GP 2.19.0 (`gp`). Times were
measured on an Apple M5 Max shared with other jobs (load average often above
50) with four worker processes:

```bash
cd problems/oeis-a297707
OUT=/tmp/a297707_out
# gaps and compositeness witnesses for 3 <= n <= 250: about 20 min wall
for s in 3 4 5 6; do python3 certify_a297707.py search $s 250 --stride 4 --out $OUT & done; wait
# ECPP certificates for 3 <= n <= 175: about 3 h wall; the per-n
# single-thread run times add up to 10.6 h (737 s for n = 175)
seq 3 175 | xargs -P 4 -I{} python3 certify_a297707.py prove {} {} --out $OUT
python3 certify_a297707.py merge --out $OUT   # writes $OUT/a297707_gaps.jsonl
```

ECPP time grows roughly like the third power of the digit count (a fit over
$100\le n\le 175$ gives exponent 2.8); the same setup would need very
roughly another 50 h of single-thread ECPP time to reach $n=250$
(3317 digits).

The search records also contain timing fields, so a regenerated data file
differs from the committed one only in those fields.

## Verify

```bash
cd problems/oeis-a297707
# CI subset: everything for 3 <= n <= 50, pure Python (26 s locally)
python3 verify_a297707.py --certs certs --max-n 50 --require-certified-through 50
# full local check with the regenerated certificates (86 CPU-min with gmpy2)
python3 verify_a297707.py --certs $OUT/certs --pari gp --require-certified-through 175
```

Split into four $n$-ranges (`--min-n`/`--max-n`), the full check took about
35 min wall on the loaded machine. It also re-checks the compositeness
witnesses for $176\le n\le250$, re-tests each of those endpoints as a
base-2 strong probable prime, and lists those $n$ as having an unproved
(BPSW-only) endpoint.

## What is not claimed

- For $176\le n\le250$ only the lower bound (the gap is at least the
  recorded value) is proved, and nothing is computed for $n>250$. The BPSW
  screen up to $n=250$ reproduces the upstream "greater than 250" statement
  only at the probable-prime level.
- The upstream theorem is not formalized or proved in Lean; the primality
  proofs are ECPP certificates checked by two programs (this repository's
  Python checker and PARI/GP), not Lean proofs.
- The infinite question (whether a composite gap ever occurs) is open; the
  structural remark only explains why one is unlikely for small $n$.
- No novelty is claimed. The bound 250 is the one stated in the upstream
  formalization of the OEIS entry; this work only adds certificates for
  $2<n\le 175$ and a probable-prime re-computation up to $n=250$.

## Original search script

[`oeis_a297707_search.py`](oeis_a297707_search.py) is the earlier
experimental BPSW search (requires `gmpy2` and `sympy`); its endpoints are
probable primes only:

```bash
python3 problems/oeis-a297707/oeis_a297707_search.py N
```

## Upstream Lean formalization

The FormalConjectures [original snapshot and provenance record](upstream/README.md)
is preserved in [`297707_fd3973db.lean`](upstream/297707_fd3973db.lean).
The theorem stating that the counterexample index is greater than `250` is
a `by sorry` **conjecture statement**, not a formal proof. The certified data
here settles its instances $2<n\le 175$ computationally and does not certify
the statement itself.
