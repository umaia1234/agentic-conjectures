**English** | [한국어](README.ko.md)

# OEIS A056777 / Choudhury–Wei Conjecture 1.1

## Partial theorem

The original conjecture asks whether a composite number \(n\ge4\) that
simultaneously satisfies

\[
\varphi(n+12)=\varphi(n)+12,
\qquad
\sigma(n+12)=\sigma(n)+12
\]

must be of the form

\[
n=p(p+8),
\qquad p,p+2,p+6,p+8\text{ all prime}.
\]

In this folder we prove the following.

> For a composite \(n\ge4\) satisfying the two equations above, \(n+12\)
> cannot be a prime power.

The detailed invariants and the case analysis for every prime are in
[PROOF.md](PROOF.md), and the theorem is **kernel-checked in Lean 4** in
[`AgenticConjectures/OeisA056777.lean`](../../AgenticConjectures/OeisA056777.lean)
(see [below](#lean-4-formalization)). This result rules out the opposite end of the
case "\(n\) is a prime power" already excluded by the paper, but does
not resolve the full original conjecture. In any remaining solution,
neither side is a prime power, and outside the paper's semiprime
theorem at least one side has three or more distinct prime factors or a
repeated prime factor.

The same Lean module now also kernel-checks the other ingredients of that
sentence and one more constraint, for every solution \(n\): \(n\) itself is
not a prime power (the paper's Theorem 3.1); if \(n\) and \(n+12\) are both
products of two distinct primes, then \(n=p(p+8)\) for a prime quadruple (the
"only if" direction of the paper's Theorem 2.2, which needs only the totient
equation); and \(\sigma(n)\) and \(\sigma(n+12)\) are even, i.e. neither
\(n\) nor \(n+12\) is a square or twice a square. Separately, an
[independent exhaustive search](#independent-exhaustive-search-to-1012)
with two implementations confirms the conjecture for every
\(n\le10^{12}\), reproducing the authors' reported search; that is a
finite computation, not a proof.

## Status of the source and scope of verification

- The [Choudhury–Wei paper v3, Conjecture
  1.1](https://arxiv.org/abs/2606.10331v3), as of 2026-07-22, explicitly
  left this problem open. Theorem 2.2 of the paper decides the case
  where \(n,n+12\) are both products of two distinct primes, and
  Theorem 3.1 rules out the case where \(n\) itself is a prime power.
- The authors reported that, with their published [OpenMP
  code](https://github.com/bvrtoverfitprimes/integersequencetesting/blob/main/search_omp.cpp),
  they checked exactly \(2\le n<10^{12}\) and that all 166 solutions
  obtained were of the expected form. The
  [search section](#independent-exhaustive-search-to-1012) below reruns
  that range (up to and including \(10^{12}\)) with independently written
  code and gets the same 166 solutions.
- The Lean results do not rely on any finite search: the prime-power
  exclusion for \(n+12\) is the elementary number-theoretic argument of
  [PROOF.md](PROOF.md), and it and the further constraints are
  machine-checked by the Lean module described below (CI rebuilds it with
  the no-`sorry` gate and the axiom audit). The search is a separate,
  finite computational result with its own logs and verifier.
- The same public partial theorem could not be found on the open web,
  arXiv, math Q&A sites, SeqFan, or GitHub as of 2026-08-11, but this
  is only a negative search result. We do not assert novelty before
  peer review.

## Lean 4 formalization

The partial theorem is formalized, `sorry`-free and against mathlib
only, in
[`AgenticConjectures/OeisA056777.lean`](../../AgenticConjectures/OeisA056777.lean)
(namespace `AgenticConjectures.OeisA056777`):

| Declaration | Content |
|---|---|
| `A n` | the upstream predicate `OeisA56777.A`, term for term: `¬ n.Prime ∧ 1 < n ∧ φ (n+12) = φ n + 12 ∧ σ 1 (n+12) = σ 1 n + 12` (upstream spells `φ` as `totient`) |
| `statement` | the open Choudhury–Wei Conjecture 1.1, `∀ n, A n → ComesFromPrimeQuadruple n` (a `Prop`, **not** proved) |
| `totient_mul_sigma_add_lt_of_not_isPrimePow` | the key inequality \(\varphi(m)\sigma(m)+m<m^2\) for every \(m>1\) that is not a prime power (inequality (7) of PROOF.md) |
| `add_twelve_ne_prime_pow` | **main theorem**: `A n → q.Prime → n + 12 ≠ q ^ ℓ` |
| `not_isPrimePow_add_twelve` | the same in mathlib's `IsPrimePow` form: `A n → ¬ IsPrimePow (n + 12)` |
| `not_isPrimePow` | the paper's Theorem 3.1: `A n → ¬ IsPrimePow n` |
| `semiprime_case` | the "only if" direction of the paper's Theorem 2.2, from the totient equation alone: for primes `p < q`, `p' < q'` with `n = p * q`, `n + 12 = p' * q'` and `φ (n+12) = φ n + 12`, conclude `p' = p + 2 ∧ q' = p + 6 ∧ q = p + 8` |
| `comesFromPrimeQuadruple_of_semiprime` | the same as `A n → … → ComesFromPrimeQuadruple n` |
| `sq_or_two_mul_sq_of_odd_sigma` | `Odd (σ 1 m) → ∃ k, m = k ^ 2 ∨ m = 2 * k ^ 2` |
| `even_sigma`, `even_sigma_add_twelve` | `A n → Even (σ 1 n)` and `A n → Even (σ 1 (n + 12))`: neither \(n\) nor \(n+12\) is a square or twice a square |

Statement faithfulness. `A` is copied term for term from the upstream
snapshot (the only spelling difference is mathlib's notation `φ` for
`Nat.totient`), so "composite \(n\ge4\)" is encoded as
`¬ n.Prime ∧ 1 < n` (which forces \(n\ge4\)); both equations are
additive in `ℕ`, so no truncated-subtraction issue arises; \(\varphi\)
is `Nat.totient` and \(\sigma\) is `ArithmeticFunction.sigma 1`.
"Prime power" is `q ^ ℓ` with `q` prime and any `ℓ` (for `ℓ = 0` the
claim is trivial), equivalently mathlib's `IsPrimePow`.

The Lean proof follows PROOF.md case by case (\(q\ge5\), \(q=3\),
\(q=2\)) with one deliberate deviation: for \(q=2\) it does not use
"\(\sigma(n)\) odd ⇒ \(n\) is a square or twice a square"; instead,
writing \(n=4w\) with \(w\) odd and \(8\mid w+3\), the two equations
give \(\varphi(w)=w-3\) and \(7\sigma(w)=8w+11\). If \(w\) is a prime
power, \(\varphi(w)=w-3\) forces \(w=9\), but \(8\nmid12\); otherwise
the key inequality gives \(w\le9\), so \(8\mid w+3\) leaves only
\(w=5\), which \(7\sigma(w)=8w+11\) excludes (\(7\nmid51\)). The
theorem proved is the same.

The further declarations, with their correspondence to the paper:

- `not_isPrimePow`. The paper's Theorem 3.1 says that no prime \(p\) and
  \(k\ge2\) satisfy both equations at \(n=p^k\). Such an \(n\) is composite
  and \(>1\), and \(k=1\) (a prime) is excluded on both sides, so this is
  exactly `A n → ¬ IsPrimePow n`. Proof: with \(n=r^{b+2}\) and
  \(x=r^{b+1}\) one has \(\varphi(n)\sigma(n)+x=n^2\), \(\varphi(n)+x=n\) and
  \(\sigma(n)\ge n+x\); since \(n+12\) is not a prime power (main theorem),
  the key inequality for \(n+12\), rewritten with the two equations, gives
  \(n+12<x\), impossible because \(x<n\). (The paper treats a prime-power
  \(n+12\) separately; here the main theorem covers it.)
- `semiprime_case`, `comesFromPrimeQuadruple_of_semiprime`. The paper's
  Theorem 2.2 assumes \(n=pq\), \(n+12=p'q'\) with primes \(p<q\),
  \(p'<q'\) and both equations and concludes
  \((p,p',q',q)=(p,p+2,p+6,p+8)\) (the paper also notes \(p\ge5\), which
  follows from the four numbers being prime). `semiprime_case` assumes only
  the totient equation, so it is slightly stronger. The converse ("if")
  direction is the upstream theorem `a_of_comesFromPrimeQuadruple`, proved
  in the upstream file and not repeated here. Proof: the totient equation
  gives \(p'+q'=p+q\), then \(p<p'\) and \((p'-p)(q'-p)=12\); of the
  factorizations with \(p'-p<q'-p\), \((1,12)\) forces \(p=2\) and
  \(q'=14\), \((3,4)\) fails by parity, and \((2,6)\) is the quadruple.
- `even_sigma`, `even_sigma_add_twelve` (not from the paper). If
  \(\sigma(n)\) were odd, so would be \(\sigma(n+12)=\sigma(n)+12\), and by
  `sq_or_two_mul_sq_of_odd_sigma` both \(n\) and \(n+12\) would be squares
  or twice squares. Then \(k^2+12=j^2\) forces \(n=4\), which is not in
  A056777 (\(\varphi(16)=8\ne\varphi(4)+12\)); \(k^2+12=2j^2\) and
  \(2k^2+12=j^2\) have no solutions modulo 32; and \(2k^2+12=2j^2\) has none
  modulo 8 (the residue checks are `decide` over `ZMod 32` and `ZMod 8`).

Reproduce (from the repository root; `lake build` and `check_axioms.py`
need the mathlib cache, `lake exe cache get`):

```bash
lake build AgenticConjectures.OeisA056777   # this module alone, ~20 s once mathlib is cached
lake build                                  # whole library (needed by check_axioms.py)
python3 scripts/check_sorry.py
python3 scripts/check_axioms.py             # only propext / Classical.choice / Quot.sound
```

## Independent exhaustive search to 10^12

> **Computed result (finite range).** The composite \(n\le10^{12}\) with
> \(\varphi(n+12)=\varphi(n)+12\) and \(\sigma(n+12)=\sigma(n)+12\) are
> exactly the 166 numbers \(n=p(p+8)\) with \(p,p+2,p+6,p+8\) all prime,
> from \(65=5\cdot13\) to \(967164068009=983441\cdot983449\). Hence
> Conjecture 1.1 holds for every \(n\le10^{12}\).

This reproduces the authors' reported search over \(2\le n<10^{12}\) (166
solutions, all of the predicted form) with code written without consulting
theirs, and it agrees term by term with the 166-term OEIS b-file
(`b056777.txt`, retrieved 2026-10-24, SHA-256
`8a4d205fea5761af6deac8c2bf23d709c4e7844e792f48bf8616135376835ccf`). It is
not a new result and not a proof: it says nothing about \(n>10^{12}\). The
solutions are listed in [`a056777_hits.txt`](a056777_hits.txt); all of them
are \(\equiv65\pmod{72}\). A prime \(n\) satisfies both equations exactly
when \(n+12\) is prime as well (\(\varphi(p)=p-1\), \(\sigma(p)=p+1\));
A056777 excludes those, and the programs only count them (`primehits`).

### Programs

- **Implementation 1**, [`a056777_search.cpp`](a056777_search.cpp) (C++17,
  `std::thread`): a segmented factorization sieve. In each segment every
  \(m\) starts as its odd part (\(\varphi\), \(\sigma\) of the 2-part come
  from `ctz`), and every odd prime \(p\le\sqrt{N+12}\) is divided out of its
  multiples completely by exact division with the 2-adic inverse of \(p\); a
  cofactor \(>1\) left at the end is a single prime. All values are exact
  64-bit integers (\(\sigma(m)<2^{43}\) here). For every block of \(10^9\)
  consecutive \(n\) (block \(k\) is \(k\cdot10^9<n\le(k+1)\cdot10^9\)) it
  logs the composite solutions, the number of prime solutions, the exact
  sums \(\sum\varphi(n)\) and \(\sum\sigma(n)\), and the position-weighted
  hash \(\sum(\varphi(n)C+\sigma(n))(2n+1)\bmod2^{64}\),
  \(C=\texttt{0x9E3779B97F4A7C15}\). This is the general scheme the paper
  describes (cofactor plus running \(\varphi\), \(\sigma\)), implemented
  independently.
- **Implementation 2**, [`a056777_independent.py`](a056777_independent.py)
  (Python with numba kernels, `multiprocessing`): a different algorithm, an
  exponent-count sieve. Every multiple of every prime power \(p^k\) in the
  segment (2 included) increments a counter, a second pass multiplies in
  the tabulated \(\varphi(p^e)\), \(\sigma(p^e)\), \(p^e\), and the final
  cofactor is \(m\) divided by the product of the prime-power parts found.
  It prints the same block lines (statistics computed with numpy).
- **Closed forms**, [`a056777_sums.cpp`](a056777_sums.cpp):
  \(\sum_{n\le x}\sigma(n)=\sum_{d\le x}d\lfloor x/d\rfloor\) and
  \(\Phi(x)=\sum_{n\le x}\varphi(n)\) from
  \(\Phi(x)=x(x+1)/2-\sum_{d=2}^{x}\Phi(\lfloor x/d\rfloor)\), without
  factoring any \(n\).
- **Verifier**, [`a056777_verify.py`](a056777_verify.py) (Python + sympy +
  g++, run by CI): builds both C++ programs; compares implementation 1 block
  by block with a pure-Python smallest-prime-factor recurrence on
  \(n\le10^6\); runs implementation 1 on \(n\le10^9\) and checks its
  solutions against the prime-quadruple values and its totals against the
  closed forms; and audits the committed logs (blocks tile
  \([1,10^{12}]\) with no gap or overlap, per-run totals, solutions equal to
  the prime-quadruple values and to `a056777_hits.txt`, closed forms at every
  run boundary, implementation 2 identical block by block).

### Cross-checks

| Check | Range | Result |
|---|---|---|
| implementation 2 reproduces every block line of implementation 1 (composite and prime solutions, \(\sum\varphi\), \(\sum\sigma\), hash) | \(n\le10^{11}\), 100 blocks | identical |
| logged totals \(\sum\varphi(n)\), \(\sum\sigma(n)\) versus the closed forms | \(x=10^{11},\,4\cdot10^{11},\,7\cdot10^{11},\,10^{12}\) | equal |
| logged solutions versus the values \(p(p+8)\) from a separate prime sieve | \(n\le10^{12}\) | identical (166) |
| every solution re-checked with sympy `totient` and `divisor_sigma` | 166 values | pass |
| logged solutions versus the OEIS b-file | \(n\le10^{12}\) | identical (166) |
| pure-Python reference versus implementation 1, block by block (CI) | \(n\le10^6\) | identical |

### Runs

All runs on an Apple M5 Max (18 cores) shared with other jobs (load average
between about 20 and 140 during the runs); implementation 1 built with Apple
clang 21, `g++ -O3 -std=c++17 -pthread`, implementation 2 run with Python
3.12.13, numpy 2.5.4 and numba 0.68.0.

| Log | Range of \(n\) | Program | Parallelism | Wall time |
|---|---|---|---|---|
| [`logs/main_1e11.log`](logs/main_1e11.log) | \(1\) to \(10^{11}\) | implementation 1 | 3 threads | 473 s |
| [`logs/main_1e12_part1.log`](logs/main_1e12_part1.log) | \(10^{11}+1\) to \(4\cdot10^{11}\) | implementation 1 | 3 threads | 1339 s |
| [`logs/main_1e12_part2.log`](logs/main_1e12_part2.log) | \(4\cdot10^{11}+1\) to \(7\cdot10^{11}\) | implementation 1 | 3 threads | 1145 s |
| [`logs/main_1e12_part3.log`](logs/main_1e12_part3.log) | \(7\cdot10^{11}+1\) to \(10^{12}\) | implementation 1 | 3 threads | 957 s |
| [`logs/independent_1e11.log`](logs/independent_1e11.log) | \(1\) to \(10^{11}\) | implementation 2 | 2 processes | 1600 s |

Source SHA-256 at the time of the runs: `a056777_search.cpp`
`a49af0162285cdc4f792e6e17d7f68bce4528a6c582ff1fc23b233145854f1d6`,
`a056777_independent.py`
`9a64d87424d43eb558a9dca4f505a7226f6ac7588ef33d77bd12c82f1dc41f75`,
`a056777_sums.cpp`
`ac639d75e41078700ad12e6f60c6121f1af6b9aa1d85fc6041668fb0e5177b95`.

Reproduce (from this directory; `build/` is gitignored):

```bash
python3 a056777_verify.py                    # CI check, about 17 s here
mkdir -p build
g++ -O3 -std=c++17 -pthread -o build/a056777_search a056777_search.cpp
./build/a056777_search --start 1 --end 100000000000 --threads 3 > build/main_1e11.log
./build/a056777_search --start 100000000001 --end 400000000000 --threads 3 > build/main_1e12_part1.log
./build/a056777_search --start 400000000001 --end 700000000000 --threads 3 > build/main_1e12_part2.log
./build/a056777_search --start 700000000001 --end 1000000000000 --threads 3 > build/main_1e12_part3.log
# implementation 2 (needs numpy and numba)
python3 a056777_independent.py --start 1 --end 100000000000 --procs 2 > build/independent_1e11.log
g++ -O3 -std=c++17 -o build/a056777_sums a056777_sums.cpp
./build/a056777_sums 100000000000 400000000000 700000000000 1000000000000   # about 10 s
```

`python3 a056777_verify.py --limit 1000000000000 --threads 3` reruns
implementation 1 over the whole range with all checks, and
`python3 a056777_verify.py --independent 100000000000 --threads 2` (with a
Python that has sympy, numpy and numba) reruns implementation 2 and compares
it with the committed logs.

What is not claimed. The search is a finite computation; it does not prove
Conjecture 1.1 and says nothing beyond \(10^{12}\). It is not new: it
reproduces the authors' reported search and the OEIS data. Implementation 1
follows the same general scheme as the authors' program; the algorithmically
different implementation 2 covers only \(n\le10^{11}\), so above \(10^{11}\)
the per-number values are corroborated only in aggregate (closed-form totals
at \(4\cdot10^{11}\), \(7\cdot10^{11}\), \(10^{12}\)) and through the solution
list matching the separately computed prime-quadruple values. There is no
formal (Lean) certificate for the search; it rests on the compiled code and
the hardware, mitigated by the independent implementations and audits above.

## Upstream Lean formalization

The FormalConjectures original and pinned provenance used for the audit
are preserved in the [upstream record](upstream/README.md) and in
[`56777.lean`](upstream/56777.lean). The central conjecture is a
**statement** closed with `by sorry`, not a formal proof, and the
prime-power exclusion theorem for \(n+12\) and the further constraints in
this folder are not formalized in that upstream file — they live in this
repository's own module listed above, which restates the upstream
predicate term for term instead of importing the (non-standalone)
snapshot.
