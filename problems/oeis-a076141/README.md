**English** | [한국어](README.ko.md)

# Computational progress on OEIS A076141

Checked on 2026-08-11 for `n < 2^40`, and extended on 2026-10-24 to
`n < 2^100`.  These are rigorous bounded verifications, not a proof of the
full conjecture.  Lean 4 also proves the weaker bound `a(n) <= 2` for every
`n`.

For the complete occurrence-geometry argument, see
[the problem-local details](DETAILS.md).  Sections 1–7 there cover the
`2^40` run, and section 8 covers the extension.

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

The 2026-10 extension (section "Extension to `n < 2^100`" below) uses two
independent single-occurrence enumerators and found no counterexample for

```text
0 < n < 2^64  = 18,446,744,073,709,551,616              (every bit position)
0 < n < 2^100 = 1,267,650,600,228,229,401,496,703,205,376 (reduced positions)
```

The reduced positions are justified by pair lemmas that are proved in Lean 4.
The `2^64` statement does not depend on those lemmas.  The same lemmas give
the unconditional bound `a(n) <= 2` for every `n` (Lean theorem `a_le_two`),
with no computation.

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

`a076141_independent_periodic.cpp` uses the x86 BMI2 intrinsics in
`immintrin.h` (`_pdep_u64`), so it does not compile on arm64.  It was not
rerun during the 2026-10 extension.  The results above are unchanged.

## Extension to `n < 2^100` (2026-10)

### Statement

For every `n` with `0 < n < 2^100`, the binary word of `n` occurs at most
once in the binary word of `n^2`, so `a(n) <= 1`.  (Upstream also has
`a(0) = 1`.)

The two ranges rest on different facts.

- `0 < n < 2^64` uses only elementary facts and exhaustive enumeration at
  every bit position.
- `2^64 <= n < 2^100` additionally uses the pair lemmas proved in
  [`AgenticConjectures/OeisA076141.lean`](../../AgenticConjectures/OeisA076141.lean).

Separately, the Lean module proves the weaker bound `a(n) <= 2` for every
`n` (`a_le_two`) with no computation.  Three occurrences of an odd `k >= 3`
would violate the pair geometry of item 4 below, and occurrences of `2m`
shift to occurrences of `m` ([DETAILS.md §8.4](DETAILS.md)).

### Method

[DETAILS.md §8](DETAILS.md) gives the proofs.

1. A counterexample has an odd counterexample `k >= 3` below it (Lean).
   Every occurrence of an odd `k >= 3` of bit length `L` starts at a bit
   position `t` with `3 <= t <= L-1` (Lean).
2. At a fixed position `t`, an occurrence of an odd `n` is determined in two
   ways.  Its low part `B = n^2 mod 2^t` determines it through a 2-adic
   square root; this is the bottom method, with `2^(t-3)` candidates.  Its
   high part `A = floor(n^2 / 2^(t+L))` determines it through an integer
   square root; this is the top method, with about `3*2^(L-t-2)` candidates.
   Every candidate is checked against the exact square.  For every `n`
   found, all occurrences are counted, and a count of at least 2 would be
   reported as a counterexample.
3. The full plan examines every position `3 <= t <= L-1` at cost
   `O(2^(L/2))` per `L`.  It was used for `L <= 64`.
4. The reduced plan rests on the Lean theorem `pair_geometry`.  Two
   occurrences `s < t` of an odd `n >= 3` satisfy `3 <= s`, `2s <= t`,
   `L+s <= 2t` and `t < L`.  So one of them lies in `[3, sigma]` or in
   `[tau, L-1]`, where `sigma = floor(L/3)+1` and
   `tau = max(2*sigma+2, ceil((L+sigma+1)/2))`.  Searching only these
   positions costs `O(2^(L/3))` per `L`.  It was used for `L <= 100`.
5. Two independently written programs implement both plans.
   - P, `a076141_occ_closed.cpp`, uses a 2-adic inverse square root (bottom)
     and an integer square root (top).
   - Q, `a076141_occ_hensel.cpp`, uses bitwise Hensel lifting (bottom) and
     an exact galloping search on `n^2 - 2^t n` (top).  It takes no square
     roots.

   The two programs must print identical per-`L` lines, including candidate
   counts, and identical `OCC L t n count` lists.
   `a076141_bruteforce_odd.cpp` scans every window of every odd `n` directly.
6. `a076141_crosscheck.py --smoke` compiles the three programs and compares
   them.  `a076141_crosscheck.py --logs` re-checks the committed logs.  The
   checks are:
   - exit status 0 and `counterexamples=0`;
   - the recorded SHA-256 of each occurrence list;
   - P = Q;
   - no gaps in `L`;
   - reduced-mode lists equal full-mode lists restricted to the reduced
     positions, wherever both exist;
   - the brute-force list equals the full-mode lists on its range.

### Results

The enumerator runs used 3 threads and the brute-force run used 1 thread,
on a shared Apple M5 Max (arm64; `g++` is Apple clang 21).  The load
average was 60–90 on 18 cores, so the wall times are pessimistic.

| Log | Program | Mode | `L` | Bottom candidates | Top candidates | Occurrences | Counterexamples | Wall (s) | User CPU (s) |
|---|---|---|---|---:|---:|---:|---:|---:|---:|
| [`p_full_L3-64.log`](logs/p_full_L3-64.log) | P | full | 3–64 | 6,442,450,879 | 6,442,450,878 | 514 | 0 | 433.23 | 800.10 |
| [`q_full_L3-64.log`](logs/q_full_L3-64.log) | Q | full | 3–64 | 6,442,450,879 | 6,442,450,878 | 514 | 0 | 331.35 | 581.79 |
| [`p_red_L3-96.log`](logs/p_red_L3-96.log) | P | reduced | 3–96 | 8,589,934,495 | 3,221,225,378 | 737 | 0 | 422.68 | 658.38 |
| [`q_red_L3-96.log`](logs/q_red_L3-96.log) | Q | reduced | 3–96 | 8,589,934,495 | 3,221,225,378 | 737 | 0 | 1026.44 | 1585.17 |
| [`p_red_L97-100.log`](logs/p_red_L97-100.log) | P | reduced | 97–100 | 12,884,901,884 | 4,831,838,204 | 73 | 0 | 571.47 | 993.95 |
| [`q_red_L97-100.log`](logs/q_red_L97-100.log) | Q | reduced | 97–100 | 12,884,901,884 | 4,831,838,204 | 73 | 0 | 1099.56 | 2498.56 |
| [`bf_L3-34.log`](logs/bf_L3-34.log) | BF | brute force | 3–34 | 8,589,934,590 odd `n` | — | 146 | 0 | 1067.06 | 551.09 |

In every run each `n` found has exactly one occurrence (`max_count=1`), and
no counterexample was found.  The full-mode occurrence lists for
`L <= 34` equal the brute-force list of all odd `n < 2^34`, which has
146 occurrences.  For `3 <= L <= 64`, the reduced-mode lists equal the
full-mode lists restricted to the reduced positions.

Throughput, in candidates per CPU second from the table: P about 16 million
(full) and 18 million (reduced); Q about 22 million (full) and 7 million
(reduced).  Q is slower in reduced mode, where its bitwise lift needs
`L - t + 1` steps per candidate at the small positions `t <= sigma`.  The
brute force scans about 16 million odd `n` per CPU second.

### Lean declarations

All declarations are in the namespace `AgenticConjectures.OeisA076141`.

| Declaration | Content |
|---|---|
| `list_count_infix`, `binary_pattern_nat`, `a` | upstream definitions, copied term for term |
| `statement` | upstream conjecture `∀ n, a n ≤ 1` (open; not proved here) |
| `Occ n L s` | `n ^ 2 / 2 ^ s % 2 ^ L = n` (occurrence at bit position `s`) |
| `a_eq_countP` | for `n ≠ 0`, `a n` counts the window positions with `Occ` |
| `a_zero` | `a 0 = 1` |
| `occ_lt`, `three_le_of_occ` | occurrences of odd `n ≥ 3` start at `3 ≤ s < L` |
| `occ_of_occ_two_mul`, `occ_descent`, `exists_odd_of_two_occ` | occurrences pass from `2n` to `n`, and so injectively to the odd part |
| `not_occ_pair_of_close` | no pair at `s`, `s+d` when `2d+s+1 ≤ L` |
| `not_occ_pair_of_far` | no pair at `s`, `s+d` when `d < s`, `s+d < L` and `2^(L-1) ≤ n` |
| `pair_geometry`, `pair_covered` | `3 ≤ s`, `2s ≤ t`, `L+s ≤ 2t`, `t < L`; reduced positions cover every pair |
| `exists_two_occ_of_two_le_a`, `reduction` | `2 ≤ a n` gives an odd `k ≤ n`, `k ≥ 3`, with such a pair |
| `a_le_two` | `a n ≤ 2` for every `n` (unconditional; uses no search) |
| `SearchedPos`, `a_le_one_of_search` | the hypothesis checked by the searches for all `L ≤ N` implies `a n ≤ 1` for `n < 2^N` |

### Statement faithfulness

The Lean module copies `list_count_infix`, `binary_pattern_nat` and `a` term
for term from [`upstream/76141_34382c19.lean`](upstream/76141_34382c19.lean).
`statement` is the proposition of `oeis_a076141_conjecture`.

- **Index base.** Upstream compares windows at offsets `i` from the most
  significant end of the reversed `Nat.digits 2` lists.  `Occ` counts bit
  positions `s` from the least significant end.  `a_eq_countP` proves that
  `s = M - L - i`, where `M` and `L` are the binary lengths of `n^2` and
  `n`.
- **Natural subtraction.** The only truncated subtraction is in
  `M - L - i`, with `i ≤ M - L`.
- **Boundary value.** `n = 0` is special upstream: its pattern is `[0]`, so
  `a 0 = 1` (`a_zero`).  It is excluded from the searches and is not a
  counterexample.
- **The bound `a_le_two`.** It is stated for the upstream `a` itself, so
  `∀ n, a n ≤ 2` is a complete Lean proof of a weakening of `statement`
  (`2` in place of `1`).
- **What the theorems leave open.** The finite claim "`a n ≤ 1` for all
  `n < 2^100`" is reduced by `a_le_one_of_search` (with `N = 100`) to the
  per-`L` hypothesis that the programs check.  That hypothesis is not proved
  in Lean.  The completeness of the bottom and top methods is not formalized
  either.

### Reproduction

From this directory:

```bash
python3 a076141_crosscheck.py --smoke 28                     # about 12 s; run in CI
python3 a076141_crosscheck.py --logs logs/*.log              # under 1 s; run in CI
g++ -O3 -std=c++20 -o a076141_occ_closed a076141_occ_closed.cpp
g++ -O3 -std=c++20 -o a076141_occ_hensel a076141_occ_hensel.cpp
g++ -O3 -std=c++20 -o a076141_bruteforce_odd a076141_bruteforce_odd.cpp
./a076141_occ_closed 3 64 full 3        # 433 s wall, 800 s CPU
./a076141_occ_hensel 3 64 full 3        # 331 s wall, 582 s CPU
./a076141_occ_closed 3 96 reduced 3     # 423 s wall, 658 s CPU
./a076141_occ_hensel 3 96 reduced 3     # 1026 s wall, 1585 s CPU
./a076141_occ_closed 97 100 reduced 3   # 571 s wall, 994 s CPU
./a076141_occ_hensel 97 100 reduced 3   # 1100 s wall, 2499 s CPU
./a076141_bruteforce_odd 3 34 1         # 1067 s wall, 551 s CPU
```

From the repository root, `lake build AgenticConjectures.OeisA076141` takes
about 25 s once Mathlib is built.  The [`logs/`](logs/) directory holds the
complete output of each run listed above.  Each log has a header with the
command, the source SHA-256, the host and the start time, and a footer with
the exit status, the times and the SHA-256 of its `OCC` lines.

### What is not claimed

- No proof of the conjecture for all `n`; the only unconditional result is
  the weaker bound `a(n) <= 2`.
- No formal verification of the enumerators' completeness, of the programs,
  or of the compiler.  These risks are reduced by two independent
  implementations that agree line for line and by brute-force agreement for
  `L <= 34`.
- The range `2^64 <= n < 2^100` depends on the Lean pair lemmas; the range
  `n < 2^64` does not.
- No novelty or priority claim.

## Limitation

This proves only the finite statements `n<2^40` (pair geometry) and `n<2^100`
(single occurrences; `n<2^64` without the pair lemmas), plus the weaker
bound `a(n)<=2` for all `n`.  It does not settle
the OEIS question for arbitrarily large `n`, and no novelty or priority claim
is made without external review.

## Upstream Lean statement

The exact FormalConjectures [snapshot and provenance](upstream/README.md) are
preserved in [`76141_34382c19.lean`](upstream/76141_34382c19.lean). Its
universal theorem closes with `by sorry`: it is a conjecture statement, not a
formal proof. The work here verifies only the finite ranges stated above.
[`AgenticConjectures/OeisA076141.lean`](../../AgenticConjectures/OeisA076141.lean)
copies the upstream definitions and proves the reduction lemmas used by the
2026-10 searches and the weaker bound `a n ≤ 2`, but not the conjecture
itself.
