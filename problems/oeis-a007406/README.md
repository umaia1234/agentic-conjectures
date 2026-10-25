**English** | [한국어](README.ko.md)

# OEIS A007406 — the Eldar–Ordowski gcd conjecture

## Verdict

**Partial.** The conjecture is not proved. This directory contains:

- a Lean 4 proof of the prime half (classical), of the `2`-, `3`- and `5`-parts,
  of an exact reduction of the conjecture to a bound on `q`-adic valuations,
  and of the cases `n = t q` (`2 ≤ t ≤ 6`, every prime `q`) and of every
  `5`-smooth `n > 3`;
- a Boyd-tree certificate that checks the reduced bound for every prime
  `5 ≤ q ≤ 2,642,245`; with the Lean reduction this gives the conjecture for
  every `3 < n ≤ 5,284,491` (computational, see the trust model below);
- two independent direct checks of the conjecture from the definition for
  `3 < n ≤ 10^6`.

The Lean proofs use no `sorry`, extra axioms, or `native_decide`.

## The sequence and the conjecture

[OEIS A007406](https://oeis.org/A007406) (Wolstenholme numbers, offset 1) is
the numerator of

\[
H_2(n)=\sum_{k=1}^{n}\frac{1}{k^2}:\qquad 1, 5, 49, 205, 5269, 5369, 266681, \dots
\]

The entry (checked on 2026-10-24) records:

> “Conjecture: for n > 3, gcd(n, a(n-1)) = A089026(n). Checked up to n = 10^5.”
> — Amiram Eldar and Thomas Ordowski, Jul 28 2019

where [A089026](https://oeis.org/A089026)`(n)` is `n` if `n` is prime and `1`
otherwise. Jonathan Sondow added that the prime case follows from
Wolstenholme's theorem, so it remains to show `gcd(n, a(n-1)) = 1` for
composite `n > 3`.

The upstream formalization is `OeisA7406.conjecture` in
google-deepmind/formal-conjectures at commit
`c094b979118b89adb77cf5f8d923ac9dd2e51b1d`; byte-exact snapshots of
`7406.lean` and the imported `89026.lean` are in [upstream/](upstream/README.md).

## Mathematics

Write `v_q` for the `q`-adic valuation, `a(m)` for the numerator of `H_2(m)`,
and, for a prime `q`,

\[
U_q(m)=\sum_{k\le m,\ q\nmid k}\frac1{k^2},\qquad
H_2(m)=U_q(m)+\frac{H_2(\lfloor m/q\rfloor)}{q^2}.
\]

`U_q(m)` is `q`-integral. For `q ≥ 5` the block sums vanish modulo `q`:
`U_q(qt) ≡ t·Σ_{x∈F_q^×} x^{-2} = t·Σ_{x∈F_q^×} x^2 ≡ 0 (mod q)`.

1. **Prime half** (classical, Wolstenholme type). With `t = 1` this gives
   `p ∣ a(p-1)` for primes `p ≥ 5`, hence `gcd(p, a(p-1)) = p`.
2. **Exact reduction.** For a prime `q ≥ 5` and `t ≥ 2`,
   `H_2(qt-1) = U_q(qt) + H_2(t-1)/q^2` with `v_q(U_q(qt)) ≥ 1`, so
   `q ∣ a(qt-1)` if and only if `v_q(H_2(t-1)) ≥ 3`.
3. **Small primes.** `v_2(H_2(m)) ≤ 0` and `v_3(H_2(m)) ≤ 0` for all `m ≥ 1`
   (so `a(m)` is never divisible by `2` or `3`), and `v_5(H_2(m)) ≤ 2`.
4. **Equivalence.** The conjecture holds if and only if
   `v_q(H_2(m)) ≤ 2` for every prime `q ≥ 5` and every `m ≥ 1`.
5. **Pruning and trees.** If `s ≥ 1`, `0 ≤ r < q` and `v_q(H_2(s)) ≤ 1`, then
   `v_q(H_2(qs+r)) = v_q(H_2(s)) - 2`. So every `m` with `v_q(H_2(m)) ≥ 2`
   lies in the tree with roots `1, …, q-1` in which a node `s` has the children
   `qs, …, qs+q-1` only when `v_q(H_2(s)) ≥ 2` — the analogue of Boyd's tree for
   the harmonic numbers. A finite tree on which `v_q ≤ 2` everywhere proves
   `v_q(H_2(m)) ≤ 2` for all `m ≥ 1`.

The `2`- and `3`-parts are trees whose roots all have `v_q ≤ 0`; the `5`-part
is a tree whose roots have `v_5 ≤ 1`.

## Lean results

Module `AgenticConjectures.OeisA007406`
([source](../../AgenticConjectures/OeisA007406.lean)):

| Declaration | Statement |
|---|---|
| `statement` | the conjecture, as in upstream (not proved) |
| `prime_dvd_a_pred`, `statement_at_prime` | `p ∣ a(p-1)` for primes `p ≥ 5`; the conjecture for prime `n > 3` |
| `two_not_dvd_a`, `three_not_dvd_a` | `2 ∤ a(m)` and `3 ∤ a(m)` for `m ≥ 1` |
| `padicValRat_five_H2_le_two`, `five_not_dvd_a` | `v_5(H_2(m)) ≤ 2` for `m ≥ 1`; `5 ∤ a(5t-1)` for `t ≥ 2` |
| `dvd_a_iff` | `q ∣ a(qt-1) ↔ 3 ≤ v_q(H_2(t-1))` for primes `q ≥ 5`, `t ≥ 2` |
| `statement_iff` | the conjecture `↔` `v_q(H_2(m)) ≤ 2` for all primes `q ≥ 5`, `m ≥ 1` |
| `padicValRat_H2_mul_add` | pruning lemma (item 5 above) |
| `padicValRat_H2_le_two_of_tree` | tree-certificate interface used by the computation |
| `statement_le_of_padicValRat_le_two` | bounds for all primes `5 ≤ q ≤ Q` give the conjecture for `3 < n ≤ 2Q+1` |
| `statement_at_of_padicValRat_le_two` | bounds for the prime factors `q ≥ 5` of `n` give the conjecture at `n` |
| `statement_at_of_five_smooth`, `statement_at_two_pow` | every `5`-smooth `n > 3`; `n = 2^k`, `k ≥ 2` |
| `statement_at_two_mul` … `statement_at_six_mul` | `n = tq` for `t = 2, 3, 4, 5, 6` and every prime `q` |
| `statement_at_mul` | `n = qt`, `q` prime, `t ≥ 2` `5`-smooth, `q^3 ∤ a(t-1)` if `q ≥ 5` |
| `statement_at_sq` | `n = q^2`, `q ≥ 5` prime, `q^3 ∤ a(q-1)` |
| `statement_at_prime_pow` | `n = q^k`, `k ≥ 2`, `q ≥ 5` prime, `q^2 ∤ a(q-1)` |
| `a_zero` … `a_five` | `a(0..5) = 0, 1, 5, 49, 205, 5269` |

The hypotheses of the last three rows are finite checks for any given `q` or
`t`. The `q^2 ∤ a(q-1)` condition fails exactly when `v_q(H_2(q-1)) ≥ 2`;
classically this happens precisely for the Wolstenholme primes
(`q ∣ B_{q-3}`), of which `16843` and `2124679` are the known ones; the root
scan below finds no other such `q ≤ 2,642,245`.

## Computation

### Boyd-tree certificate for `5 ≤ q ≤ 2,642,245`

For each prime `q` the roots `1 ≤ m < q` are scanned for `H_2(m) ≡ 0 (mod q^2)`,
i.e. `v_q(H_2(m)) ≥ 2`. Every such root is recomputed exactly modulo `q^15`
(a root with `v_q ≥ 3` would be a counterexample) and its children are
evaluated modulo `q^13` through

\[
H_2(qs+r)=U_q(qs)+\sum_{\rho=1}^{r}\frac{1}{(qs+\rho)^2}+\frac{H_2(s)}{q^2},\qquad
U_q(qs)\equiv\sum_{j<P}(-1)^j(j+1)\,q^j F_j(s)\,A_{j+2}\pmod{q^P},
\]

with `F_j(s) = Σ_{i<s} i^j` and `A_t = Σ_{ρ=1}^{q-1} ρ^{-t}`; children with
`v_q = 2` would be expanded in turn.

Root scan, two independent C implementations (`192,723` primes, about
`2.4·10^11` root values each):

- `a007406_roots_mont.c` (R1): Montgomery arithmetic modulo `q^3`, batch
  inversion; reports `v_q ≥ 2` and `v_q ≥ 3` separately.
- `a007406_roots_lin.c` (R2): linear-time inverse table modulo `q^2`, plain
  128-bit remainders.

Both scanners report the same five roots with `v_q(H_2(m)) ≥ 2`, and R1
finds no root with `v_q ≥ 3`. The Python checker recomputes each root
modulo `q^15` and expands its children; `a007406_children.gp` repeats the
expansion independently:

| `q` | root `m` | `v_q(H_2(m))` | children with `v_q = 0 / 1 / ≥2` |
|---|---|---|---|
| 7 | 3 = (q−1)/2 | 2 | 6 / 1 / 0 |
| 16843 | 8421 = (q−1)/2 | 2 | 16841 / 2 / 0 |
| 16843 | 16842 = q−1 | 2 | 16842 / 1 / 0 |
| 2124679 | 1062339 = (q−1)/2 | 2 | 2124678 / 1 / 0 |
| 2124679 | 2124678 = q−1 | 2 | 2124679 / 0 / 0 |

Every tree therefore stops at depth 1, and `v_q(H_2(m)) ≤ 2` for all
`m ≥ 1` and all primes `5 ≤ q ≤ 2,642,245`. All five roots are explained by
the classical congruences `H_2(q−1) ≡ (2/3) q B_{q−3}` and
`H_2((q−1)/2) ≡ (7/3) q B_{q−3} (mod q^2)` (checked numerically here for
`q ≤ 300`): `q = 16843` and `q = 2124679` are the known Wolstenholme primes
(`q ∣ B_{q−3}`), and `q = 7` divides the factor `7/3`. Both scanners also
confirm `q ∣ a(q−1)` for every `q` and agree on the `385,031` roots
`m ≤ q−2` with `v_q ≥ 1`.

With `statement_le_of_padicValRat_le_two` (`Q = 2,642,245`) this gives the
conjecture for every `3 < n ≤ 5,284,491`; with
`statement_at_of_padicValRat_le_two` it also gives the conjecture for every
`n > 3` whose prime factors are all at most `2,642,245`.

### Direct checks from the definition

Two independent implementations compare `gcd(n, a(n-1))` with `A089026(n)`
straight from the definition, without the reduction:

- `a007406_certificate.py --direct-max N` keeps the integer
  `B(m) = lcm(1..m)^2 H_2(m)` and reads off
  `v_q(a(m)) = max(0, v_q(B(m)) - 2 v_q(lcm(1..m)))` for the prime factors `q`
  of `n = m+1`; `--fraction-max N` does the same with `fractions.Fraction`.
- `a007406_direct.gp` sums `1/k^2` in exact PARI/GP rationals and takes
  `gcd(numerator, n)`.

Both find no mismatch for `3 < n ≤ 10^6` (Python 12 min, PARI/GP 3.2 min).
This range is inside the `n ≤ 5,284,491` covered above; the point of these
runs is that they use no part of the reduction. They extend the
Eldar–Ordowski check (`n ≤ 10^5`).

### Trust model

- Lean: the reduction, the families above, and the implication "bounds for
  all primes `5 ≤ q ≤ Q` ⇒ conjecture for `3 < n ≤ 2Q+1`".
- Computation (not Lean): the bounds for `5 ≤ q ≤ 2,642,245`. The root scan is
  the only part without a CI re-run above `q = 20,000`; it was run with two
  independent implementations whose hit lists and prime counts agree. The
  child expansion is done by the Python checker and, independently, by
  `a007406_children.gp` (power sums from Bernoulli polynomials instead of
  Stirling numbers); both agree on every child valuation count.
- The checker's self-test compares the expansion with exact fractions and, for
  `q = 5, 7, 11, 13`, compares the tree with a brute-force list of all
  `m ≤ 700…2500` having `v_q(H_2(m)) ≥ 2`.

## Reproduction

All commands run from this directory with Python 3.8+ (standard library
only); timings are from an Apple M5 Max shared with other jobs, Python 3.12,
PARI/GP 2.19.0, Apple clang 21. CI runs the first command:

```bash
# Self-test; definitional checks for n <= 3000 (Fraction) and n <= 30000
# (scaled integers); complete Boyd trees for all 2260 primes 5 <= q <= 20000.
python3 a007406_certificate.py --self-test --fraction-max 3000 \
  --direct-max 30000 --tree-max 20000                          # about 7 s

# Re-verify the committed scanner logs: identical hit lists and counts, every
# hit recomputed mod q^15, its children expanded mod q^13.
python3 a007406_certificate.py --hits logs/roots_R1_2642245.txt \
  logs/roots_R2_2642245.txt                                    # about 30 s
```

Not in CI (outputs and timings in [`logs/RUNS.txt`](logs/RUNS.txt)):

```bash
# The two root scans (we used 2 threads each; any thread count works).
cc -O3 -std=c11 -pthread a007406_roots_mont.c -o /tmp/a007406_roots_mont
cc -O3 -std=c11 -pthread a007406_roots_lin.c -o /tmp/a007406_roots_lin
/tmp/a007406_roots_mont 5 2642245 4 > /tmp/a007406_R1.txt     # R1: 23 min wall, 38 CPU-min
/tmp/a007406_roots_lin 5 2642245 4 > /tmp/a007406_R2.txt      # R2: 81 min wall, 153 CPU-min
python3 a007406_certificate.py --hits /tmp/a007406_R1.txt /tmp/a007406_R2.txt

# Independent child expansion of the five hits (every line must show "v>=2: []").
printf 'children(7, 3, 13)\nchildren(16843, 8421, 13)\nchildren(16843, 16842, 13)\nchildren(2124679, 1062339, 13)\nchildren(2124679, 2124678, 13)\n' \
  | gp -q -D parisizemax=4G a007406_children.gp                # about 30 s

# Direct checks for 3 < n <= 10^6.
python3 a007406_certificate.py --direct-max 1000000            # 12 min
echo 'check(10^6)' | gp -q -D parisizemax=2G a007406_direct.gp # 3.2 min
```

## What is not claimed

- The conjecture itself. A composite `n > 5,284,491` is covered only when all
  its prime factors `q ≥ 5` are at most `2,642,245` (computation), when
  `n = tq` with `2 ≤ t ≤ 6`, when `n` is `5`-smooth, or under the explicit
  hypotheses of `statement_at_mul`, `statement_at_sq` and
  `statement_at_prime_pow`.
- The bounds for `q ≤ 2,642,245` are computational and not formalized in Lean;
  Lean proves only that such bounds imply the conjecture in the stated range.
- Above `q = 20,000` the completeness of the root hit list rests on the two C
  scanners; CI does not re-run them.

## Statement faithfulness

- `a` is upstream `OeisA7406.a` term for term:
  `(∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ) ^ 2).num.natAbs`. Since the sum
  is positive for `n ≥ 1`, `natAbs` of the numerator is the numerator, matching
  the OEIS definition (offset 1). The Lean value `a 0 = 0` (empty sum) is
  outside the OEIS range and does not enter the statement.
- `a089026` is upstream `OeisA89026.a` term for term (`if n.Prime then n else 1`),
  renamed so both definitions share one namespace. It matches A089026 for
  `n ≥ 1`; the extra value `a089026 0 = 1` does not enter the statement.
- `statement` is `∀ n : ℕ, 3 < n → Nat.gcd n (a (n - 1)) = a089026 n`, the
  proposition of `OeisA7406.conjecture (n) (hn : 3 < n)`. Under `3 < n`, the
  natural-number subtraction `n - 1` is ordinary subtraction, and the index
  `n - 1 ≥ 3` is inside the OEIS range.
- Upstream proves `a_0 … a_4` with `decide +native`; here the same values are
  proved by exact rational arithmetic (`a_zero` … `a_four`).

## Prior art

- The prime half is classical: `H_2(p-1) ≡ 0 (mod p)` for primes `p ≥ 5`
  (Wolstenholme's theorem; noted in the OEIS entry by T. D. Noe and
  J. Sondow).
- The OEIS entry reports a check up to `n = 10^5` (Eldar–Ordowski).
- The reduction to `q`-adic valuations and the tree pruning are standard
  techniques (Boyd's `p`-adic study of the harmonic numbers); the
  `q^2`-divisibility of `H_2(q-1)` is the classical Wolstenholme-prime
  condition. Nothing here is claimed to be new.
- The 2026-10-24 harvest triage had a Boyd-tree search to `q ≤ 3000` and a
  direct check to `n ≤ 2500`.

This result has not been reported to OEIS or upstream; any external
submission needs human approval.

## Files

- [`a007406_certificate.py`](a007406_certificate.py) — stdlib-only checker
  (definitional, scaled-integer, Boyd-tree and hit-file modes, self-test).
- [`a007406_roots_mont.c`](a007406_roots_mont.c),
  [`a007406_roots_lin.c`](a007406_roots_lin.c) — the two root scanners.
- [`a007406_children.gp`](a007406_children.gp) — independent child expansion.
- [`a007406_direct.gp`](a007406_direct.gp) — PARI/GP direct check.
- [`logs/`](logs/) — outputs and runtimes of the large runs.
- [`upstream/`](upstream/README.md) — upstream snapshots and provenance.
