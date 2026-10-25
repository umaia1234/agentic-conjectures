# Stretched Littlewood--Richardson negative-coefficient search

## Outcome

**Status: UNKNOWN / negative result of the search.**

No triple with a negative ordinary power-basis coefficient was found.  This is
not a proof of the King--Tollu--Toumazet positivity conjecture, nor is it an
exhaustion of all triples in the FrontierMath box.

The target was the [FrontierMath open problem](https://epoch.ai/frontiermath/open-problems/stretched-lr-coefficients):
find partitions `lambda`, `mu`, `nu`, each of length at most 7 and size at most
30, with `|lambda| = |mu| + |nu|`, for which

```text
t -> c^(t lambda)_(t mu,t nu)
```

has a negative coefficient in the ordinary monomial basis.  As of 11 August
2026 the problem page still labels this problem unsolved.  A recent relevant
result is [Ferudun, arXiv:2607.22301](https://arxiv.org/abs/2607.22301), which
proves coefficientwise positivity when all three partitions have at most four
parts; this motivated concentrating computation on ranks 5--7.

The [2026-10-24 extension](#exhaustive-sub-boxes-2026-10-24) computes every
stretched polynomial exactly for every triple of the box with at most six
parts, and for every triple with `|lambda| <= 27`.  Only the 7-part triples
with `28 <= |lambda| <= 30` remain unchecked.  The earlier random and Kostka
searches are described in the section after it.

## Exhaustive sub-boxes (2026-10-24)

Write `B(K, s)` for the set of triples `(lambda, mu, nu)` with
`|lambda| = |mu| + |nu| = s`, at most `K` parts in each partition and
`c^lambda_(mu,nu) > 0`, counted once per unordered pair `{mu, nu}` (the
coefficient is symmetric in `mu` and `nu`).  Triples with
`c^lambda_(mu,nu) = 0` are left out: by the saturation theorem (Knutson--Tao)
their stretched values vanish for every `t >= 1`.

**Result (exhaustive negative search).**  For every triple in the boxes below,
`P(t) = c^(t lambda)_(t mu,t nu)` was computed exactly as a polynomial, and no
coefficient of `t^0, ..., t^deg(P)` is negative.  In fact none of them is zero
either.

| parts at most | sizes `s` | pairs `{mu, nu}` | triples | regime A / B | max degree | shard wall time (sum) |
| ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 7 | 1–27 | 278,507 | 21,405,341 | 21,145,174 / 260,167 | 11 | 16,887 s |
| 6 | 28–30 | 253,072 | 27,587,273 | 27,178,465 / 408,808 | 10 | 14,040 s |
| 5 | 1–30 | 295,667 | 16,425,716 | 16,414,891 / 10,825 | 6 | 1,757 s |

The first two rows together cover **every triple of the FrontierMath box
with at most six parts**: sizes 1--27 lie inside the 7-part run, and sizes
28--30 were run separately.  They also cover every 7-part triple with
`|lambda| <= 27`.  The 5-part run is a separate pass over a sub-box that the
other two already cover; it has its own digests.  **Not covered:** triples
where `lambda` has exactly seven parts and `28 <= |lambda| <= 30`.  For
comparison, Ferudun (arXiv:2607.22301) proves positivity for at most four
parts.

The smallest positive coefficient divided by `P(1)` in each run is listed
below.  In every case it is the leading coefficient.  The minimum for each
size is in `exhaustive_summary.json`.

- 7 parts, sizes 1--27: `1/186278400`, for the coefficient of `t^11` (degree
  11, `P(1) = 14`) with `lambda = (8,7,5,3,2,1,1)`, `mu = (5,4,3,2,1)`,
  `nu = (4,3,2,2,1)`.
- 6 parts, sizes 28--30: `1/5806080`, for the coefficient of `t^10` (degree
  10, `P(1) = 16`) with `lambda = (9,8,6,4,2,1)`, `mu = nu = (5,4,3,2,1)`.
- 5 parts, sizes 1--30: `1/2880`, for the coefficient of `t^6` (degree 6,
  `P(1) = 8`) with `lambda = (7,6,4,2,1)`, `mu = nu = (4,3,2,1)`.

### Method ([exhaustive_search.py](./exhaustive_search.py), [lr_count.cpp](./lr_count.cpp))

1. **Enumeration and completeness.**  The unordered pairs `{mu, nu}` with at
   most `K` parts and `|mu| + |nu| = s` are generated in a fixed order.
   `lrcalc.mult(mu, nu, K)` (lrcalc 2.1, Python package) lists every `lambda`
   with at most `K` parts and `c > 0`.  Each list is certified complete by the
   GL_K dimension identity
   `sum_lambda c^lambda_(mu,nu) dim V_lambda = dim V_mu dim V_nu`.  The
   dimensions come from Weyl's formula, so this check uses no LR code.
2. **Degree bound.**  `deg P` is at most the dimension of the LR-tableau
   polytope.  `degree_bound` bounds that dimension rigorously.  It uses the
   affine space cut out by the row-sum and content equations together with
   the variables that are forced to vanish at every stretch by column
   strictness and the lattice-word condition.  The bound `D` actually used
   is the minimum over six orientations with the same stretched polynomial:
   `c^lambda_(mu,nu) = c^lambda_(nu,mu) = c^(mu')_(nu,lambda') = c^(nu')_(mu,lambda')`,
   where `p'` is the complement of `p` in the `len(lambda) x lambda_1`
   rectangle.  All four express the same invariant dimension for GL_n, and
   complements commute with stretching.
3. **Exact values.**  `lr_count.cpp` is a new exact counter.  It is a
   row-by-row LR-tableau dynamic program with unsigned 128-bit counts and
   overflow detection, and it shares no code with lrcalc or Normaliz.
   - *Regime A* (the values at `t = 1..D+1` sum to at most 20,000): lrcalc
     recomputes every one of these values.  `P` is interpolated from
     `t = 0..D`, and the value at `t = D+1` must lie on the interpolant.
   - *Regime B* (otherwise): Normaliz (PyNormaliz 2.24) computes the
     polytope's dimension `d`, which is checked to be at most `D`, and its
     Ehrhart quasi-polynomial, which must have period 1 and degree `d`.  The
     DP values at `t = 0..d` are interpolated, `t = d+1` is the extra check,
     and the interpolant must equal Normaliz's polynomial exactly.  The DP's
     cost differs by up to about 100x between the six orientations.  All six
     must agree at `t = 3`, and the one that visits the fewest DP nodes there
     computes the values at larger `t`.  lrcalc recomputes `P(1)`, and also
     `P(2)` whenever `P(2) <= 5,000,000` (every value when they sum to at most
     200,000).
4. Every coefficient is checked for sign.  Any disagreement between
   implementations aborts the run, and none occurred.
5. For each `(K, s)`, [exhaustive_summary.json](./exhaustive_summary.json)
   records the pair and triple counts, the regime counts, the degree
   histogram, the smallest positive coefficient divided by `P(1)`, and a
   digest.  The digest is the sum mod `2^256` of the SHA-256 of
   `"lambda|mu|nu|c_0,c_1,..."` over all triples, so a rerun can be compared
   without storing every polynomial.  `--merge` builds the file from the
   shard logs.

### Trust base

- Mathematics: the LR rule; `P` is the Ehrhart function of the LR polytope
  and is a polynomial (Derksen--Weyman, Rassart), so its degree is at most
  the polytope's dimension; saturation (only used to skip `c = 0`); the GL_n
  duality behind the six orientations; Weyl's dimension formula.
- Software: lrcalc 2.1 (enumeration and recomputation), Normaliz through
  PyNormaliz 2.24 (regime B), and the new DP.  Each polynomial rests on two
  independent computations.  In regime A, the DP and lrcalc both supply
  every interpolation value.  In regime B, the DP interpolation and
  Normaliz's Ehrhart polynomial must agree, and lrcalc spot-checks the
  values.
- In regime B the degree comes from Normaliz's dimension.  That value is
  checked against the rigorous bound `D`, against Normaliz's own polynomial,
  and against the DP value at `t = d+1`.  `d <= D` held in all 679,800
  regime-B computations.  It also held for 53,000 random triples of
  `B(7, 18..27)` that were compared with Normaliz separately; there the
  bound was sharp for 60% of them.
- Arithmetic is exact throughout: Python integers and fractions, and `u128`
  in the DP with overflow detection.

### Reproduction

```bash
uv pip install --python <python> lrcalc==2.1 pynormaliz==2.24
cd problems/stretched-lr
mkdir -p build
c++ -O2 -std=c++17 -shared -fPIC lr_count.cpp -o build/liblrcount.so
run() { python exhaustive_search.py --library build/liblrcount.so "$@"; }
# Round 1 (shared machine, load average 60-90 on 18 cores); seconds = wall time
run --rows 7 --min-size 1 --max-size 26 --shard 0 --shards 2 > r7a0.jsonl   # 3,431 s
run --rows 7 --min-size 1 --max-size 26 --shard 1 --shards 2 > r7a1.jsonl   # 3,456 s
run --rows 5 --min-size 1 --max-size 30 > r5.jsonl                          # 1,757 s
# Round 2 (load average 4-40); the B(6) logs' per-size times exclude a
# ~49-minute system sleep that their end-to-end wall times include
for k in 0 1 2 3; do
  run --rows 7 --min-size 27 --max-size 27 --shard $k --shards 4 > r7b$k.jsonl   # 2,080-3,409 s each
  run --rows 6 --min-size 28 --max-size 30 --shard $k --shards 4 > r6$k.jsonl    # 2,908-3,832 s each
done
python exhaustive_search.py --merge r7a0.jsonl r7a1.jsonl r5.jsonl r7b*.jsonl r6*.jsonl \
  > exhaustive_summary.json
```

To compute one polynomial:
`python exhaustive_search.py --library build/liblrcount.so --triple 8,6,5,4,3,2,1 6,5,4,3,2,1 3,2,1,1,1`.

The CI self-tests need neither lrcalc nor Normaliz:

```bash
python3 exhaustive_search.py --self-test --rows 7 --max-size 10
g++ -O3 -std=c++17 -shared -fPIC lr_count.cpp -o /tmp/liblrcount_selftest.so && \
  python3 exhaustive_search.py --self-test --rows 7 --max-size 10 \
    --library /tmp/liblrcount_selftest.so
```

Each takes a few seconds (2.7 s and 3.8 s here).  They check seven recorded
polynomials of degree 1--11.  Six are recomputed from scratch with the
pure-Python oracle
[lr_tableau_dp.py](./lr_tableau_dp.py).  The seventh is the degree-11
example of [closest_positive.json](./closest_positive.json).  Its recorded
values are checked for internal consistency, the pure-Python oracle
recomputes them for `t <= 3`, and with `--library` the C++ DP recomputes all
twelve.  The self-tests also recompute the whole sub-box `B(7, 1..10)`
(2,722 triples) and check its Weyl dimension identities.  Its per-size pair
and triple counts, degree histograms and digests must equal those in
`exhaustive_summary.json`.  With `--library`, `lr_count.cpp` must reproduce
every oracle value: in all six orientations for `t <= 4`, and in the
orientation the search would choose for larger `t`.

### What is not claimed

- This is not an exhaustion of the FrontierMath box.  The 7-part triples with
  `28 <= |lambda| <= 30` remain.  The current enumeration would also revisit
  the 6-part triples, and at the observed growth of about 2x per unit of
  size this would take roughly 40 CPU-hours.
- It is not a proof of the conjecture, and there is no novelty claim.
  Computations over comparable ranges may well exist in the literature.
- The individual polynomials are not stored, only counts, histograms,
  extremal examples and digests.  Regime B also relies on Normaliz for the
  degree, as described above.

## What was computed

There were three complementary searches.

1. Classic Anders Buch `lrcalc` 1.2 was called in-process through its C ABI.
   For 242,890 nonzero random triples, values at enough consecutive integer
   stretches to meet the ambient hive-dimension bound were interpolated over
   exact Python `Fraction`s.  Two further stretch values were evaluated and
   checked against every interpolation.
2. [`lrcalc-rs`](https://github.com/PerAlexandersson/lrcalc-rs) commit
   `17efa93108512abb4cbb8db721060e8819639f77` was built and its six
   `lr_ehrhart` tests passed.  Nine million random trials produced 3,463,330
   nonzero dimension screens.  The 85,711 triples meeting the chosen
   dimension thresholds were interpolated using exact `u128` full/interior
   counts and `BigRational` coefficients.  No arithmetic error and no negative
   coefficient occurred.
3. The stretched-Kostka slice was exhausted under the prompt bounds.  Write
   `lambda_i = beta_i + ... + beta_r` and `mu = (lambda_2,...,lambda_r)`;
   then `c^lambda_(mu,alpha) = K_(alpha,beta)`.  All 10,312 pairs with
   `5 <= len(beta) <= 7`, `len(alpha) <= 7`, and
   `sum(i*beta_i) <= 30` were tested.  Of these, 3,129 were nonzero.  No
   negative coefficient occurred.

Exact per-run seeds, thresholds, dimension histograms, and trust boundaries
are in [search_summary.json](./search_summary.json).

## Independent LR oracle

[lr_tableau_dp.py](./lr_tableau_dp.py) is a pure-Python arbitrary-precision
implementation of the Littlewood--Richardson tableau rule.  It does not call
either lrcalc implementation.  A weakly increasing row is represented by its
content vector; the dynamic program enforces column strictness and the lattice
word inequalities row by row.

It passed:

- five hand-checkable cases, including
  `c^(3,2,1)_((2,1),(2,1)) = 2` and its stretch-2 value 3;
- 3,000 random base-value comparisons with classic `lrcalc`;
- 1,500 random stretched comparisons (`t = 1,2,3`) with classic `lrcalc`;
- all twelve positive-stretch values `t = 1,...,12` for the recorded
  degree-11 example in [closest_positive.json](./closest_positive.json).

There were no mismatches.  The `t=12` value is an extra point beyond the
degree-11 interpolation data `t=0,...,11`.

Run its self-test with:

```bash
python problems/stretched-lr/lr_tableau_dp.py --self-test
```

## A strongly cross-checked positive example

The smallest normalized positive coefficient retained in the exhaustive
Kostka slice was

```python
lambda_ = [8, 6, 5, 4, 3, 2, 1]
mu      = [6, 5, 4, 3, 2, 1]
nu      = [3, 2, 1, 1, 1]
```

Its polynomial is

```text
1
+ (50317/13860)t
+ (2159/360)t^2
+ (15769/2592)t^3
+ (6073/1440)t^4
+ (108157/51840)t^5
+ (719/960)t^6
+ (23587/120960)t^7
+ (13/360)t^8
+ (47/10368)t^9
+ (1/2880)t^10
+ (7/570240)t^11.
```

Every coefficient is positive.  The values at `t=1,...,6` agree with classic
`lrcalc`, and all values at `t=1,...,12` agree with the independent tableau
DP.  This example is recorded to expose the search's numerical boundary, not
as a purported solution.

Among the later three-million-trial mixed random batch, the smallest retained
positive coefficient was `1/907200` (the leading coefficient of a degree-10
polynomial); its complete data are in `search_summary.json`.  Zero coefficients
also occurred frequently in lower-dimensional/degenerate polynomials, but no
coefficient was negative.

## Reproduction

### Classic lrcalc path

On Debian/Ubuntu, obtain a local, non-system installation:

```bash
mkdir -p /tmp/stretched_lr_lrcalc
cd /tmp/stretched_lr_lrcalc
apt download lrcalc liblrcalc1t64 liblrcalc-dev
for package in ./*.deb; do dpkg-deb -x "$package" root; done
```

Then run a smoke test or a random search:

```bash
python problems/stretched-lr/search_stretched.py \
  --library /tmp/stretched_lr_lrcalc/root/usr/lib/x86_64-linux-gnu/liblrcalc.so.1.0.1 \
  --self-test

python problems/stretched-lr/search_stretched.py \
  --library /tmp/stretched_lr_lrcalc/root/usr/lib/x86_64-linux-gnu/liblrcalc.so.1.0.1 \
  --mode random --rows 7 --max-total 30 --iterations 100000 --seed 20260811
```

Without `--library`, the script now uses the `lrcalc` Python package instead
(`uv pip install lrcalc==2.1`, as in the exhaustive search below), e.g.
`python problems/stretched-lr/search_stretched.py --self-test`.

Classic `lrcalc` returns signed 64-bit counts.  The script treats a negative or
decreasing stretched value as suspected overflow, but a positive wrap cannot
be ruled out internally.  This limitation is why the large reported search
also used the Rust `u128`/`BigRational` route.

### Exact Rust search path

```bash
git clone https://github.com/PerAlexandersson/lrcalc-rs.git /tmp/lrcalc-rs
git -C /tmp/lrcalc-rs checkout 17efa93108512abb4cbb8db721060e8819639f77
cp problems/stretched-lr/rust_random_search.rs \
  /tmp/lrcalc-rs/src/bin/search_negative.rs
cp problems/stretched-lr/rust_kostka_search.rs \
  /tmp/lrcalc-rs/src/bin/search_kostka_negative.rs
cd /tmp/lrcalc-rs
cargo test --release lr_ehrhart::tests
cargo build --release --bin search_negative --bin search_kostka_negative
```

The random binary's arguments are
`SEED ITERATIONS ROWS MIN_TOTAL MAX_TOTAL MIN_DIMENSION GENERATOR`, where
`GENERATOR` is `grown` or `mixed`.  The six reported commands were:

```bash
./target/release/search_negative 5005005 2000000 5 12 30 3 grown
./target/release/search_negative 6006006 2000000 6 12 30 5 grown
./target/release/search_negative 7007007 2000000 7 12 30 7 grown
./target/release/search_negative 51515151 1000000 5 12 30 3 mixed
./target/release/search_negative 61616161 1000000 6 12 30 5 mixed
./target/release/search_negative 71717171 1000000 7 12 30 7 mixed
./target/release/search_kostka_negative
```

## Limitations and next useful direction

- Random trials are not an exhaustive enumeration and include duplicates.
- The dimension thresholds deliberately skip many low-dimensional Rust
  polynomials; independent classic-lrcalc runs sampled those regimes instead.
- The Kostka calculation is exhaustive only for that structured subfamily.
- `u128` would eventually overflow, although no Rust run reported an arithmetic
  error here.
- The tracked "smallest positive" statistic is not a proof of a global
  minimum and was not retained during the first six-million-trial batch.

A materially different continuation would optimize specifically for a low
*interior* power-basis coefficient (especially the linear coefficient in rank
5), rather than merely resampling partitions or minimizing the leading
coefficient.  The present run was stopped after the final seeded batch, with
no search process left running.
