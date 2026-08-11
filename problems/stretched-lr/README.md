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
