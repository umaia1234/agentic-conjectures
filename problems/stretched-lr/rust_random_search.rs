//! Copy this file to `src/bin/search_negative.rs` in lrcalc-rs commit
//! 17efa93108512abb4cbb8db721060e8819639f77.

use lrcalc::lr_ehrhart::{lr_stretch_dimension, lr_stretch_h_vector};
use lrcalc::lrcoef::lrcoef;
use num_rational::BigRational;
use num_traits::{Signed, Zero};
use std::collections::BTreeMap;
use std::env;
use std::time::Instant;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn range(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next() as usize % (hi - lo))
    }
}

fn random_partition(rng: &mut Rng, total: usize, rows: usize, mode: usize) -> Vec<i32> {
    let mut values = vec![0i32; rows];
    if mode == 0 {
        for _ in 0..total {
            values[rng.range(0, rows)] += 1;
        }
    } else {
        let mut remaining = total;
        let mut used = 0usize;
        while remaining > 0 && used < rows {
            let part = if used + 1 == rows {
                remaining
            } else {
                rng.range(1, remaining + 1)
            };
            values[used] = part as i32;
            remaining -= part;
            used += 1;
        }
    }
    values.sort_unstable_by(|a, b| b.cmp(a));
    while values.last() == Some(&0) {
        values.pop();
    }
    values
}

fn grow_partition(rng: &mut Rng, inner: &[i32], boxes: usize, rows: usize) -> Vec<i32> {
    let mut outer = inner.to_vec();
    outer.resize(rows, 0);
    for _ in 0..boxes {
        let addable = (0..rows)
            .filter(|&row| row == 0 || outer[row] < outer[row - 1])
            .collect::<Vec<_>>();
        let row = addable[rng.range(0, addable.len())];
        outer[row] += 1;
    }
    while outer.last() == Some(&0) {
        outer.pop();
    }
    outer
}

fn contains(outer: &[i32], inner: &[i32]) -> bool {
    inner
        .iter()
        .enumerate()
        .all(|(index, &part)| outer.get(index).copied().unwrap_or(0) >= part)
}

fn scale(parts: &[i32], stretch: u64) -> Vec<i32> {
    parts.iter().map(|&part| part * stretch as i32).collect()
}

fn evaluate(coefficients: &[BigRational], value: i64) -> BigRational {
    let value = BigRational::from_integer(value.into());
    coefficients
        .iter()
        .rev()
        .fold(BigRational::zero(), |result, coefficient| {
            result * &value + coefficient
        })
}

fn main() {
    let args = env::args().collect::<Vec<_>>();
    let seed = args
        .get(1)
        .and_then(|value| value.parse().ok())
        .unwrap_or(0x123456789abcdef);
    let iterations = args
        .get(2)
        .and_then(|value| value.parse().ok())
        .unwrap_or(100_000usize);
    let rows = args
        .get(3)
        .and_then(|value| value.parse().ok())
        .unwrap_or(7usize);
    let total_min = args
        .get(4)
        .and_then(|value| value.parse().ok())
        .unwrap_or(12usize);
    let total_max = args
        .get(5)
        .and_then(|value| value.parse().ok())
        .unwrap_or(30usize);
    let min_dimension = args
        .get(6)
        .and_then(|value| value.parse().ok())
        .unwrap_or(1usize);
    let generator = args.get(7).map(String::as_str).unwrap_or("mixed");
    assert!(matches!(generator, "grown" | "mixed"));
    let mut rng = Rng(seed);
    let started = Instant::now();
    let mut positive = 0usize;
    let mut interpolated = 0usize;
    let mut errors = 0usize;
    let mut dimensions = BTreeMap::<usize, usize>::new();
    let mut best: Option<(
        BigRational,
        usize,
        Vec<i32>,
        Vec<i32>,
        Vec<i32>,
        BigRational,
    )> = None;

    for iteration in 1..=iterations {
        let total = rng.range(total_min, total_max + 1);
        let left_sum = rng.range(1, total);
        let right_sum = total - left_sum;
        let inner_mode = rng.next() as usize % 2;
        let content_mode = rng.next() as usize % 2;
        let mut inner = random_partition(&mut rng, left_sum, rows, inner_mode);
        let mut content = random_partition(&mut rng, right_sum, rows, content_mode);
        if rng.next() & 1 == 1 {
            std::mem::swap(&mut inner, &mut content);
        }
        let outer = if generator == "grown" || rng.next() & 1 == 0 {
            grow_partition(
                &mut rng,
                &inner,
                content.iter().map(|&part| part as usize).sum(),
                rows,
            )
        } else {
            let mode = rng.next() as usize % 2;
            random_partition(&mut rng, total, rows, mode)
        };
        if !contains(&outer, &inner) {
            continue;
        }

        let dimension = match lr_stretch_dimension(&outer, &inner, &content) {
            Ok(Some(dimension)) => dimension,
            Ok(None) => continue,
            Err(_) => {
                errors += 1;
                continue;
            }
        };
        positive += 1;
        *dimensions.entry(dimension).or_default() += 1;
        if dimension < min_dimension {
            continue;
        }

        let polynomial = match lr_stretch_h_vector(&outer, &inner, &content) {
            Ok(polynomial) => polynomial,
            Err(_) => {
                errors += 1;
                continue;
            }
        };
        interpolated += 1;
        let negative = polynomial
            .coefficients
            .iter()
            .enumerate()
            .filter(|(_, coefficient)| coefficient.is_negative())
            .collect::<Vec<_>>();
        if !negative.is_empty() {
            let extra_t = polynomial.dimension as u64 + 2;
            let direct = lrcoef(
                &scale(&outer, extra_t),
                &scale(&inner, extra_t),
                &scale(&content, extra_t),
            );
            let predicted = evaluate(&polynomial.coefficients, extra_t as i64);
            println!(
                "HIT iteration={iteration} outer={outer:?} inner={inner:?} content={content:?}"
            );
            println!(
                "dimension={} coefficients={:?}",
                polynomial.dimension, polynomial.coefficients
            );
            println!(
                "negative={negative:?} sample_points={:?}",
                polynomial.sample_points
            );
            println!("extra_t={extra_t} direct={direct:?} predicted={predicted}");
            return;
        }

        let value_at_one = evaluate(&polynomial.coefficients, 1);
        if !value_at_one.is_zero() {
            for (index, coefficient) in polynomial.coefficients.iter().enumerate().skip(1) {
                if coefficient.is_positive() {
                    let score = coefficient / &value_at_one;
                    if best.as_ref().is_none_or(|record| score < record.0) {
                        best = Some((
                            score,
                            index,
                            outer.clone(),
                            inner.clone(),
                            content.clone(),
                            coefficient.clone(),
                        ));
                    }
                }
            }
        }
        if iteration % 10_000 == 0 {
            println!(
                "progress iteration={iteration} positive={positive} interpolated={interpolated} errors={errors} dimensions={dimensions:?} seconds={:.3}",
                started.elapsed().as_secs_f64()
            );
        }
    }
    println!(
        "DONE iterations={iterations} positive={positive} interpolated={interpolated} errors={errors} dimensions={dimensions:?} seconds={:.3}",
        started.elapsed().as_secs_f64()
    );
    println!("BEST normalized_positive={best:?}");
}
