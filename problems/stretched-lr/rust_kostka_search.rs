//! Exhaustive stretched-Kostka slice.  Copy to `src/bin/search_kostka_negative.rs`
//! in lrcalc-rs commit 17efa93108512abb4cbb8db721060e8819639f77.

use lrcalc::lr_ehrhart::lr_stretch_h_vector;
use num_rational::BigRational;
use num_traits::{Signed, Zero};
use std::collections::BTreeMap;
use std::time::Instant;

fn partitions(
    sum: i32,
    max_part: i32,
    max_len: usize,
    prefix: &mut Vec<i32>,
    output: &mut Vec<Vec<i32>>,
) {
    if sum == 0 {
        output.push(prefix.clone());
        return;
    }
    if max_len == 0 {
        return;
    }
    for part in (1..=sum.min(max_part)).rev() {
        prefix.push(part);
        partitions(sum - part, part, max_len - 1, prefix, output);
        prefix.pop();
    }
}

fn all_partitions(sum: i32, max_len: usize) -> Vec<Vec<i32>> {
    let mut output = Vec::new();
    partitions(sum, sum, max_len, &mut Vec::new(), &mut output);
    output
}

fn main() {
    let started = Instant::now();
    let mut beta_count = 0usize;
    let mut tested = 0usize;
    let mut positive = 0usize;
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

    for sum in 1..=30 {
        for beta in all_partitions(sum, 7) {
            if beta.len() < 5 {
                continue;
            }
            let weighted_sum: i32 = beta
                .iter()
                .enumerate()
                .map(|(index, &part)| (index as i32 + 1) * part)
                .sum();
            if weighted_sum > 30 {
                continue;
            }
            beta_count += 1;
            let outer = (0..beta.len())
                .map(|index| beta[index..].iter().sum())
                .collect::<Vec<i32>>();
            let inner = outer[1..].to_vec();
            for content in all_partitions(sum, 7) {
                tested += 1;
                match lr_stretch_h_vector(&outer, &inner, &content) {
                    Ok(polynomial) if polynomial.sample_points.is_empty() => continue,
                    Ok(polynomial) => {
                        positive += 1;
                        *dimensions.entry(polynomial.dimension).or_default() += 1;
                        let negative = polynomial
                            .coefficients
                            .iter()
                            .enumerate()
                            .filter(|(_, coefficient)| coefficient.is_negative())
                            .collect::<Vec<_>>();
                        if !negative.is_empty() {
                            println!(
                                "HIT outer={outer:?} inner={inner:?} content={content:?} beta={beta:?}"
                            );
                            println!(
                                "dimension={} coefficients={:?}",
                                polynomial.dimension, polynomial.coefficients
                            );
                            println!(
                                "negative={negative:?} sample_points={:?}",
                                polynomial.sample_points
                            );
                            return;
                        }
                        let value_at_one = polynomial
                            .coefficients
                            .iter()
                            .cloned()
                            .fold(BigRational::zero(), |sum, coefficient| sum + coefficient);
                        for (index, coefficient) in
                            polynomial.coefficients.iter().enumerate().skip(1)
                        {
                            if coefficient.is_positive() && !value_at_one.is_zero() {
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
                    Err(_) => errors += 1,
                }
            }
            if beta_count % 10 == 0 {
                println!(
                    "progress beta_count={beta_count} tested={tested} positive={positive} errors={errors} dimensions={dimensions:?} seconds={:.3}",
                    started.elapsed().as_secs_f64()
                );
            }
        }
    }
    println!(
        "DONE beta_count={beta_count} tested={tested} positive={positive} errors={errors} dimensions={dimensions:?} seconds={:.3}",
        started.elapsed().as_secs_f64()
    );
    println!("BEST normalized_positive={best:?}");
}
