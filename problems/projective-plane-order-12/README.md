**English** | [한국어](README.ko.md)

# Finite projective plane of order 12

Date of verification: 2026-08-11.

## Problem

We ask whether a finite projective plane of order 12 exists. This is
equivalent to the existence of a symmetric `2-(157,13,1)` design. Using
a `157 x 157` zero-one incidence matrix `A` whose row and column sums
are 13, the condition can be written as

```text
A A^T = 12 I + J
```

## Current status and known partial results

The primary 2026 sources record 12 as the smallest order whose existence
status is unknown. A 2023 paper ruled out collineation groups of
order 4, and combined with earlier results the only possible full
collineation group orders are 1, 2, and 3.

This directory records only the problem and its character as a
computational candidate, and claims no new existence or nonexistence
result.

## Computational perspective

The incidence condition lends itself well to formulation as exact cover
or SAT, but the number of variables is large. Because of the known
symmetry-exclusion results, the comparatively easy searches that assume
a large cyclic symmetry are already blocked. Hence a canonical search
handling trivial or very small automorphism groups is the key
bottleneck.

## FormalConjectures upstream

The [local upstream snapshot](upstream/README.md) preserves the `eq_12`
Lean declaration of Erdős problem 723 and the pinned commit information.
The declaration is an existence-problem statement with a `sorry`, and
this directory provides no new existence or nonexistence result.

## References

- Alexeev--Mixon,
  [Forbidden Sidon subsets of perfect difference sets](https://arxiv.org/html/2510.19804v2)
  (2026 edition).
- Akiyama--Suetake--Tanaka,
  [Projective planes of order 12 do not have a collineation group of order 4](https://doi.org/10.1002/jcd.21869),
  *Journal of Combinatorial Designs* 31 (2023), 87--123.
