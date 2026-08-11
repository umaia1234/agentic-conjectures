**English** | [한국어](README.ko.md)

# Conway 99-graph

Status checked as of: 2026-08-11.

## Problem

The question is whether a strongly regular graph

```text
srg(99,14,1,2)
```

exists. That is, it is the existence problem of a graph with 99 vertices in
which every vertex has degree 14, any two adjacent vertices have 1 common
neighbor, and any two non-adjacent vertices have 2 common neighbors.
Equivalently, every edge lies in exactly one triangle and every non-edge
lies in exactly one 4-cycle.

## Current status and known partial results

A 2025 peer-reviewed paper also explicitly states this existence problem as
unresolved. Writing `G` for the automorphism group of a putative graph, that
paper proved the following without computer assistance.

- If `2 | |G|`, then `|G| | 6`.
- If `7 | |G|`, then `G` is the cyclic group `Z_7`.

It contains no new computational result deciding existence or nonexistence.
This document records the statement as a candidate for future computational
search and the restrictions already known.

## Computational perspective

Fixing one vertex, the remaining vertices decompose by distance layers as
`1 + 14 + 84`. Regularity, the common-neighbor equations, and canonical
augmentation can be fed directly into SAT, integer programming, or
exhaustive search. However, since the actual graph may have almost no
symmetry, ruling out subspaces that assume a large automorphism group cannot
by itself resolve the whole problem.

## FormalConjectures upstream

The [local upstream snapshot](upstream/README.md) preserves the exact Lean
statement for 99 vertices and the pinned commit information. That file is a
problem statement containing `sorry`, and the status survey here likewise
does not decide existence or nonexistence.

## Evidence

- M. Cesarz and A. Woldar,
  [On the automorphism group of a putative Conway 99-graph](https://alco.centre-mersenne.org/articles/10.5802/alco.418/),
  *Algebraic Combinatorics* 8 (2025), 379--398.
