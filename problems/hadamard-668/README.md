**English** | [한국어](README.ko.md)

# Hadamard matrix of order 668

Status checked as of: 2026-08-11.

## Problem

The question is whether, among `668 x 668` matrices `H` with entries `+1` or
`-1`, there exists one satisfying

```text
H H^T = 668 I
```

## Current status and known partial results

The Hadamard conjecture predicts the existence of such matrices at every
order that is a multiple of 4. A 2023 peer-reviewed paper and a 2026 status
report both record 668 as the smallest unresolved order.

On the sufficient-condition route of searching for a Legendre pair of
length 333, the 2026 status report reports the following.

- It exhaustively enumerated the 12,017,243 PSD-compatible configurations
  of the 9-compression.
- The best `L1` PSD error obtained from the 37-compression heuristic
  was 236.

It contains no new result deciding the existence or nonexistence of an
order-668 matrix.

## Caution on logical scope

If a Legendre pair of length 333 exists, a Hadamard matrix of order 668 can
be constructed. However, an arbitrary Hadamard matrix of order 668 is not
necessarily of this form. Therefore the "equivalently" in the status
report's abstract must not be used as a logical equivalence for the full
existence problem.

Each structured subspace — Legendre-pair, Goethals--Seidel, Williamson, and
so on — can be searched with PSD filters, meet-in-the-middle, SAT, or SMT.
An UNSAT in one construction class is not a nonexistence proof for the full
Hadamard problem.

## FormalConjectures upstream

The [local upstream snapshot](upstream/README.md) preserves the Lean
declaration asking for existence at exactly `k=167`, i.e. order 668. That
declaration is an open problem statement containing `sorry`, and the
structured-search status above is not its answer.

## Evidence

- [Three-dimensional Hadamard matrices of Paley type](https://www.sciencedirect.com/science/article/pii/S107157972300148X),
  *Finite Fields and Their Applications* 92 (2023), 102306.
- Chojecki,
  [Computational Search for a Hadamard Matrix of Order 668 via Legendre Pairs of Length 333](https://www.ulam.ai/research/frontier-had.pdf),
  March 2026 (non-peer-reviewed status report).
