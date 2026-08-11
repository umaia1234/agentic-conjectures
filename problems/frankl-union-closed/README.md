**English** | [한국어](README.ko.md)

# Frankl's union-closed sets conjecture

Status checked as of: 2026-08-11.

## Problem

The question is whether, for every finite union-closed family `F` other than
the one consisting solely of `{empty set}`, there always exists an element
contained in at least `|F|/2` of the member sets.

## Current status and known partial results

A 2026 journal-published paper also treats this as a conjecture and presents
new necessary conditions that a minimal counterexample must satisfy. The
known computer-assisted results and the general lower bound are as follows.

- The conjecture holds for ground sets of size at most 12.
- For general families, a dimension-free lower bound has been proved: at
  least one element is contained in about `0.38234 |F|` of the sets.

Therefore ground set size 13 is the finite case immediately after the fully
verified range. This does not mean that 13 is known to be the size of a
minimal counterexample.

## Computational perspective

For ground set size 13 there are 8,192 possible member sets. Union closure,
per-element frequency upper bounds, and isomorphism elimination can be put
together into SAT, ILP, or BDD. Interpreting a computational result as a
general theorem requires exhaustiveness over all cases and a certifiable
UNSAT proof.

## FormalConjectures upstream

The [local upstream snapshot](upstream/README.md) preserves both the Lean
statement of the general Frankl conjecture and that of the known 12-element
variant. The `sorry` in the two declarations is only a statement marker, not
a formal proof inside that file, and this directory likewise does not
resolve the 13-element case.

## Evidence

- [Bouchard, *Le Matematiche* 81(1), 2026](https://arxiv.org/abs/2503.00277)
- [Vuckovic--Zivkovic's 12-element computational proof](https://ipsitransactions.org/journals/papers/tir/2017jan/p9.pdf)
- [Yu's `0.38234` lower bound](https://www.mdpi.com/1099-4300/25/5/767)
