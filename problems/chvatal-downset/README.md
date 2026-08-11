# Chvatal downset conjecture: saturated-search reduction

This directory records a bounded attack on Chvatal's conjecture for
intersecting subfamilies of downsets.  It does **not** claim a new case of the
conjecture.

## Statement

For a finite downset `D` (if `A in D` and `B subseteq A`, then `B in D`), let

- `alpha(D)` be the largest size of a pairwise-intersecting subfamily of `D`;
- `Delta(D) = max_i |{A in D : i in A}|` be the size of its largest star.

Chvatal's conjecture is

```text
alpha(D) <= Delta(D) for every finite downset D.
```

The general conjecture remains open.  A certificate-producing integer
programming computation proves it when the ground set has at most seven
elements.  The same paper reports only a floating-point solve for eight
elements:

- L. Eifler, A. Gleixner, J. Pulaj, *A Safe Computational Framework for
  Integer Programming Applied to Chvatal's Conjecture*, ACM TOMS 48 (2022),
  <https://doi.org/10.1145/3485630>.
- Preprint and public computational description:
  <https://optimization-online.org/2018/09/6802/>.

Two other reductions used by `generate_cnf.py --reduced` are literature
results recorded in that paper: rank at most three is settled, and an
intersecting family containing a singleton or a pair generates no
counterexample.  The ground-set fixings also assume all smaller ground sets
have already been settled.

## Saturation lemma

The following reduction is elementary, but it is useful in a SAT search.

**Lemma.** If Chvatal's conjecture has a counterexample, then it has a
counterexample `(D, Y)` such that

1. `D = down(Y) := {S : S subseteq T for some T in Y}`;
2. `Y` is a maximum-cardinality intersecting subfamily of `D`;
3. for every `T in D \ Y`, some `S in Y` is disjoint from `T`.

**Proof.** Start with a counterexample `D0` and choose a maximum-cardinality
intersecting subfamily `Y` of `D0`.  Put `D = down(Y)`.  Because `D0` is a
downset and `Y subseteq D0`, we have `Y subseteq D subseteq D0`.  Passing from
`D0` to `D` cannot increase any star, while it leaves `|Y|` unchanged.
Consequently `|Y| > Delta(D0) >= Delta(D)`, so `(D, Y)` is still a
counterexample.  Any intersecting subfamily of `D` is also one of `D0`, hence
`Y` remains maximum in `D`.  Finally, if `T in D \ Y` met every member of
`Y`, then `Y union {T}` would be an intersecting subfamily of `D` larger than
`Y`, a contradiction.  This proves all three assertions.  QED.

In Boolean variables `x_T = [T in D]` and `y_T = [T in Y]`, assertion 3 is
the clause

```text
not x_T or y_T or (or_{S intersect T = empty, S nonempty} y_S).
```

Assertion 1 is encoded in both directions:

```text
y_T -> x_S                         for every S subseteq T,
x_S -> or_{T superseteq S} y_T.
```

For each ground element `i`, the strict counterexample inequality
`|Y| >= |star_i(D)| + 1` is encoded as the cardinality constraint

```text
sum_{S nonempty} y_S + sum_{S contains i} (not x_S) >= 2^(n-1) + 1.
```

Thus an UNSAT result excludes every counterexample satisfying the stated
reductions.  A SAT result is decoded and checked before being printed.

## FormalConjectures source

The exact upstream Lean statement is preserved in the local
[FormalConjectures snapshot](upstream/README.md).  It states the full conjecture
with `sorry`; the bounded searches here do not prove that declaration.

## Reproduction

The generator uses PySAT.  A disposable environment keeps the dependency out
of the repository:

```bash
python -m venv /tmp/chvatal-sat-venv
/tmp/chvatal-sat-venv/bin/pip install "python-sat[pblib]"
/tmp/chvatal-sat-venv/bin/python \
  problems/chvatal-downset/generate_cnf.py \
  --n 6 --reduced --encoding cardnet --solve
```

To materialize DIMACS instead of solving it in-process:

```bash
/tmp/chvatal-sat-venv/bin/python \
  problems/chvatal-downset/generate_cnf.py \
  --n 6 --reduced --encoding cardnet \
  --output /tmp/chvatal_n6.cnf
```

A quick semantic smoke test is:

```bash
/tmp/chvatal-sat-venv/bin/python \
  problems/chvatal-downset/generate_cnf.py --self-test
```

## Trust boundary and outcome

`n6_solver_result.json` records the observed `n=6` reproduction.  CaDiCaL
reported UNSAT, but no independently checked DRAT/LRAT proof was produced.
It is therefore a **solver reproduction result**, not a new certified theorem.

The attempted `n=8` MILP runs found no positive counterexample incumbent but
did not close the dual bound.  Nine symmetry-split feasibility runs also hit
their time limits without finding a counterexample and without proving
infeasibility.  `n8_attempt_summary.md` gives the exact limits.  The eight
element case is therefore **unresolved by this attempt**.
