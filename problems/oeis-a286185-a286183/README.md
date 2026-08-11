**English** | [한국어](README.ko.md)

# OEIS A286185 & A286183 — connected induced subgraphs of Möbius ladders and antiprisms

## Verdict

For the two `2n`-vertex graphs below, the closed form conjectured on OEIS is
**true**, and so are the order-6 linear recurrence and the generating function
conjectured on the same entry (both follow from the closed form).

| | | conjectured closed form | now |
|---|---|---|---|
| [A286185](https://oeis.org/A286185) | Möbius ladder | `a(n) = A002203(n) + 3n·A000129(n) - n - 1` | **proved** for all `n ≥ 1` |
| [A286183](https://oeis.org/A286183) | antiprism | `a(n) = A005248(n) - 2n + 2n·A001906(n)` | **proved** for all `n ≥ 1` |

The proof is in [PROOF.md](PROOF.md). It is a single column transfer-matrix
argument that also re-derives the third member of the family,
[A286182](https://oeis.org/A286182) (prism graph) — where the same closed form
is **already a published theorem**, so that case serves here only as a
validation of the method. See *Prior art* below.

## The original statements

All three entries were created by Giovanni Resta on 04 May 2017. Quoting the
snapshots preserved in [`upstream/`](upstream/README.md) (OEIS versions #26–#27,
retrieved 2026-08-12), each formula still carries the word `(conjectured)`:

> **A286185** — Number of connected induced (non-null) subgraphs of the Möbius
> ladder graph with 2n nodes.
> `a(n) = 6*a(n-1) - 11*a(n-2) + 4*a(n-3) + 5*a(n-4) - 2*a(n-5) - a(n-6), for n>6 (conjectured).`
> `a(n) = Lucas(n, 2) + 3*n*Fibonacci(n, 2) - n - 1, where Lucas(n, 2) = A002203(n) and Fibonacci(n, 2) = A000129(n) (conjectured). - Eric W. Weisstein, May 08 2017`
> `G.f. (subject to the above conjectures. In fact all three conjectures are equivalent): (3*x-3*x^2-2*x^3-4*x^4+3*x^5-x^6)/(1-3*x+x^2+x^3)^2. - Robert Israel, May 08 2017`

> **A286183** — Number of connected induced (non-null) subgraphs of the
> antiprism graph with 2n nodes.
> `a(n) = 8*a(n-1) - 24*a(n-2) + 34*a(n-3) - 24*a(n-4) + 8*a(n-5) - a(n-6), for n > 6 (conjectured).`
> `a(n) = A005248(n) - 2*n + 2*n*A001906(n) (conjectured). - Eric W. Weisstein, May 08 2017`
> `G.f.: x*(3 - 9*x + 12*x^2 - 15*x^3 + 9*x^4 - 2*x^5) / ((1 - x)^2*(1 - 3*x + x^2)^2) (conjectured). - Colin Barker, May 30 2017`

## Method, in one paragraph

Split a vertex subset `S` into its `n` *columns* `c_i = {r : (i,r) ∈ S}`. Every
occupied column is internally connected and all other edges join cyclically
consecutive columns, so `S` is connected exactly when the *column graph* is
(Lemma 0 of [PROOF.md](PROOF.md)). If some column is empty the occupied columns
must form an arc, and arcs are counted by powers of a `3×3` transfer matrix; if
every column is occupied the column graph is the `n`-cycle minus the unlinked
adjacencies, which is connected iff at most one adjacency is unlinked, giving a
trace term plus `n` times a single matrix entry. The three families differ only
in the transfer matrix: `M = [[1,0,1],[0,1,1],[1,1,1]]` for the prism, the same
`M` with a row-swap `P_σ` inserted at the seam for the Möbius ladder, and
`Mₐ = [[1,1,1],[0,1,1],[1,1,1]]` for the antiprism. Their spectra
(`1, 1±√2` and `0, (3±√5)/2`) are where Pell and Fibonacci enter.

## Scope and honesty

* The argument of §3 of [PROOF.md](PROOF.md) needs `n ≥ 3` (for `n = 1, 2` the
  "column cycle" is degenerate). The cases `n = 1, 2` are settled by direct
  inspection — `K₂`, and `K₄` for both families — and agree with the same
  formulas, so the results hold for every `n ≥ 1`.
* The recurrences hold for `n ≥ 7`, exactly as OEIS states. They fail at `n = 6`,
  which would require a value `a(0)` that is not the combinatorial one.
* The proof is written in ordinary mathematics, not Lean. What CI re-verifies is
  the certificate (below) plus the Lean statements and the closed-form ⟹
  recurrence implications; **the graph-theoretic core is not machine-checked**.
* Unreviewed. Not submitted to OEIS (iron rule 7). **No novelty is claimed.**

## Prior art

A deliberate search was run before and after the proof was written (OEIS entry
text and full revision history, the arXiv full-text API, Google Scholar,
MathWorld, and the papers below).

* **The prism case A286182 is already proved.** A. Vince, *The average size of a
  connected vertex set of a graph — explicit formulas and open problems*,
  J. Graph Theory **97** (2021) 82–103,
  [doi:10.1002/jgt.22643](https://doi.org/10.1002/jgt.22643); free author copy
  [JGTfinal2.pdf](https://people.clas.ufl.edu/avince/files/JGTfinal2.pdf).
  **Lemma 7.2** gives `N(CL_n) = 1 - 3n + 2β(n) + 3n·β̄(n)` with
  `β = A001333 = A002203/2` and `β̄ = A000129`, which is literally Weisstein's
  conjectured closed form. It is quoted as such by J. Haslegrave,
  *The number and average size of connected sets in graphs with degree
  constraints*, [arXiv:2105.13332](https://arxiv.org/abs/2105.13332), §2.
  Vince's proof is a composition/binomial argument, not a transfer matrix.
  **The OEIS entry has simply not been updated**; it cites no reference at all.
  Vince's §6 similarly covers the plain ladder ([A059020](https://oeis.org/A059020)).
* **No proof was found for the Möbius ladder (A286185) or the antiprism
  (A286183).** Vince's paper covers ladders, circular ladders, wheels and
  necklaces, and neither of these two; the arXiv full-text API returns nothing
  for either A-number; the OEIS entries carry no references and no revision ever
  removed the `(conjectured)` tag. A negative search is not proof of novelty,
  and none is claimed.

## Faithfulness to the OEIS entries

The graphs used here are built as `Z_n × {0,1}` with rungs `(i,0)~(i,1)` and
rails between consecutive columns (twisted at one seam for the Möbius ladder,
plus a diagonal for the antiprism); see §0 of [PROOF.md](PROOF.md). Two
independent checks tie that to what OEIS actually tabulates:

1. `certificate.py` also builds each graph **exactly as the OEIS entry's own
   Mathematica `%t` program does** (`CirculantGraph[2n, {1,n}]` for A286185, and
   the explicit edge tables for A286182/A286183) and verifies that the resulting
   counts agree for `n = 1..9`. For the antiprism the two constructions use
   opposite diagonal orientations; the graphs are isomorphic (swap the rows) and
   the check confirms the counts match.
2. Both constructions reproduce every OEIS data term (27–28 terms per entry),
   including the degenerate `n = 1, 2`.

OEIS uses offset 1 for all three entries and so does everything here; no index
shift is involved.

## Reproduction

From this directory. Pure Python standard library, no network access.

```bash
python3 certificate.py
```

36 checks, about 38 s (measured 2026-08-12; the exhaustive-enumeration bound is
set so the command stays well inside CI's 180 s per-command timeout).
`python3 certificate.py --full` raises the exhaustive range from `n ≤ 10` to
`n ≤ 13` and takes a few minutes. `python3 certificate.py --print-edges` dumps
the edge lists.

The Lean side, from the repository root:

```bash
lake build && python3 scripts/check_sorry.py && python3 scripts/check_axioms.py
```

To re-run the graph-definition faithfulness diff between Lean and the
certificate, from the repository root:

```bash
lake env lean problems/oeis-a286185-a286183/lean_graph_check.lean
```

and compare with `python3 problems/oeis-a286185-a286183/certificate.py --print-edges`
(the edge sets agreed exactly for `n = 1..6` and all three graphs on 2026-08-12).

## What is in Lean

[`AgenticConjectures/OeisA286185A286183.lean`](../../AgenticConjectures/OeisA286185A286183.lean)
defines the three graphs and `connectedInducedCount`, states the three
closed-form conjectures as `statementPrism`, `statementMoebius`,
`statementAntiprism`, and proves without `sorry`:

* `aMoebius_linear_recurrence`, `aAntiprism_linear_recurrence`,
  `aPrism_linear_recurrence` — each closed form satisfies the order-6 recurrence
  conjectured on its entry, for every `n`;
* `statementMoebius_imp_linear_recurrence` and its two siblings — hence each
  closed-form conjecture implies the corresponding recurrence conjecture for the
  graph counts;
* `aMoebius_initial_values`, `aAntiprism_initial_values`,
  `aPrism_initial_values` — the closed forms reproduce the first six OEIS terms.

The identity `connectedInducedCount _ n = a n` itself is stated but not proved in
Lean; that is the content of [PROOF.md](PROOF.md).
