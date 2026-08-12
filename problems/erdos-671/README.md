**English** | [한국어](README.ko.md)

# Erdős #671 — everywhere-unbounded Lagrange arrays

The canonical [Erdős Problem #671](https://www.erdosproblems.com/671) asks
two existence questions about triangular arrays of Lagrange interpolation
nodes. On 2026-08-12 the page still labelled the problem **OPEN** with a
**$250 prize**. A complete solution and formalization had, however, already
been posted publicly on its discussion thread on 2026-06-22. This directory
independently rebuilds and preserves that solution; it claims no novelty or
prize, and nothing has been submitted externally.

## Canonical statement

For every row size \(n\geq 1\), choose distinct nodes
\(a_1^n,\ldots,a_n^n\in[-1,1]\). Let \(p_i^n\) be the fundamental Lagrange
polynomial for the node \(a_i^n\), let

\[
  \mathcal L^n f(x)=\sum_{i=1}^n f(a_i^n)p_i^n(x),
  \qquad
  \Lambda_n(x)=\sum_{i=1}^n |p_i^n(x)|.
\]

The page asks:

> Is there such a sequence of \(a_i^n\) such that for every continuous
> \(f:[-1,1]\to\mathbb R\) there exists some \(x\in[-1,1]\) where
> \(\limsup_{n\to\infty}\Lambda_n(x)=\infty\) and yet
> \(\mathcal L^n f(x)\to f(x)\)?

It then asks the stronger question where
\(\limsup_n\Lambda_n(x)=\infty\) must hold **for every**
\(x\in[-1,1]\), while each continuous \(f\) must still have at least one
point of convergence.

## Result

Both questions have affirmative answers. The theorem
[`erdos_671`](../../AgenticConjectures/Erdos671.lean) constructs one array
with exactly \(n\) distinct nodes in row \(n\) such that:

- for every \(x\in[-1,1]\), every real threshold \(A\), and every row bound
  \(N\), some \(n\geq N\) has \(\Lambda_n(x)\geq A\); and
- for every continuous \(f\), there is an \(x_f\in[-1,1]\) such that the
  full sequence \(\mathcal L^n f(x_f)\) converges to \(f(x_f)\).

The first condition is the cofinal form of
\(\limsup_n\Lambda_n(x)=\infty\), so the theorem proves the stronger second
question literally. The first question follows immediately by taking the
point \(x_f\) supplied for each \(f\).

## Statement faithfulness

The Lean type `Row (n + 1)` represents the canonical one-based row of size
\(n+1\); `nodeSet` and `card_nodeSet` enforce exact cardinality and the
`Embedding` field makes the nodes distinct. `Interval` is exactly the closed
real interval `Set.Icc (-1) 1`. `fundamental`, `interpolant`, and `lebesgue`
are the standard product-form Lagrange basis, interpolant, and Lebesgue
function.

The theorem states unboundedness as
`∀ A N, ∃ n ≥ N, A ≤ lebesgue ...`, which is equivalent to the page's
infinite `limsup` for the nonnegative real sequence but avoids extended-real
bookkeeping. Convergence is `Tendsto ... atTop`, exactly convergence of the
entire sequence, not merely a subsequence. There are no endpoint,
subtraction, or row-cardinality relaxations.

See [DETAILS.md](DETAILS.md) for the construction and proof architecture.

## Machine verification

The Lean source is 2,800+ lines and contains no `sorry`, added axiom, or
`native_decide`. From the repository root:

```bash
python3 scripts/check_imports.py
python3 scripts/check_sorry.py
lake build
python3 scripts/check_axioms.py
(cd problems/erdos-671/upstream && sha256sum -c SHA256SUMS)
```

The axiom audit reports only Lean's three permitted standard axioms:
`propext`, `Classical.choice`, and `Quot.sound`. The full repository gates
also run the existing certificates and documentation checks.

## Provenance and prior art

The [public discussion post](https://www.erdosproblems.com/forum/thread/671#post-7142)
attributes the proof argument to “GPT Pro” and links a “Lean formalisation by
Codex”; it does not disclose exact model or harness names. We therefore
record those labels literally and do not invent more specific attribution.
The local `GPT-5.6 Sol` attribution is restricted to independent compilation,
statement comparison, repository integration, and documentation.

The exact public Lean payload is preserved with its SHA-256 and retrieval
instructions in [upstream/README.md](upstream/README.md). The checked module
changes only the namespace and packaging needed by this repository, plus
provenance and faithfulness documentation; the proof body is unchanged.

Earlier literature on the canonical page includes Bernstein's theorem that
every node array has at least one point with unbounded Lebesgue functions,
and Erdős–Vértesi's almost-everywhere divergence result for a suitable
continuous function. A February 2026 paper by Zeraoulia and Cáceres gives a
Baire-category obstruction, not the construction proved here. No external
review of this repository's claim is asserted.
