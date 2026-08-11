**English** | [한국어](README.ko.md)

# WOWII Graph Conjecture 61

## The original conjecture and partial results

For a finite simple connected graph \(G\), let \(f(G)\) be the number of
vertices of a maximum induced forest, \(r(G)\) the Havel--Hakimi
residue, and \(D(G)\) the diameter. The original conjecture is

\[
f(G)\ge r(G)+\left\lceil\frac{D(G)}3\right\rceil.
\]

In this folder we prove the following four results.

1. In every finite simple connected graph,
   \[
   f(G)\ge\alpha(G)+\left\lceil\frac{D(G)}4\right\rceil.
   \]
2. If there are at least two vertices, then \(f(G)\ge\alpha(G)+1\), and
   if \(f(G)=\alpha(G)+1\), then \(D(G)\le4\).
3. The original conjecture holds in every connected graph with
   \[
   D(G)\in\{0,1,2,3,5,6,9\}.
   \]
4. Every finite tree satisfies the original conjecture regardless of
   diameter.

The detailed proof is in [PROOF.md](PROOF.md). These results do not
close the remaining diameters for general graphs, so they are not a
resolution of the full original conjecture.

## FormalConjectures upstream

The [local upstream snapshot](upstream/README.md) preserves the exact
Lean declaration of the original inequality at a pinned commit. The
declaration is a problem statement with a `sorry`, and the partial
results in this folder do not close that general statement.

## Source status and scope of verification

- The [WOWII Conjecture 61 original
  link](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/) is the
  source cited by FormalConjectures.
- As checked on 2026-08-11, the FormalConjectures main commit
  `9118d083ffca1536f521f9a7d103201f537ea670`'s
  [`GraphConjecture61.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/WrittenOnTheWallII/GraphConjecture61.lean)
  marked the original inequality as `category research open`.
- This folder contains no computational certificate and no completed
  Lean proof. The conclusions rely on the combinatorial arguments of
  [PROOF.md](PROOF.md) and the basic inequality
  \(r(G)\le\alpha(G)\).
