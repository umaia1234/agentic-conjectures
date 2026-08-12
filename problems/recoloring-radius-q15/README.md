**English** | [한국어](README.ko.md)

# Graph-colouring reconfiguration radius: a counterexample to Question 15

Cambie–Cames van Batenburg–Cranston Question 15 is false. The subdivided
claw on seven vertices gives a counterexample for the comparison \(k=4\) to
\(k+1=5\).

## Result

Let \(T\) be the tree obtained by subdividing every edge of \(K_{1,3}\) once.
With vertices \(0,\ldots,6\), use

```text
E(T) = {03, 06, 14, 16, 25, 26}.
```

Thus vertex 6 is the centre, vertices 0, 1, 2 are the degree-two subdivision
vertices, and vertices 3, 4, 5 are the leaves. Its graph6 encoding is
`FCOf?`. Exact calculations give:

| recolouring graph | proper colourings | recolouring edges | connected | radius | diameter |
|---|---:|---:|:---:|---:|---:|
| \(\mathcal C_4(T)\) | 2,916 | 15,876 | yes | 9 | 10 |
| \(\mathcal C_5(T)\) | 20,480 | 178,560 | yes | 10 | 10 |

In particular,

\[
  \operatorname{rad}\mathcal C_4(T)=9
  <10=\operatorname{rad}\mathcal C_5(T).
\]

Here \(4\ge3\), and both recolouring graphs satisfy the connectedness
hypothesis. One such graph is enough to refute the universal statement.

## Source and statement

For a graph \(G\), the vertices of its \(k\)-recolouring graph
\(\mathcal C_k(G)\) are the proper \(k\)-colourings of \(G\). Two colourings
are adjacent exactly when they differ at one vertex. The published question
asks, for \(k\ge3\) when both consecutive recolouring graphs are connected:

> “Is it necessarily true that
> \(\operatorname{rad}\mathcal C_k(G)\ge
> \operatorname{rad}\mathcal C_{k+1}(G)\)?”

Primary source: Stijn Cambie, Wouter Cames van Batenburg, and Daniel W.
Cranston, “Sharp Bounds on Lengths of Linear Recolouring Sequences,”
*Electronic Journal of Combinatorics* 33(1) (2026), #P1.18,
[doi:10.37236/13788](https://doi.org/10.37236/13788), Question 15.

## Machine certificate

[`counterexample.json`](counterexample.json) fixes the graph and every claimed
integer. Two independent implementations reconstruct the complete
recolouring graphs rather than trusting a saved search transcript.

1. [`recolor_radius_exact.cpp`](recolor_radius_exact.cpp) encodes colourings as
   base-\(k\) integers, materialises every legal one-vertex move, checks
   connectedness, and computes the exact radius by integer BFS.
2. [`verify_counterexample.py`](verify_counterexample.py) uses a separate
   graph6 decoder, tuple-valued colourings, and standard-library deque BFS. It
   invokes the C++ program only after completing its own calculation and then
   compares the results.

Global permutations of the colour names act by automorphisms of each
recolouring graph. Both implementations therefore take one restricted-growth
representative from every colour-name orbit as a BFS source. The Python
certificate audits this orbit decomposition against all labelled states and
runs a complete, unpruned BFS from all 122 representatives for \(k=4\) and
all 187 representatives for \(k=5\).

As internal checks, the state counts also equal the tree formula
\(k(k-1)^6\). For \(k=4\), exactly 192 labelled states have eccentricity 9 and
the remaining 2,724 have eccentricity 10. For \(k=5\), all 20,480 states have
eccentricity 10. These distributions independently force the two stated
radii.

The detailed derivation and certificate invariants are recorded in
[`DETAILS.md`](DETAILS.md).

## Reproduction

From the repository root, run:

```bash
g++ -O3 -std=c++17 \
  problems/recoloring-radius-q15/recolor_radius_exact.cpp \
  -o /tmp/recolor_radius_exact
python3 problems/recoloring-radius-q15/verify_counterexample.py \
  --cpp /tmp/recolor_radius_exact
```

Expected output is:

```text
PASS graph6 FCOf? decodes as the 7-vertex subdivided claw
PASS independent Python exhaustive BFS: C_4 connected, 2916 states, 15876 edges, radius 9, diameter 10
PASS independent Python exhaustive BFS: C_5 connected, 20480 states, 178560 edges, radius 10, diameter 10
PASS independent C++ exact-radius results agree
PASS counterexample: 9 < 10 (...s)
```

The recorded local run took 1.87 seconds and used about 23 MB of peak resident
memory. The verifier uses only a C++17 compiler and the Python standard
library.

## Preserved earlier search result

The fixed [`atlas_1_7.g6`](atlas_1_7.g6) dataset and its two verifiers remain
as a separate bounded result. They check all 1,252 isomorphism classes of
simple graphs on one through seven vertices for the \(k=3\) to \(k=4\)
comparison. Exactly 145 have both recolouring graphs connected, and none is a
counterexample. The dataset has SHA-256
`ad68465d32eb7679a1ed8b0aa7a7f1da366da9b1ef8566b04664c504e8876255`.
This does not conflict with the counterexample, which uses \(k=4\).

To rerun that audit with the same compiled binary:

```bash
python3 problems/recoloring-radius-q15/verify_atlas.py \
  --cpp /tmp/recolor_radius_exact
```

## Faithfulness and scope

The certificate uses finite undirected simple graphs, labelled proper
colourings with palettes \(\{0,\ldots,k-1\}\), one-vertex recolouring moves,
ordinary graph distance, and minimum eccentricity as radius. These are the
published definitions. Zero-based rather than one-based colour names have no
mathematical effect. The final published paper numbers the statement as
Question 15; earlier manuscript versions used different numbering.

This repository records a machine-verified counterexample. It makes no claim
of publication priority or novelty before external review.
