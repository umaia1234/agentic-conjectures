# Exact computation of L(6) for Pulse Graphs

This directory contains an unreviewed, exact computer-assisted answer to an
open finite case in Pakin Methawisal, *Pulse Graphs: Prime-Activated Boolean
Dynamics on Directed Graphs*, arXiv:2607.10453v2 (2026-08-01):

> **Result.** `L(6) = 17`.

The paper defines `L(n)` as the maximum attractor period over loopless directed
graphs on `n` vertices. It determines `L(1),...,L(5) = 1,1,1,3,9`; its
conclusion explicitly lists “determining the exact values of L(n) for n >= 6”
as an open problem.

Primary source: <https://arxiv.org/abs/2607.10453v2>

## Transition rule

For a state `x` and vertex `v`, let `k(v)` be the number of active
in-neighbors of `v`. The synchronous next state has `v` active exactly when
`k(v)` is prime. On six loopless vertices, the possible activating counts are
therefore `2`, `3`, and `5`. In the programs, state bit `i` is the state of
vertex `i`, with vertex 0 stored in the least-significant bit.

## Why the enumeration proves the upper bound

Every loopless digraph has a unique underlying simple graph up to
isomorphism: retain the unordered pair `{u,v}` when at least one of `u->v` and
`v->u` is present. `geng` generates every underlying unlabeled simple graph,
and `directg` replaces each retained pair by one of `u->v`, `v->u`, or both,
while suppressing isomorphic outputs. Different underlying graph isomorphism
classes cannot produce isomorphic digraphs. Thus the pipeline generates every
unlabeled loopless digraph exactly once. Relabeling preserves attractor period,
so unlabeled enumeration is sufficient.

More explicitly, a digraph isomorphism \(\varphi:G\to H\) induces the state
bijection \((\Phi_\varphi(x))_{\varphi(v)}=x_v\). It preserves every active
in-neighbor count, and hence

\[
\Phi_\varphi\circ F_G=F_H\circ\Phi_\varphi.
\]

The two transition maps are conjugate, so all their cycle lengths agree.

For `n=6`, the pipeline reads 156 underlying simple graphs and emits exactly
1,540,944 nonisomorphic loopless digraphs. For every one, `pulse_analyze.cpp`
constructs its exact map on all 64 Boolean states and enumerates every directed
cycle in that functional graph. The largest period encountered is 17; exactly
two unlabeled digraphs attain it. This proves `L(6) <= 17` conditional only on
the standard nauty generation guarantee and the small checker.

`pulse_analyze_kahn.cpp` repeats the full upper-bound computation using an
independent cycle algorithm: it removes every functional-graph state of
in-degree zero (and all states exposed recursively), then counts the cycles in
the unremoved subgraph. It independently returns the same graph count,
maximum, and number of maximizing isomorphism classes.

`witness.json` gives a 21-arc graph and an explicit 17-cycle, while
`verify_witness.py` independently parses that ordered arc list, recomputes the
Pulse transition from the definition, checks every transition in the cycle,
and enumerates all cycles of that witness. This proves `L(6) >= 17` without
using the exhaustive C++ analyzer.

The cycle enumeration is exhaustive because a finite functional graph has
exactly one directed cycle in each weak component. Following the unique
out-edge from any state must eventually repeat a state; two states joined by
an edge have forward orbits reaching the same cycle, and this propagates
along every undirected path in the component. The primary analyzer records
the first occurrence of each state along each forward path. The Kahn-style
analyzer instead repeatedly removes in-degree-zero states: cycle states
survive, while every noncycle state is eventually peeled from an in-tree.
These are independent implementations of the two characterizations.

## Explicit lower-bound witness

With vertices \(0,\ldots,5\), the witness has the following 21 arcs:

\[
\begin{aligned}
E=\{&
(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(0,5),(5,0),\\
&(1,3),(3,1),(1,4),(5,1),(2,3),(3,2),(4,2),(2,5),\\
&(3,4),(4,3),(3,5),(5,3),(5,4)
\}.
\end{aligned}
\]

Its in-neighbor sets are

\[
\begin{aligned}
N^-(0)&=\{2,3,4,5\},&N^-(1)&=\{3,5\},\\
N^-(2)&=\{0,3,4\},&N^-(3)&=\{0,1,2,4,5\},\\
N^-(4)&=\{0,1,3,5\},&N^-(5)&=\{0,2,3\}.
\end{aligned}
\]

Encode a state \(x\) by \(s(x)=\sum_{v=0}^5x_v2^v\). In the table,
the six-bit display is \(x_5x_4\cdots x_0\), and
\(\mathbf k_x=(k_x(0),\ldots,k_x(5))\). Components equal to 2, 3, or 5
are precisely the active bits in the next state.

| state | bits | \(\mathbf k_x\) | next |
|---:|:---:|:---|---:|
| 24 | 011000 | \((2,1,2,1,1,1)\) | 5 |
| 5 | 000101 | \((1,0,1,2,1,2)\) | 40 |
| 40 | 101000 | \((2,2,1,1,2,1)\) | 19 |
| 19 | 010011 | \((1,0,2,3,2,1)\) | 28 |
| 28 | 011100 | \((3,1,2,2,1,2)\) | 45 |
| 45 | 101101 | \((3,2,2,3,3,3)\) | 63 |
| 63 | 111111 | \((4,2,3,5,4,3)\) | 46 |
| 46 | 101110 | \((3,2,1,3,3,2)\) | 59 |
| 59 | 111011 | \((3,2,3,4,4,2)\) | 39 |
| 39 | 100111 | \((2,1,1,4,3,2)\) | 49 |
| 49 | 110001 | \((2,1,2,3,2,1)\) | 29 |
| 29 | 011101 | \((3,1,3,3,2,3)\) | 61 |
| 61 | 111101 | \((4,2,3,4,3,3)\) | 54 |
| 54 | 110110 | \((3,1,1,4,2,1)\) | 17 |
| 17 | 010001 | \((1,0,2,2,1,1)\) | 12 |
| 12 | 001100 | \((2,1,1,1,1,2)\) | 33 |
| 33 | 100001 | \((1,1,1,2,2,1)\) | 24 |

The 17 states are distinct and the last transition returns to the first, so
the table proves \(L(6)\geq17\) directly from the transition rule. The
independent Python verifier also enumerates all cycles in this witness and
finds lengths \(1,1,2,17\).

## Reproduction

Requirements: a C++17 compiler, Python 3, and nauty's `geng` and `directg`
(on Debian/Ubuntu these may be named `nauty-geng` and `nauty-directg`). The
recorded 2026-08-11 final run used nauty 2.8.8. Run:

```sh
bash reproduce.sh
```

The regression values for `n=1,...,6` are:

```text
graphs=1       max_period=1
graphs=3       max_period=1
graphs=16      max_period=1
graphs=218     max_period=3
graphs=9608    max_period=9
graphs=1540944 max_period=17 attaining_unlabeled=2
```

The first five maximum periods exactly reproduce the paper. The `n=6` output
also prints the complete ordered arc list and the 17-cycle stored in
`witness.json`.

The core exhaustive command is:

```sh
geng -q 6 | directg -q -T | ./pulse_analyze 6
```

If your distribution prefixes nauty executables, replace the first two tools
with `nauty-geng` and `nauty-directg`.

For the lower bound alone, with no nauty dependency:

```sh
python3 problems/pulse-graphs-l6/verify_witness.py
```

To verify the checked-in artifacts:

```sh
cd problems/pulse-graphs-l6
sha256sum -c SHA256SUMS
```

The final run passed all six hashes and both upper-bound algorithms. This
result was developed separately from pre-existing work elsewhere in this
workspace. Targeted public searches through 2026-08-11 found no earlier posted
answer, but that is not a literature review or a priority claim. The exact
finite computation remains an unreviewed computer-assisted result and relies
on nauty's standard isomorph-free generation guarantee.
