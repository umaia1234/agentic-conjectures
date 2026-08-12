**English** | [한국어](DETAILS.ko.md)

# Mathematical details of the recolouring-radius counterexample

## Refuted statement

The final published Question 15 asks whether every finite simple graph \(G\)
and integer \(k\ge3\) for which both \(\mathcal C_k(G)\) and
\(\mathcal C_{k+1}(G)\) are connected must satisfy

\[
  \operatorname{rad}\mathcal C_k(G)
  \ge
  \operatorname{rad}\mathcal C_{k+1}(G).
\]

The certificate refutes this universal statement with \(k=4\).

## Fixed witness

Let \(T\) have vertex set \(\{0,1,2,3,4,5,6\}\) and edge set

\[
  \{03,06,14,16,25,26\}.
\]

It is the subdivided claw: vertex 6 has degree 3, vertices 0, 1, 2 have
degree 2, and vertices 3, 4, 5 have degree 1. The independent graph6 decoder
checks that `FCOf?` is exactly this graph.

Both required recolouring graphs are connected. For each palette, the
certificate runs BFS from one state and checks that it reaches every
enumerated proper colouring: all 2,916 states for \(q=4\) and all 20,480 for
\(q=5\).

## Complete state spaces

A proper \(q\)-colouring of a seven-vertex tree can be chosen by assigning
the first vertex any of \(q\) colours and each subsequent vertex in a rooted
tree any colour except its parent's. Hence

\[
  |V(\mathcal C_q(T))|=q(q-1)^6.
\]

This gives \(4\cdot3^6=2{,}916\) and
\(5\cdot4^6=20{,}480\), matching both implementations. The verifiers do not
rely on this formula: they enumerate all \(q^7\) maps and retain exactly
those that give different colours to both endpoints of every edge.

From each retained state they generate every state obtained by changing one
coordinate to a colour absent from its graph neighbours. Consequently the
materialised adjacency relation is exactly the definition of
\(\mathcal C_q(T)\). The resulting undirected edge counts are 15,876 for
\(q=4\) and 178,560 for \(q=5\); adjacency symmetry is checked explicitly.

## Exact radii

The symmetric group on the \(q\) colour names acts on proper colourings.
Applying one global permutation to every state of a recolouring path is an
automorphism of \(\mathcal C_q(T)\), so states in the same orbit have equal
eccentricity.

Every orbit has one restricted-growth representative: scan the vertex
colours in label order, rename the first colour to 0, and rename each new
colour by the next unused integer. The Python verifier independently
canonicalises every labelled state and confirms that the resulting set is
exactly the set of restricted-growth representatives. It then runs a full,
unpruned BFS from every representative. The complete result is:

| \(q\) | colour-name orbits | labelled eccentricity distribution | radius | diameter |
|---:|---:|---:|---:|---:|
| 4 | 122 | \(192\) at 9; \(2{,}724\) at 10 | 9 | 10 |
| 5 | 187 | \(20{,}480\) at 10 | 10 | 10 |

For the \(q=4\) centre `(0,0,1,1,2,0,3)`, the numbers of states at distances
0 through 9 are

```text
1, 10, 50, 160, 365, 621, 774, 630, 268, 37.
```

They sum to 2,916, so this one BFS gives eccentricity 9 and proves the upper
bound on the radius. The full orbit-source computation proves that no state
has smaller eccentricity. For \(q=5\), every state has eccentricity 10; for
the centre `(0,0,0,1,1,1,1)`, the distance layers are

```text
1, 21, 180, 846, 2436, 4545, 5598, 4464, 2079, 297, 13.
```

These sum to 20,480. Therefore

\[
  \operatorname{rad}\mathcal C_4(T)=9<10
  =\operatorname{rad}\mathcal C_5(T),
\]

which is the required strict reversal.

## Independent implementation audit

The Python implementation represents a colouring as a tuple and its
recolouring graph as adjacency lists indexed by a tuple-to-integer dictionary.
It fully explores all 122 and 187 orbit representatives without a radius
cutoff. It also reconstructs labelled eccentricity counts from orbit sizes
\(q!/(q-r)!\), where \(r\) is the number of colours used by a representative,
and checks that the weights sum to the full state count.

The C++ implementation instead represents a colouring by its base-\(q\)
integer code and maps the entire code space through a dense integer array.
Its BFS storage, neighbour generation, graph6 parser, and radius search are
separate from the Python code. It agrees on connectedness, state and edge
counts, orbit counts, and both exact radii. The certificate fails on any
disagreement or on any mismatch with `counterexample.json`.

## Preserved bounded audit and trust boundary

The earlier atlas certificate remains valid: for \(k=3\) to \(4\), no
counterexample occurs among all unlabelled simple graphs through order seven.
That finite statement is independent of the \(k=4\) witness and remains
registered as a second verification command.

The counterexample certificate's trust boundary is the ordinary C++ compiler,
Python runtime, and the correctness of exhaustive integer BFS. No saved path,
radius transcript, third-party graph library, random choice, or unverified
search result is needed. The computation uses the published conventions for
finite simple graphs, proper labelled colourings, one-vertex moves, ordinary
graph distance, and radius. Using colour names starting at 0 is only a
renaming.
