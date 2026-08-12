**English** | [한국어](DETAILS.ko.md)

# Mathematical details of the bounded radius audit

## Finite proposition checked

For every finite simple graph \(G\) with \(1\le|V(G)|\le7\), if both
\(\mathcal C_3(G)\) and \(\mathcal C_4(G)\) are connected, then

\[
  \operatorname{rad}\mathcal C_3(G)
  \ge
  \operatorname{rad}\mathcal C_4(G).
\]

The program checks one representative of every graph-isomorphism class in
this range. Graph isomorphisms induce isomorphisms of recolouring graphs, so
connectedness and radius do not depend on the representative.

## Colour-permutation reduction

The symmetric group on the \(k\) colour names acts on proper \(k\)-colourings.
Applying one global permutation to every state of a recolouring path is an
automorphism of \(\mathcal C_k(G)\). In particular, colourings in the same
orbit have equal eccentricity.

Every orbit has exactly one restricted-growth representative: scan the vertex
colours in vertex-label order, rename the first colour to 0, and thereafter
rename each newly encountered colour to the next unused integer. Therefore,
after connectedness has been checked using an unrestricted BFS, it is enough
to run eccentricity BFS from the restricted-growth states when taking the
minimum that defines the radius. Both implementations use this reduction but
encode states differently.

## Disconnected input graphs

If \(G=G_1\mathbin{\dot\cup}G_2\), restriction to the two components gives a
canonical graph isomorphism

\[
  \mathcal C_k(G)
  \cong
  \mathcal C_k(G_1)\mathbin{\square}\mathcal C_k(G_2),
\]

where \(\square\) is the Cartesian graph product. A recolouring step changes
one vertex, hence exactly one component colouring, which proves the adjacency
correspondence. A Cartesian product is connected exactly when both factors
are connected. In a connected Cartesian product, distances add:

\[
  d((x_1,x_2),(y_1,y_2))=d(x_1,y_1)+d(x_2,y_2).
\]

Consequently eccentricities add, and minimizing independently in the two
coordinates gives

\[
  \operatorname{rad}(H_1\mathbin{\square}H_2)
  =\operatorname{rad}(H_1)+\operatorname{rad}(H_2).
\]

Induction gives the same facts for any finite number of components. The C++
implementation enumerates the full product directly. The Python verifier
uses the component formula through order seven and checks its output against
direct full-product BFS through order six: the \(k=3\) output is checked for
every input graph, and the \(k=4\) output is checked whenever the \(k=3\)
recolouring graph is connected.

## Exhaustiveness and failure conditions

Whenever a program tests \(k=3\) or \(k=4\) for an input graph, it enumerates
every map from the labelled vertex set to the \(k\)-colour palette and retains
exactly the proper ones. From a colouring it generates every proper state
obtained by changing one vertex. Thus the constructed adjacency relation is
exactly that of \(\mathcal C_k(G)\), and ordinary BFS gives exact distances.
Both programs test \(k=3\) first and need not test \(k=4\) when
\(\mathcal C_3(G)\) is disconnected, because such a graph is outside the
hypothesis of the finite proposition.

The certificate fails if the graph6 data have the wrong SHA-256, contain a
duplicate or malformed record, have nonstandard per-order counts, disagree
with the recorded connected-pair totals, make the two implementations
disagree in their shared direct-BFS range, or contain a counterexample. The
fixed data contain the standard \(1,2,4,11,34,156,1044\) unlabelled simple
graphs of orders 1 through 7.

The remaining external trust point is that NetworkX 3.6.1 faithfully packages
the standard Graph Atlas. `generate_atlas_data.py` makes that provenance
reproducible and pins the resulting bytes; the verifier does not treat a
successful finite search as evidence for graphs outside the recorded range.
