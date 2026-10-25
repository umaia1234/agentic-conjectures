/* prune189.c: PRUNE hook for nauty's geng (compile geng.c with -DPRUNE=prune189).
   Rejects a graph (intermediate or final) in which some vertex has more than SMAX
   vertices at distance exactly 2. This is sound for exhaustive search: geng's
   intermediate graphs are induced subgraphs of the final graph, and if w is at
   distance 2 from v in an induced subgraph H of G then v,w are non-adjacent with a
   common neighbour in G, so w is at distance 2 from v in G as well. Under the
   hypothesis of WOWII 189, |N_2(v)| <= distEven(v) - 1 <= sigma(G), so every
   hypothesis graph with sigma(G) <= SMAX survives the pruning.
   Second rule: sigma(G) <= SMAX needs two vertices of degree <= SMAX in the final
   graph; degrees only grow along geng's construction path and maxn - n vertices are
   still to come, so a graph with fewer than 2 - (maxn - n) such vertices is pruned.
   SMAX is read from the environment variable SMAX (required). */
#include "gtools.h"
static int smax = -1;
int prune189(graph *g, int n, int maxn) {
  if (smax < 0) {
    char *e = getenv("SMAX");
    if (!e) { fprintf(stderr, "prune189: set SMAX\n"); exit(2); }
    smax = atoi(e);
  }
  int low = 0;
  for (int v = 0; v < n; v++)
    if (POPCOUNT(g[v]) <= smax) low++;
  if (low + (maxn - n) < 2) return 1;
  for (int v = 0; v < n; v++) {
    setword nb = g[v], w = nb, n2 = 0;
    while (w) {
      int u = FIRSTBITNZ(w);
      w ^= bit[u];
      n2 |= g[u];
    }
    n2 &= ~nb & ~bit[v];
    if (POPCOUNT(n2) > smax) return 1;
  }
  return 0;
}
