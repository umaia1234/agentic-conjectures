/* For every graph6 line on stdin (regular graphs, n <= 62): compute i(G) exactly, and decide
   whether mu*(G) < i(G) (a counterexample to i <= mu*).  mu* is computed exactly whenever
   i(G) >= ceil(m/(2r-1)); otherwise i < lower bound <= mu* and no search is needed.
   Prints every counterexample and a SUMMARY line (statistics also go to stderr); with -v it
   prints "i mu* graph6" for every graph instead of the counterexample lines.
   C99 plus the GCC/Clang builtins __builtin_popcountll and __builtin_ctzll. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint64_t set;
static int n, r, m;
static set adj[64], cl[64];       /* open and closed neighbourhoods */
static int best;

static int pc(set x) { return __builtin_popcountll(x); }

static void ids(set avail, int size) {
    /* avail = undominated vertices = vertices still allowed in the set */
    if (!avail) { if (size < best) best = size; return; }
    if (size + (pc(avail) + r) / (r + 1) >= best) return;
    int bv = -1, bc = 99;
    for (set a = avail; a; a &= a - 1) {
        int v = __builtin_ctzll(a), c = pc(cl[v] & avail);
        if (c < bc) { bc = c; bv = v; if (c <= 1) break; }
    }
    for (set c = cl[bv] & avail; c; c &= c - 1) {
        int u = __builtin_ctzll(c);
        ids(avail & ~cl[u], size + 1);
    }
}

/* is there a maximal matching with at most k edges extending the current partial state?
   mt = matched vertices, fb = vertices that must stay unmatched, cnt = edges used */
static long nodes;
static int mm(set mt, set fb, int cnt, int k) {
    nodes++;
    set un = ((n == 64) ? ~0ULL : ((1ULL << n) - 1)) & ~mt;
    int unc = 0, bu = -1, bv = -1, bw = 99;
    for (set a = un; a; a &= a - 1) {
        int u = __builtin_ctzll(a);
        set nb = adj[u] & un;
        unc += pc(nb);
        if (nb) {
            /* choose uncovered edge whose endpoints have few options */
            int opts = pc(nb & ~fb);
            if (!(fb >> u & 1) && opts < bw) {
                bw = opts; bu = u; bv = __builtin_ctzll(nb);
            } else if (bu < 0) { bu = u; bv = __builtin_ctzll(nb); }
        }
    }
    unc /= 2;
    if (unc == 0) return cnt <= k;
    if (cnt + (unc + 2 * r - 2) / (2 * r - 1) > k) return 0;
    /* uncovered edge (bu,bv): match bu, or forbid bu and match bv */
    int u = bu, v = bv;
    if (fb >> u & 1) { int t = u; u = v; v = t; }
    if (fb >> u & 1) return 0;            /* both endpoints forbidden: uncoverable */
    for (set c = adj[u] & un & ~fb; c; c &= c - 1) {
        int w = __builtin_ctzll(c);
        if (mm(mt | (1ULL << u) | (1ULL << w), fb, cnt + 1, k)) return 1;
    }
    if (fb >> v & 1) return 0;
    fb |= 1ULL << u;
    for (set c = adj[v] & un & ~fb; c; c &= c - 1) {
        int w = __builtin_ctzll(c);
        if (mm(mt | (1ULL << v) | (1ULL << w), fb, cnt + 1, k)) return 1;
    }
    return 0;
}

static int parse(const char *s) {
    if (*s == '>') return 0;
    n = s[0] - 63;
    if (n < 1 || n > 62) return 0;
    memset(adj, 0, sizeof adj);
    int k = 0, len = (int)strlen(s);
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++, k++) {
            int byte = 1 + k / 6, bit = 5 - k % 6;
            if (byte >= len) return 0;
            if (((s[byte] - 63) >> bit) & 1) { adj[i] |= 1ULL << j; adj[j] |= 1ULL << i; }
        }
    m = 0; r = pc(adj[0]);
    for (int v = 0; v < n; v++) {
        if (pc(adj[v]) != r) { fprintf(stderr, "not regular: %s\n", s); exit(2); }
        m += pc(adj[v]); cl[v] = adj[v] | (1ULL << v);
    }
    m /= 2;
    return 1;
}

int main(int argc, char **argv) {
    int verbose = argc > 1 && !strcmp(argv[1], "-v");
    char line[4096];
    long total = 0, needmu = 0, tight = 0, viol = 0;
    long hist[64] = {0};   /* histogram of mu* - i (only computed when i >= LB) */
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\r\n")] = 0;
        if (!parse(line)) continue;
        total++;
        best = n + 1; ids((n == 64) ? ~0ULL : ((1ULL << n) - 1), 0);
        int i = best, lb = (m + 2 * r - 2) / (2 * r - 1);
        if (verbose) {
            int k = lb; while (!mm(0, 0, 0, k)) k++;
            printf("%d %d %s\n", i, k, line);
            continue;
        }
        if (i < lb) continue;
        needmu++;
        /* exact mu*: smallest k >= lb with a maximal matching of size <= k */
        int k = lb;
        while (!mm(0, 0, 0, k)) k++;
        if (k < i) { viol++; printf("COUNTEREXAMPLE i=%d mu*=%d %s\n", i, k, line); fflush(stdout); }
        else { hist[k - i]++; if (k == i) tight++; }
    }
    fprintf(stderr, "graphs %ld  i>=LB(needed mu*) %ld  tight(i=mu*) %ld  counterexamples %ld  mm-nodes %ld\n",
            total, needmu, tight, viol, nodes);
    fprintf(stderr, "hist mu*-i (among i>=LB):");
    for (int d = 0; d < 64; d++) if (hist[d]) fprintf(stderr, " %d:%ld", d, hist[d]);
    fprintf(stderr, "\n");
    printf("SUMMARY graphs=%ld needmu=%ld tight=%ld counterexamples=%ld\n", total, needmu, tight, viol);
    return 0;
}
