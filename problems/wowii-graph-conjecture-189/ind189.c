/*
 * ind189.c -- independent checker for WOWII Conjecture 189.
 *
 * For a finite simple graph G on n vertices:
 *   distEven(v) = #{ w : dist(v,w) is even }   (v itself counts, dist(v,v) = 0)
 *   sigma(G)    = second entry of the degree sequence sorted nondecreasingly
 *   hyp(G)      = n >= 2, G connected, max_v distEven(v) <= 1 + sigma(G)
 * For every hyp graph we decide exactly whether G has a Hamiltonian path.
 *
 * Input: graph6 lines on stdin, n <= 32. Empty lines and a ">>graph6<<"
 * header are ignored. A malformed line aborts the run with exit status 2.
 * (The null graph, n = 0, is accepted and counted as not connected.)
 *
 * Default output: "NT <g6> n=<n> sigma=<s>" on stdout for every hyp graph
 * without a Hamiltonian path. At EOF, on stderr:
 *   total=<graphs read> connected=<..> hyp=<..> nontraceable=<..>
 *   sigma=<s> hyp=<count>     (hyp graphs by sigma; nonzero counts only)
 *   n=<k> hyp=<count>         (hyp graphs by order; nonzero counts only)
 *
 * Options:
 *   -d    instead of NT lines, print one line per input graph:
 *         <g6> <connected 0/1> <sigma|-> <maxDistEven|-> <hyp 0/1> <traceable 0/1|->
 *         (sigma/maxDistEven only for connected graphs with n >= 2,
 *          traceable only for hyp graphs). The stderr summary is still printed.
 *   -dp   decide Hamiltonian paths with the subset DP only (n <= 25)
 *         instead of the backtracking search.
 *
 * Distances: one plain BFS per source vertex, explicit queue, adjacency lists.
 *
 * Build: cc -O3 -march=native -o ind189 ind189.c
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 32    /* largest supported order */
#define DP_MAXN 25 /* largest order for the subset DP (table of 2^n uint32) */

typedef struct {
    int n;
    int deg[MAXN];
    int nbr[MAXN][MAXN]; /* adjacency lists, used by the distance BFS */
    uint32_t adj[MAXN];  /* adjacency rows as bit sets, used by the path deciders */
} graph;

static uint32_t bit(int v) { return (uint32_t)1 << v; }

/* Decode the graph6 string s[0..len-1] into g.
   Returns 0 on success, -1 if s is malformed or n > MAXN. */
static int parse_g6(const char *s, size_t len, graph *g)
{
    const unsigned char *p = (const unsigned char *)s;
    if (len == 0 || p[0] < 63 || p[0] > 125) return -1; /* 126 = multi-byte n >= 63 */
    int n = p[0] - 63;
    if (n > MAXN) return -1;
    int nbits = n * (n - 1) / 2;
    if (len != 1 + (size_t)(nbits + 5) / 6) return -1;
    for (size_t i = 1; i < len; i++)
        if (p[i] < 63 || p[i] > 126) return -1;

    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->adj[v] = 0;
    }
    /* Upper triangle column by column: x(0,1), x(0,2), x(1,2), x(0,3), ...
       six bits per byte, most significant first; trailing pad bits ignored. */
    const unsigned char *q = p + 1;
    int k = 6, x = 0;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++) {
            if (k == 6) {
                x = *q++ - 63;
                k = 0;
            }
            if (x & (32 >> k)) {
                g->nbr[i][g->deg[i]++] = j;
                g->nbr[j][g->deg[j]++] = i;
                g->adj[i] |= bit(j);
                g->adj[j] |= bit(i);
            }
            k++;
        }
    return 0;
}

/* Breadth-first search from s (explicit FIFO queue over adjacency lists).
   Returns the number of vertices at even distance from s, s included, and
   stores the number of vertices reached in *reached. */
static int bfs_even(const graph *g, int s, int *reached)
{
    int dist[MAXN], queue[MAXN];
    int head = 0, tail = 0, even = 0;
    for (int v = 0; v < g->n; v++) dist[v] = -1;
    dist[s] = 0;
    queue[tail++] = s;
    while (head < tail) {
        int v = queue[head++];
        if (dist[v] % 2 == 0) even++;
        for (int k = 0; k < g->deg[v]; k++) {
            int w = g->nbr[v][k];
            if (dist[w] < 0) {
                dist[w] = dist[v] + 1;
                queue[tail++] = w;
            }
        }
    }
    *reached = tail;
    return even;
}

/* Backtracking: the path built so far ends at `end`; U = vertices not yet on
   it. Returns 1 iff the path extends through all of U, i.e. iff G[U+{end}] has
   a Hamiltonian path end -> w1 -> ... -> wk with {w1..wk} = U. Every move is
   tried; a branch is cut only on a necessary condition of such a path:
     - each w in U needs a predecessor in U+{end}; each w in U except the last
       one wk also needs a successor, so it has >= 2 neighbours in U+{end}:
       no w may have 0 such neighbours and at most one w may have exactly 1;
     - G[U+{end}] must be connected. */
static int ham_extend(const uint32_t *adj, int end, uint32_t U)
{
    if (U == 0) return 1;
    uint32_t live = U | bit(end);
    int ones = 0;
    for (uint32_t t = U; t; t &= t - 1) {
        int a = __builtin_popcount(adj[__builtin_ctz(t)] & live);
        if (a == 0) return 0;
        if (a == 1 && ++ones > 1) return 0;
    }
    uint32_t seen = bit(end), frontier = seen;
    while (frontier) {
        uint32_t next = 0;
        for (uint32_t t = frontier; t; t &= t - 1) next |= adj[__builtin_ctz(t)];
        next &= live & ~seen;
        seen |= next;
        frontier = next;
    }
    if (seen != live) return 0;
    for (uint32_t t = adj[end] & U; t; t &= t - 1) {
        int x = __builtin_ctz(t);
        if (ham_extend(adj, x, U & ~bit(x))) return 1;
    }
    return 0;
}

/* Exact Hamiltonian path test by backtracking from every possible start.
   A vertex of degree 1 must be an endpoint of any Hamiltonian path (n >= 2),
   so if one exists it is the only start tried; more than two of them, or a
   vertex of degree 0, rule a Hamiltonian path out. */
static int ham_dfs(const graph *g)
{
    int n = g->n;
    if (n <= 1) return n == 1;
    uint32_t all = (n == 32) ? 0xFFFFFFFFu : bit(n) - 1;
    int leaves = 0, leaf = -1;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] == 0) return 0;
        if (g->deg[v] == 1 && leaves++ == 0) leaf = v;
    }
    if (leaves > 2) return 0;
    if (leaf >= 0) return ham_extend(g->adj, leaf, all & ~bit(leaf));
    for (int s = 0; s < n; s++)
        if (ham_extend(g->adj, s, all & ~bit(s))) return 1;
    return 0;
}

/* Held-Karp style subset DP, no pruning: ends[S] = set of vertices u in S such
   that some path with vertex set exactly S ends at u. ends[{u}] = {u}; for
   |S| >= 2, u is in ends[S] iff ends[S - u] contains a neighbour of u. */
static uint32_t *dp_ends;
static int dp_cap = -1;

static int ham_dp(const graph *g)
{
    int n = g->n;
    if (n == 0) return 0;
    if (n > DP_MAXN) {
        fprintf(stderr, "ind189: -dp supports n <= %d (got n=%d)\n", DP_MAXN, n);
        exit(2);
    }
    if (n > dp_cap) {
        free(dp_ends);
        dp_ends = malloc(sizeof *dp_ends << n);
        if (!dp_ends) {
            fprintf(stderr, "ind189: out of memory\n");
            exit(2);
        }
        dp_cap = n;
    }
    uint32_t N = bit(n);
    dp_ends[0] = 0;
    for (uint32_t S = 1; S < N; S++) {
        if ((S & (S - 1)) == 0) {
            dp_ends[S] = S;
            continue;
        }
        uint32_t e = 0;
        for (uint32_t t = S; t; t &= t - 1) {
            int u = __builtin_ctz(t);
            if (dp_ends[S & ~bit(u)] & g->adj[u]) e |= bit(u);
        }
        dp_ends[S] = e;
    }
    return dp_ends[N - 1] != 0;
}

typedef struct {
    int connected; /* 0/1 */
    int sigma;     /* -1 unless connected and n >= 2 */
    int maxde;     /* max_v distEven(v); -1 unless computed in full mode */
    int hyp;       /* 0/1 */
    int trace;     /* 0/1; -1 unless hyp */
} result;

/* With full = 0 the distance loop stops at the first vertex that violates the
   hypothesis (maxde is then not reported); full = 1 computes every BFS. */
static void analyze(const graph *g, int full, int use_dp, result *r)
{
    int n = g->n, reached;
    r->connected = 0;
    r->sigma = -1;
    r->maxde = -1;
    r->hyp = 0;
    r->trace = -1;
    if (n == 0) return;
    int e = bfs_even(g, 0, &reached);
    r->connected = (reached == n);
    if (!r->connected || n < 2) return;

    int d1 = MAXN, d2 = MAXN; /* smallest and second smallest degree */
    for (int v = 0; v < n; v++) {
        int d = g->deg[v];
        if (d < d1) {
            d2 = d1;
            d1 = d;
        } else if (d < d2) {
            d2 = d;
        }
    }
    r->sigma = d2;

    int maxde = e, ok = (e <= 1 + d2);
    for (int v = 1; v < n && (ok || full); v++) {
        e = bfs_even(g, v, &reached);
        if (e > maxde) maxde = e;
        if (e > 1 + d2) ok = 0;
    }
    if (full) r->maxde = maxde;
    r->hyp = ok;
    if (ok) r->trace = use_dp ? ham_dp(g) : ham_dfs(g);
}

#ifndef IND189_NO_MAIN
static int opt_detail, opt_dp;
static long long lineno, cnt_total, cnt_conn, cnt_hyp, cnt_nt;
static long long hist_sigma[MAXN + 1], hist_n[MAXN + 1];

static void handle_line(char *s, size_t len)
{
    while (len > 0 && (s[len - 1] == '\r' || s[len - 1] == ' ' || s[len - 1] == '\t')) len--;
    if (len >= 10 && memcmp(s, ">>graph6<<", 10) == 0) {
        s += 10;
        len -= 10;
    }
    if (len == 0) return;
    s[len] = '\0';

    graph g;
    result r;
    if (parse_g6(s, len, &g) != 0) {
        fprintf(stderr, "ind189: line %lld: not a graph6 string with n <= %d: %s\n", lineno, MAXN, s);
        exit(2);
    }
    analyze(&g, opt_detail, opt_dp, &r);
    cnt_total++;
    cnt_conn += r.connected;
    if (r.hyp) {
        cnt_hyp++;
        hist_sigma[r.sigma]++;
        hist_n[g.n]++;
        if (!r.trace) cnt_nt++;
    }
    if (opt_detail) {
        char sg[16] = "-", md[16] = "-";
        if (r.sigma >= 0) snprintf(sg, sizeof sg, "%d", r.sigma);
        if (r.maxde >= 0) snprintf(md, sizeof md, "%d", r.maxde);
        printf("%s %d %s %s %d %s\n", s, r.connected, sg, md, r.hyp,
               r.trace < 0 ? "-" : (r.trace ? "1" : "0"));
    } else if (r.hyp && !r.trace) {
        printf("NT %s n=%d sigma=%d\n", s, g.n, r.sigma);
    }
}

#define IBUF (1 << 20)
static char ibuf[IBUF + 1]; /* +1: room for the terminator of an unterminated last line */
static char obuf[1 << 20];

int main(int argc, char **argv)
{
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-d") == 0)
            opt_detail = 1;
        else if (strcmp(argv[i], "-dp") == 0)
            opt_dp = 1;
        else {
            fprintf(stderr, "usage: %s [-d] [-dp] < graphs.g6\n", argv[0]);
            return 2;
        }
    }
    setvbuf(stdout, obuf, _IOFBF, sizeof obuf);

    size_t have = 0, pos = 0;
    int eof = 0;
    for (;;) {
        char *nl = memchr(ibuf + pos, '\n', have - pos);
        if (nl) {
            lineno++;
            handle_line(ibuf + pos, (size_t)(nl - (ibuf + pos)));
            pos = (size_t)(nl - ibuf) + 1;
            continue;
        }
        if (eof) {
            if (pos < have) {
                lineno++;
                handle_line(ibuf + pos, have - pos);
            }
            break;
        }
        memmove(ibuf, ibuf + pos, have - pos);
        have -= pos;
        pos = 0;
        if (have == IBUF) {
            fprintf(stderr, "ind189: line %lld too long\n", lineno + 1);
            return 2;
        }
        size_t got = fread(ibuf + have, 1, IBUF - have, stdin);
        if (got == 0) {
            if (ferror(stdin)) {
                perror("ind189: read error");
                return 2;
            }
            eof = 1;
        }
        have += got;
    }
    if (fflush(stdout) != 0) {
        perror("ind189: write error");
        return 2;
    }

    fprintf(stderr, "total=%lld connected=%lld hyp=%lld nontraceable=%lld\n",
            cnt_total, cnt_conn, cnt_hyp, cnt_nt);
    for (int s = 0; s <= MAXN; s++)
        if (hist_sigma[s]) fprintf(stderr, "sigma=%d hyp=%lld\n", s, hist_sigma[s]);
    for (int k = 0; k <= MAXN; k++)
        if (hist_n[k]) fprintf(stderr, "n=%d hyp=%lld\n", k, hist_n[k]);
    return 0;
}
#endif
