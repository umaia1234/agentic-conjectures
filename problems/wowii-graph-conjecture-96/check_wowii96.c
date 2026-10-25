/*
 * check_wowii96.c: a second, self-contained numeric check of WOWII Conjecture 96
 * and of its per-root form.
 *
 * The Lean proof in AgenticConjectures/WowiiGraphConjecture96.lean is the
 * certificate. This program shares no code with verify_wowii96.py: it has its
 * own graph6 parser, finds independence numbers by branching instead of by
 * enumerating subsets, and finds distance parities by breadth-first search on
 * bitmasks.
 *
 * For a connected graph G on n >= 2 vertices, write alpha for the independence
 * number, l(v) for the independence number of the subgraph induced by N(v),
 * L = max_v l(v), and E(v) for the number of vertices at even distance from v
 * (v included). The program checks
 *
 *   conjecture 96:  alpha <= 1 + min_v E(v) * (L - 1)      (signed arithmetic)
 *   per-root form:  alpha <= max(1, l(v)) + sum_{u != v, d(v,u) even} max(1, l(u) - 1)
 *                   for every root v, with l(u) - 1 truncated at 0
 *
 * Usage:
 *   cc -O2 -o /tmp/check_wowii96 check_wowii96.c
 *   /tmp/check_wowii96 --selftest
 *   geng -cq 9 | /tmp/check_wowii96
 *
 * It prints the number of graphs and of (graph, root) pairs, the violations and
 * the tight cases of both inequalities, and the minimum slack of the conjecture.
 * It exits with status 0 only if every non-blank input line is a connected graph
 * on at least two vertices and neither inequality is violated.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define MAXN 32

typedef uint32_t set;

static set full(int n)
{
    return n == 32 ? ~(set)0 : ((set)1 << n) - 1;
}

/* Size of a largest independent set inside s, by branching on the lowest vertex. */
static int mis(const set *adj, set s)
{
    if (s == 0)
        return 0;
    int v = __builtin_ctz(s);
    set rest = s & (s - 1);
    if ((adj[v] & rest) == 0) /* v has no neighbour in s: some largest set contains it */
        return 1 + mis(adj, rest);
    int take = 1 + mis(adj, rest & ~adj[v]);
    int skip = mis(adj, rest);
    return take > skip ? take : skip;
}

/* The vertices at even distance from v, or 0 if some vertex is unreachable. */
static set even_from(const set *adj, int n, int v)
{
    set seen = (set)1 << v, layer = seen, even = seen;
    for (int d = 1; layer; d++) {
        set next = 0;
        for (set t = layer; t; t &= t - 1)
            next |= adj[__builtin_ctz(t)];
        next &= ~seen;
        seen |= next;
        if (d % 2 == 0)
            even |= next;
        layer = next;
    }
    return seen == full(n) ? even : 0;
}

struct invariants {
    int alpha, max_l, min_e;
    int l[MAXN];
    set even[MAXN];
};

/* Returns 0 if the graph is disconnected. */
static int compute(const set *adj, int n, struct invariants *g)
{
    g->alpha = mis(adj, full(n));
    g->max_l = 0;
    g->min_e = n + 1;
    for (int v = 0; v < n; v++) {
        g->l[v] = mis(adj, adj[v]);
        if (g->l[v] > g->max_l)
            g->max_l = g->l[v];
        g->even[v] = even_from(adj, n, v);
        if (g->even[v] == 0)
            return 0;
        int e = __builtin_popcount(g->even[v]);
        if (e < g->min_e)
            g->min_e = e;
    }
    return 1;
}

static long conjecture_rhs(const struct invariants *g)
{
    return 1 + (long)g->min_e * ((long)g->max_l - 1);
}

static long per_root_bound(const struct invariants *g, int v)
{
    long bound = g->l[v] > 1 ? g->l[v] : 1;
    for (set t = g->even[v] & ~((set)1 << v); t; t &= t - 1) {
        int l = g->l[__builtin_ctz(t)];
        bound += l > 1 ? l - 1 : 1;
    }
    return bound;
}

/* Parse one graph6 string with 1 <= n <= MAXN; returns n, or -1 if malformed. */
static int parse_graph6(const char *line, set *adj)
{
    size_t len = strlen(line);
    if (len >= 10 && strncmp(line, ">>graph6<<", 10) == 0) {
        line += 10;
        len -= 10;
    }
    if (len == 0 || line[0] < 64 || line[0] > 63 + MAXN)
        return -1;
    int n = line[0] - 63;
    long nbits = (long)n * (n - 1) / 2;
    if ((long)len != 1 + (nbits + 5) / 6)
        return -1;
    memset(adj, 0, sizeof(set) * MAXN);
    long k = 0;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++, k++) {
            int c = line[1 + k / 6];
            if (c < 63 || c > 126)
                return -1;
            if ((c - 63) >> (5 - k % 6) & 1) {
                adj[i] |= (set)1 << j;
                adj[j] |= (set)1 << i;
            }
        }
    if (nbits % 6) { /* the padding bits of the last byte must be zero */
        int c = line[len - 1];
        if (c < 63 || c > 126 || ((c - 63) & ((1 << (6 - nbits % 6)) - 1)))
            return -1;
    }
    return n;
}

static void add_edge(set *adj, int a, int b)
{
    adj[a] |= (set)1 << b;
    adj[b] |= (set)1 << a;
}

/* Hand-computed invariants of small graphs: alpha, L, min_v E(v). */
static int expect(const char *name, const set *adj, int n, int alpha, int max_l, int min_e)
{
    struct invariants g;
    int ok = compute(adj, n, &g) && g.alpha == alpha && g.max_l == max_l && g.min_e == min_e;
    printf("%-14s alpha %d, L %d, min E %d, 1 + min E * (L - 1) = %ld: %s\n", name, g.alpha,
           g.max_l, g.min_e, conjecture_rhs(&g), ok ? "as expected" : "UNEXPECTED");
    return ok;
}

static int selftest(void)
{
    set adj[MAXN];
    int ok = 1;
    char name[32];

    memset(adj, 0, sizeof adj); /* K_1: the literal row reads 1 <= 0 */
    ok &= expect("K_1", adj, 1, 1, 0, 1);
    for (int n = 2; n <= 6; n++) { /* K_n: 1 <= 1, tight */
        memset(adj, 0, sizeof adj);
        for (int a = 0; a < n; a++)
            for (int b = a + 1; b < n; b++)
                add_edge(adj, a, b);
        snprintf(name, sizeof name, "K_%d", n);
        ok &= expect(name, adj, n, 1, 1, 1);
    }
    for (int m = 1; m <= 12; m++) { /* K_{1,m}, centre 0: m <= 1 + 1 * (m - 1), tight */
        memset(adj, 0, sizeof adj);
        for (int leaf = 1; leaf <= m; leaf++)
            add_edge(adj, 0, leaf);
        snprintf(name, sizeof name, "K_1,%d", m);
        ok &= expect(name, adj, m + 1, m, m, 1);
    }
    memset(adj, 0, sizeof adj); /* P_4: 2 <= 1 + 2 * 1 */
    for (int v = 0; v < 3; v++)
        add_edge(adj, v, v + 1);
    ok &= expect("P_4", adj, 4, 2, 2, 2);
    memset(adj, 0, sizeof adj); /* C_5: 2 <= 1 + 3 * 1 */
    for (int v = 0; v < 5; v++)
        add_edge(adj, v, (v + 1) % 5);
    ok &= expect("C_5", adj, 5, 2, 2, 3);
    memset(adj, 0, sizeof adj); /* Petersen: 4 <= 1 + 7 * 2 */
    for (int v = 0; v < 5; v++) {
        add_edge(adj, v, (v + 1) % 5);
        add_edge(adj, v, v + 5);
        add_edge(adj, v + 5, (v + 2) % 5 + 5);
    }
    ok &= expect("Petersen", adj, 10, 4, 3, 7);
    memset(adj, 0, sizeof adj); /* K_{2,3}: 3 <= 1 + 2 * 2 */
    for (int a = 0; a < 2; a++)
        for (int b = 2; b < 5; b++)
            add_edge(adj, a, b);
    ok &= expect("K_2,3", adj, 5, 3, 3, 2);
    printf("%s\n", ok ? "OK" : "FAILED");
    return ok ? 0 : 1;
}

int main(int argc, char **argv)
{
    if (argc == 2 && strcmp(argv[1], "--selftest") == 0)
        return selftest();
    if (argc != 1) {
        fprintf(stderr, "usage: %s [--selftest] < graphs.g6\n", argv[0]);
        return 2;
    }
    long graphs = 0, pairs = 0, bad_lines = 0;
    long conj_violations = 0, conj_tight = 0, root_violations = 0, root_tight = 0;
    long min_slack = 0;
    char line[256];
    set adj[MAXN];
    struct invariants g;
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\r\n")] = '\0';
        if (line[0] == '\0')
            continue;
        int n = parse_graph6(line, adj);
        if (n < 2 || !compute(adj, n, &g)) {
            if (bad_lines++ < 10)
                fprintf(stderr, "not a connected graph6 graph on 2..%d vertices: %s\n", MAXN,
                        line);
            continue;
        }
        long slack = conjecture_rhs(&g) - g.alpha;
        if (graphs == 0 || slack < min_slack)
            min_slack = slack;
        graphs++;
        conj_tight += slack == 0;
        if (slack < 0 && conj_violations++ < 10)
            fprintf(stderr, "conjecture 96 fails on %s\n", line);
        for (int v = 0; v < n; v++) {
            long bound = per_root_bound(&g, v);
            pairs++;
            root_tight += g.alpha == bound;
            if (g.alpha > bound && root_violations++ < 10)
                fprintf(stderr, "per-root form fails on %s (root %d)\n", line, v);
        }
    }
    printf("graphs: %ld; (graph, root) pairs: %ld; rejected lines: %ld\n", graphs, pairs,
           bad_lines);
    printf("conjecture 96: %ld violations, tight on %ld graphs, minimum slack %ld\n",
           conj_violations, conj_tight, min_slack);
    printf("per-root form: %ld violations, tight on %ld pairs\n", root_violations, root_tight);
    int ok = graphs > 0 && bad_lines == 0 && conj_violations == 0 && root_violations == 0;
    printf("%s\n", ok ? "OK" : "FAILED");
    return ok ? 0 : 1;
}
