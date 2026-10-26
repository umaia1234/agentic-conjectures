/* Exhaustive check of WOWII Conjecture 300 on graph6 input: a C companion to
   check_wowii300.py --graph6 that prints the same summary lines, fast enough for all
   connected graphs on 11 vertices.

   The conjecture: if G is connected with n > 2 vertices, then
   gamma_t(G) <= (n + f)/2, where f is the number of vertices v at which
   lambda(v) = alpha(complement[N_complement(v)]) attains its minimum.

   For every connected graph with n > 2 the program computes gamma_t by trying vertex
   subsets in order of size (Gosper's hack): the first total dominating set found has the
   minimum size. When 2*gamma_t >= n it also computes lambda(v) as the clique number of
   G - N_G[v] (an independent set of the complement is a clique of G), the frequency f of
   the minimum, and the slack n + f - 2*gamma_t. Since f >= 1, a violation needs
   2*gamma_t >= n + 2, so the graphs with 2*gamma_t < n cannot violate the bound.

   Build: cc -O2 -o sweep_wowii300 sweep_wowii300.c
   Use:   geng -cq 10 | ./sweep_wowii300 [-p]
   With -p it also prints a NEAR line for every graph with 2*gamma_t >= n.
   Exit status 1 if some graph violates the bound or no graph is read. */

#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define MAXN 62

typedef uint64_t set;

static int n;
static set adj[MAXN];

/* Returns 0 on success, -1 for a line that is not a graph6 string with n <= MAXN. */
static int parse_graph6(const char *s)
{
    size_t len = strlen(s);
    while (len > 0 && (s[len - 1] == '\n' || s[len - 1] == '\r'))
        len--;
    if (len == 0 || s[0] < 63 || s[0] - 63 > MAXN)
        return -1;
    n = s[0] - 63;
    if (len != 1 + (size_t)(n * (n - 1) / 2 + 5) / 6)
        return -1;
    memset(adj, 0, sizeof adj);
    int k = 0;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++, k++)
            if (((s[1 + k / 6] - 63) >> (5 - k % 6)) & 1) {
                adj[i] |= (set)1 << j;
                adj[j] |= (set)1 << i;
            }
    return 0;
}

static int connected(void)
{
    set seen = 1, frontier = 1, full = ((set)1 << n) - 1;
    while (frontier) {
        set next = 0;
        for (set f = frontier; f; f &= f - 1)
            next |= adj[__builtin_ctzll(f)];
        frontier = next & ~seen;
        seen |= next;
    }
    return seen == full;
}

static int total_dominating(set d)
{
    for (int v = 0; v < n; v++)
        if (!(adj[v] & d))
            return 0;
    return 1;
}

/* Smallest k such that some k-subset is total dominating (0 if there is none). */
static int gamma_t(void)
{
    set limit = (set)1 << n;
    for (int k = 1; k <= n; k++)
        for (set d = ((set)1 << k) - 1; d < limit;) {
            if (total_dominating(d))
                return k;
            set c = d & -d, r = d + c;
            d = (((r ^ d) >> 2) / c) | r;
        }
    return 0;
}

static int max_clique(set cand)
{
    if (!cand)
        return 0;
    int v = __builtin_ctzll(cand);
    set rest = cand & (cand - 1);
    int with_v = 1 + max_clique(rest & adj[v]);
    if (__builtin_popcountll(rest) <= with_v)
        return with_v;
    int without_v = max_clique(rest);
    return with_v > without_v ? with_v : without_v;
}

/* Number of vertices v at which omega(G - N_G[v]) attains its minimum. */
static int frequency_of_min(void)
{
    set full = ((set)1 << n) - 1;
    int min = MAXN + 1, freq = 0;
    for (int v = 0; v < n; v++) {
        int lam = max_clique(full & ~(adj[v] | (set)1 << v));
        if (lam < min) {
            min = lam;
            freq = 0;
        }
        freq += lam == min;
    }
    return freq;
}

static long long count[MAXN + 1], near[MAXN + 1], violations[MAXN + 1];
static long long gamma_hist[MAXN + 1][MAXN + 1];
static long long slack_hist[MAXN + 1][2 * MAXN + 1]; /* slack s is stored at s + MAXN */

static void print_histogram(const long long *h, int lo, int hi, int offset)
{
    int first = 1;
    putchar('{');
    for (int k = lo; k <= hi; k++)
        if (h[k + offset]) {
            printf("%s%d: %lld", first ? "" : ", ", k, h[k + offset]);
            first = 0;
        }
    putchar('}');
}

int main(int argc, char **argv)
{
    int print_near = argc == 2 && strcmp(argv[1], "-p") == 0;
    if (argc > 1 && !print_near) {
        fprintf(stderr, "usage: sweep_wowii300 [-p]\n");
        return 2;
    }
    char line[256];
    long long skipped = 0, total = 0, bad_violations = 0;
    while (fgets(line, sizeof line, stdin)) {
        if (line[0] == '>' || line[0] == '\n')
            continue;
        if (parse_graph6(line) != 0) {
            fprintf(stderr, "unsupported line: %s", line);
            return 1;
        }
        if (n <= 2 || !connected()) {
            skipped++;
            continue;
        }
        count[n]++;
        total++;
        int g = gamma_t();
        gamma_hist[n][g]++;
        if (2 * g < n)
            continue;
        int f = frequency_of_min();
        int slack = n + f - 2 * g;
        near[n]++;
        slack_hist[n][slack + MAXN]++;
        line[strcspn(line, "\r\n")] = 0;
        if (print_near)
            printf("NEAR %s n=%d gamma_t=%d frequency=%d\n", line, n, g, f);
        if (slack < 0) {
            violations[n]++;
            bad_violations++;
            printf("VIOLATION %s n=%d gamma_t=%d frequency=%d\n", line, n, g, f);
        } else if (slack == 0) {
            printf("EQUALITY %s n=%d gamma_t=%d frequency=%d\n", line, n, g, f);
        }
    }
    for (int k = 0; k <= MAXN; k++) {
        if (!count[k])
            continue;
        printf("n=%d: %lld connected graphs; gamma_t histogram ", k, count[k]);
        print_histogram(gamma_hist[k], 0, MAXN, 0);
        printf("; 2*gamma_t >= n on %lld, slack histogram ", near[k]);
        print_histogram(slack_hist[k], -MAXN, MAXN, MAXN);
        printf("; violations %lld\n", violations[k]);
    }
    printf("skipped %lld graphs with n <= 2 or disconnected\n", skipped);
    int ok = total > 0 && bad_violations == 0;
    printf("%s\n", ok ? "OK" : "FAILED");
    return ok ? 0 : 1;
}
