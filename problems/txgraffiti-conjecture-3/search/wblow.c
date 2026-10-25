/* Weighted lexicographic blow-ups.  Reads graph6 base graphs B and a target degree r; enumerates
   all weightings t : V -> {1..T} with sum_{w in N(v)} t(w) = r for every v (backtracking), and
   prints the blow-up B[t] (vertex v replaced by an independent set of t(v) twins) as graph6 when
   it has at most 62 vertices.  Usage: wblow r T [maxout_per_graph] < base.g6 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n, A[64][64], deg[64], nb[64][64], R, T, wt[64], cnt, maxout;
static long outtotal;
static int parse(const char *s) {
    if (*s == '>') return 0;
    n = s[0] - 63; if (n < 1 || n > 62) return 0;
    memset(A, 0, sizeof A); memset(deg, 0, sizeof deg);
    int k = 0, len = strlen(s);
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++, k++) {
        int byte = 1 + k / 6, bit = 5 - k % 6; if (byte >= len) return 0;
        if (((s[byte] - 63) >> bit) & 1) { A[i][j] = A[j][i] = 1; }
    }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (A[i][j]) nb[i][deg[i]++] = j;
    return 1;
}
static void emit(void) {
    int N = 0, base[64], idx[64];
    for (int v = 0; v < n; v++) { base[v] = N; N += wt[v]; }
    if (N > 62) return;
    static int B[64][64]; memset(B, 0, sizeof B);
    for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) if (A[u][v])
        for (int a = 0; a < wt[u]; a++) for (int b = 0; b < wt[v]; b++) B[base[u] + a][base[v] + b] = 1;
    (void)idx;
    char out[4096]; int p = 0, k = 0, x = 0; out[p++] = 63 + N;
    for (int j = 1; j < N; j++) for (int i = 0; i < j; i++) {
        x = (x << 1) | B[i][j]; k++; if (k == 6) { out[p++] = 63 + x; x = 0; k = 0; } }
    if (k) { x <<= (6 - k); out[p++] = 63 + x; }
    out[p] = 0; puts(out); cnt++; outtotal++;
}
/* assign weights in vertex order; check each vertex's constraint once all its neighbours are set */
static int ok_partial(int upto) {
    for (int v = 0; v < n; v++) {
        int s = 0, allset = 1;
        for (int j = 0; j < deg[v]; j++) { int w = nb[v][j]; if (w <= upto) s += wt[w]; else allset = 0; }
        if (s > R) return 0;
        if (allset && s != R) return 0;
        if (!allset) { int rem = 0; for (int j = 0; j < deg[v]; j++) if (nb[v][j] > upto) rem++;
            if (s + rem > R || s + rem * T < R) return 0; }
    }
    return 1;
}
static void rec(int v) {
    if (maxout && cnt >= maxout) return;
    if (v == n) { emit(); return; }
    for (int w = 1; w <= T; w++) { wt[v] = w; if (ok_partial(v)) rec(v + 1); }
}
int main(int argc, char **argv) {
    R = atoi(argv[1]); T = atoi(argv[2]); maxout = argc > 3 ? atoi(argv[3]) : 0;
    char line[4096];
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\r\n")] = 0;
        if (!parse(line)) continue;
        cnt = 0; rec(0);
    }
    fprintf(stderr, "blow-ups emitted: %ld\n", outtotal);
    return 0;
}
