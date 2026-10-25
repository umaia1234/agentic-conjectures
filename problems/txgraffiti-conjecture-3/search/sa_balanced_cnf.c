/* Simulated annealing for unsatisfiable proper (k-1)-balanced k-CNF formulas (Iwane's class):
   v variables, c = 2(k-1)v/k clauses of k literals over distinct variables, every literal exactly
   k-1 times.  Objective: number of satisfying assignments (exact, maintained incrementally over all
   2^v assignments).  Moves swap two literal occurrences between clauses (keeps occurrence counts).
   Usage: sa_balanced_cnf k v steps restarts seed T0 T1   (k <= 8, v <= 30; prints best counts per
   restart and, on success, the formula in DIMACS clause lines).  Temperatures act on log(#SAT + 1). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
static int K, V, C;
static int cl[256][8];
static uint8_t *cnt;
static long nsat;
static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
/* literal l: variable l>>1, positive iff (l&1)==0; falsified when var bit == (l&1) */
static void apply(int j, int d) {
    uint32_t fix = 0, pat = 0;
    for (int i = 0; i < K; i++) { int l = cl[j][i]; fix |= 1u << (l >> 1); if (l & 1) pat |= 1u << (l >> 1); }
    uint32_t fr = ((V == 32) ? 0xffffffffu : ((1u << V) - 1)) & ~fix;
    uint32_t s = 0;
    for (;;) {
        uint32_t a = s | pat;
        if (d > 0) { if (cnt[a]++ == 0) nsat--; }
        else { if (--cnt[a] == 0) nsat++; }
        if (s == fr) break;
        s = (s - fr) & fr;
    }
}
static int proper(int j, int i, int l) {
    for (int t = 0; t < K; t++) if (t != i && (cl[j][t] >> 1) == (l >> 1)) return 0;
    return 1;
}
static void randomize(void) {
    int occ[512], m = 0;
    for (int l = 0; l < 2 * V; l++) for (int t = 0; t < K - 1; t++) occ[m++] = l;
    for (;;) {
        for (int i = m - 1; i > 0; i--) { int r = rnd() % (i + 1), x = occ[i]; occ[i] = occ[r]; occ[r] = x; }
        for (int j = 0; j < C; j++) for (int i = 0; i < K; i++) cl[j][i] = occ[j * K + i];
        /* repair improper clauses by random swaps */
        int bad = 1, it = 0;
        while (bad && it < 100000) {
            bad = 0; it++;
            for (int j = 0; j < C; j++) for (int i = 0; i < K; i++)
                if (!proper(j, i, cl[j][i])) {
                    bad = 1;
                    int j2 = rnd() % C, i2 = rnd() % K;
                    int a = cl[j][i], b = cl[j2][i2];
                    if (j2 != j && proper(j, i, b) && proper(j2, i2, a)) { cl[j][i] = b; cl[j2][i2] = a; }
                }
        }
        if (!bad) return;
    }
}
int main(int argc, char **argv) {
    if (argc != 8) { fprintf(stderr, "usage: sa_balanced_cnf k v steps restarts seed T0 T1\n"); return 1; }
    K = atoi(argv[1]); V = atoi(argv[2]); long steps = atol(argv[3]); int restarts = atoi(argv[4]);
    if (K < 2 || K > 8 || V < K || V > 30) { fprintf(stderr, "need 2 <= k <= 8, k <= v <= 30\n"); return 1; }
    rs = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atol(argv[5]) * 0x2545F4914F6CDD1DULL;
    C = 2 * (K - 1) * V / K;
    if (2 * (K - 1) * V % K) { fprintf(stderr, "k must divide 2(k-1)v\n"); return 1; }
    cnt = malloc((size_t)1 << V);
    long globalbest = -1;
    for (int r = 0; r < restarts; r++) {
        randomize();
        memset(cnt, 0, (size_t)1 << V); nsat = 1L << V;
        for (int j = 0; j < C; j++) apply(j, 1);
        long best = nsat;
        double T0 = atof(argv[6]), T1 = atof(argv[7]);
        for (long s = 0; s < steps; s++) {
            double T = T0 * pow(T1 / T0, (double)s / steps);
            int j1 = rnd() % C, j2 = rnd() % C; if (j1 == j2) continue;
            int i1 = rnd() % K, i2 = rnd() % K;
            int a = cl[j1][i1], b = cl[j2][i2];
            if (a == b || !proper(j1, i1, b) || !proper(j2, i2, a)) continue;
            long old = nsat;
            apply(j1, -1); apply(j2, -1);
            cl[j1][i1] = b; cl[j2][i2] = a;
            apply(j1, 1); apply(j2, 1);
            long d = nsat - old;
            double x = (old > 0 ? log((double)nsat + 1) - log((double)old + 1) : (double)d);
            if (d <= 0 || (double)(rnd() % 1000000) / 1e6 < exp(-x / T)) {
                if (nsat < best) best = nsat;
                if (nsat == 0) break;
            } else {
                apply(j1, -1); apply(j2, -1);
                cl[j1][i1] = a; cl[j2][i2] = b;
                apply(j1, 1); apply(j2, 1);
            }
        }
        if (globalbest < 0 || best < globalbest) globalbest = best;
        printf("k=%d v=%d c=%d restart %d best %ld (global %ld)\n", K, V, C, r, best, globalbest);
        fflush(stdout);
        if (nsat == 0) {
            printf("UNSAT FORMULA k=%d v=%d c=%d\n", K, V, C);
            for (int j = 0; j < C; j++) { for (int i = 0; i < K; i++) { int l = cl[j][i]; printf("%d ", (l & 1) ? -((l >> 1) + 1) : ((l >> 1) + 1)); } printf("0\n"); }
            fflush(stdout);
            return 0;
        }
    }
    return 0;
}
