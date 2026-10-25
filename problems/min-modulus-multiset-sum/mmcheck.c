/* mmcheck.c -- independent second implementation of the exhaustive search for valid n-subsets
 * of Z_N (unique multiset-sum problem).  Written separately from mmsearch*.cpp.
 *
 * Differences from mmsearch: plain C; validity is decided by *counting* multisets (capped DP
 * tables: number of multisets of size j with sum v, capped at 2), straight from the definition;
 * after the first three elements {0, d, a2} the remaining elements are chosen in DECREASING
 * order; canonicity is recomputed from scratch for every new node.
 *
 * Normal form searched (one per affine orbit x -> u x + v, u a unit):
 *   sorted A = {0 < d < a2 < ...} where d = min_{x != y in A} gcd(x - y, N), every pairwise
 *   difference has gcd >= d, and no image u(A - p) (p, q in A, gcd(q - p, N) = d, u a unit with
 *   u (q - p) = d mod N) has an element strictly between d and a2.
 *
 * Every node keeps the list of its valid one-element extensions (validity is hereditary, so a
 * child's list is a filtered suffix of its parent's list).
 *
 * Usage: mmcheck n Nlo Nhi
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXMOD 2600
#define MAXK 14

static int N, n, d, a2;
static int gcdtab[MAXMOD];
static uint8_t T[MAXK + 1][MAXK + 2][MAXMOD]; /* T[k][j][v]: table for the current k-element set */
static int el[MAXK + 1];                     /* current elements; el[0]=0, el[1]=d, el[2]=a2 */
static int sigma[MAXK + 2];                  /* sigma[k] = el[0] + ... + el[k-1] mod N */
static int cand[MAXK + 2][MAXMOD], ncand[MAXK + 2]; /* valid extensions of el[0..m-1], decreasing */
static int ustart[MAXMOD + 1], uflat[MAXMOD];       /* units u with u*g = d, listed per g */
static long long nodes[MAXK + 2], found;
static FILE *solout;

static int gcd(int a, int b) {
  while (b) {
    int t = a % b;
    a = b;
    b = t;
  }
  return a;
}

static int invmod(int a) { /* inverse of a unit a mod N */
  long long r0 = N, r1 = a, s0 = 0, s1 = 1;
  while (r1) {
    long long q = r0 / r1, t;
    t = r0 - q * r1, r0 = r1, r1 = t;
    t = s0 - q * s1, s0 = s1, s1 = t;
  }
  s0 %= N;
  return (int)(s0 < 0 ? s0 + N : s0);
}

/* for every g with gcd(g, N) = d: the units u with u*g = d (mod N), i.e. g = d * u^{-1} */
static void build_units(void) {
  static int cnt[MAXMOD], pos[MAXMOD];
  memset(cnt, 0, sizeof(int) * N);
  for (int u = 1; u < N; u++)
    if (gcdtab[u] == 1) cnt[(int)((long long)d * invmod(u) % N)]++;
  ustart[0] = 0;
  for (int g = 0; g < N; g++) ustart[g + 1] = ustart[g] + cnt[g], pos[g] = ustart[g];
  for (int u = 1; u < N; u++)
    if (gcdtab[u] == 1) uflat[pos[(int)((long long)d * invmod(u) % N)]++] = u;
}

/* T[k+1] = table of the set el[0..k] (el[k] = x newly added), from T[k] */
static void add_to_table(int k, int x) {
  for (int v = 0; v < N; v++) T[k + 1][0][v] = 0;
  T[k + 1][0][0] = 1;
  for (int j = 1; j <= n; j++) {
    const uint8_t *src = T[k][j], *prev = T[k + 1][j - 1];
    uint8_t *dst = T[k + 1][j];
    for (int v = 0; v < x; v++) { /* w = v - x + N */
      int s = src[v] + prev[v - x + N];
      dst[v] = (uint8_t)(s > 2 ? 2 : s);
    }
    for (int v = x; v < N; v++) { /* w = v - x */
      int s = src[v] + prev[v - x];
      dst[v] = (uint8_t)(s > 2 ? 2 : s);
    }
  }
}

/* is el[0..k-1] + {x} valid, given T[k] for el[0..k-1] (assumed valid)?  sig = sum of el[0..k-1]
 * reduced mod N. */
static int valid_ext(int k, int sig, int x) {
  int v = sig + x - N; /* sum of the (k+1)-set */
  if (v < 0) v += N;
  int total = 0;
  /* multisets of size k+1 over el + {x}: i copies of x and k+1-i elements of el */
  for (int i = 0; i <= k + 1; i++) {
    total += T[k][k + 1 - i][v];
    if (total >= 2) return 0;
    v -= x;
    if (v < 0) v += N;
  }
  return total == 1;
}

/* is el[0..k-1] + {x, y} valid, given T[k] for el[0..k-1]?  Counts the multisets with a copies
 * of x and b copies of y directly, without building the table of el[0..k-1] + {x}. */
static int valid_pair(int k, int sig, int x, int y) {
  int va = (int)(((long long)sig + x + y) % N); /* target - a*x */
  int total = 0;
  for (int a = 0; a <= k + 2; a++) {
    int v = va;
    for (int b = 0; a + b <= k + 2; b++) {
      total += T[k][k + 2 - a - b][v];
      if (total >= 2) return 0;
      v -= y;
      if (v < 0) v += N;
    }
    va -= x;
    if (va < 0) va += N;
  }
  return total == 1;
}

/* canonicity test of the m-element set el[0..m-1] (from scratch) */
static int canonical_ok(int m) {
  for (int p = 0; p < m; p++)
    for (int q = 0; q < m; q++) {
      if (p == q) continue;
      int g = el[q] - el[p];
      if (g < 0) g += N;
      if (gcdtab[g] != d) continue;
      for (int t = ustart[g]; t < ustart[g + 1]; t++) {
        int u = uflat[t];
        for (int r = 0; r < m; r++) {
          int diff = el[r] - el[p];
          if (diff < 0) diff += N;
          int z = (int)((unsigned)u * (unsigned)diff % (unsigned)N);
          if (z > d && z < a2) return 0;
        }
      }
    }
  return 1;
}

static int gcd_ok(int m, int x) {
  for (int i = 0; i < m; i++) {
    int g = x - el[i];
    if (g < 0) g += N;
    if (gcdtab[g] < d) return 0;
  }
  return 1;
}

static void report(void) {
  found++;
  if (solout) {
    fprintf(solout, "SOL N=%d", N);
    for (int i = 0; i < n; i++) fprintf(solout, " %d", el[i]);
    fprintf(solout, "\n");
  }
}

/* el[0..m-1] chosen (m >= 3); choose the remaining n - m elements from cand[m] */
static void dfs(int m) {
  int need = n - m, nc = ncand[m];
  if (need == 2) { /* last two elements x > y: test el + {x, y} directly */
    for (int i = 0; i + 1 < nc; i++) {
      int x = cand[m][i];
      el[m] = x;
      int checked = 0;
      for (int j = i + 1; j < nc; j++) {
        int y = cand[m][j];
        if (gcdtab[x - y] < d) continue;
        if (!valid_pair(m, sigma[m], x, y)) continue;
        if (!checked) {
          checked = 1;
          if (!canonical_ok(m + 1)) break;
          nodes[m + 1]++;
        }
        el[m + 1] = y;
        if (!canonical_ok(m + 2)) continue;
        nodes[m + 2]++;
        report();
      }
    }
    return;
  }
  for (int i = 0; i + need <= nc; i++) {
    int x = cand[m][i];
    el[m] = x;
    if (!canonical_ok(m + 1)) continue;
    nodes[m + 1]++;
    if (need == 1) {
      report();
      continue;
    }
    add_to_table(m, x);
    sigma[m + 1] = (sigma[m] + x) % N;
    int c = 0;
    for (int j = i + 1; j < nc; j++) {
      int y = cand[m][j];
      if (gcdtab[x - y] < d) continue;
      if (!valid_ext(m + 1, sigma[m + 1], y)) continue;
      cand[m + 1][c++] = y;
    }
    ncand[m + 1] = c;
    if (c >= need - 1) dfs(m + 1);
  }
}

static void run(void) {
  for (int v = 0; v < N; v++) gcdtab[v] = gcd(v, N);
  memset(nodes, 0, sizeof nodes);
  found = 0;
  for (d = 1; d < N; d++) {
    if (N % d) continue;
    build_units();
    /* table for {0} */
    memset(T[0], 0, sizeof T[0]);
    T[0][0][0] = 1;
    el[0] = 0;
    add_to_table(0, 0);
    el[1] = d;
    add_to_table(1, d);
    if (n == 2) {
      found++;
      continue;
    }
    for (a2 = d + 1; a2 < N; a2++) {
      if (!gcd_ok(2, a2)) continue;
      if (!valid_ext(2, d, a2)) continue;
      el[2] = a2;
      if (!canonical_ok(3)) continue;
      nodes[3]++;
      if (n == 3) {
        report();
        continue;
      }
      add_to_table(2, a2);
      sigma[3] = (d + a2) % N;
      int c = 0;
      for (int y = N - 1; y > a2; y--) {
        if (!gcd_ok(3, y)) continue;
        if (!valid_ext(3, sigma[3], y)) continue;
        cand[3][c++] = y;
      }
      ncand[3] = c;
      if (c >= n - 3) dfs(3);
    }
  }
}

int main(int argc, char **argv) {
  if (argc < 4) {
    fprintf(stderr, "usage: %s n Nlo Nhi\n", argv[0]);
    return 1;
  }
  n = atoi(argv[1]);
  int lo = atoi(argv[2]), hi = atoi(argv[3]);
  if (n < 2 || n > MAXK - 1 || hi >= MAXMOD) return 1;
  solout = stdout;
  for (N = (lo > n ? lo : n); N <= hi; N++) {
    clock_t t0 = clock();
    run();
    double secs = (double)(clock() - t0) / CLOCKS_PER_SEC;
    long long tot = 0;
    for (int i = 0; i <= MAXK + 1; i++) tot += nodes[i];
    printf("N=%d n=%d found=%lld nodes=%lld secs=%.3f depth:", N, n, found, tot, secs);
    for (int i = 3; i <= n; i++) printf(" %lld", nodes[i]);
    printf("\n");
    fflush(stdout);
  }
  return 0;
}
