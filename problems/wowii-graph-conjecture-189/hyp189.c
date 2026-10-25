// hyp189: filter graph6 graphs for WOWII Conjecture 189.
// Hypothesis: G connected, n > 1, max_v distEven(v) <= 1 + sigma(G),
// distEven(v) = #{w : dist(v,w) even} (v included), sigma = 2nd smallest degree.
// Conclusion: G has a Hamiltonian path.
// Reads graph6 on stdin (n <= 64). Prints counterexamples (hypothesis + not traceable)
// to stdout prefixed "CE ", and near misses (excess 1 or 2, non-traceable, 2-connected)
// prefixed "NEAR<e> " when -near is given. Statistics go to stderr.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint64_t u64;
#define MAXN 64

static int n;
static u64 adj[MAXN];

static int parse_g6(const char *s) {
  const unsigned char *p = (const unsigned char *)s;
  if (strncmp(s, ">>graph6<<", 10) == 0) p += 10;
  int nn;
  if (*p == 126) {
    p++;
    nn = ((p[0] - 63) << 12) | ((p[1] - 63) << 6) | (p[2] - 63);
    p += 3;
  } else {
    nn = *p - 63;
    p++;
  }
  if (nn > MAXN || nn < 0) return -1;
  n = nn;
  for (int i = 0; i < n; i++) adj[i] = 0;
  int bit = 0, val = 0;
  for (int j = 1; j < n; j++)
    for (int i = 0; i < j; i++) {
      if (bit == 0) {
        if (*p < 63 || *p > 126) return -1;
        val = *p - 63;
        p++;
        bit = 6;
      }
      bit--;
      if ((val >> bit) & 1) {
        adj[i] |= 1ULL << j;
        adj[j] |= 1ULL << i;
      }
    }
  return n;
}

static inline u64 allmask(void) { return n == 64 ? ~0ULL : ((1ULL << n) - 1); }

// distances: returns 0 if disconnected. de[v] = distEven(v), ecc[v] = eccentricity.
static int dist_stats(int *de, int *ecc) {
  u64 all = allmask();
  for (int v = 0; v < n; v++) {
    u64 vis = 1ULL << v, fr = vis, even = vis;
    int d = 0, e = 0;
    while (fr) {
      u64 nf = 0, f = fr;
      while (f) {
        int u = __builtin_ctzll(f);
        f &= f - 1;
        nf |= adj[u];
      }
      nf &= ~vis;
      if (!nf) break;
      vis |= nf;
      fr = nf;
      d++;
      e = d;
      if (!(d & 1)) even |= nf;
    }
    if (vis != all) return 0;
    de[v] = __builtin_popcountll(even);
    ecc[v] = e;
  }
  return 1;
}

static int connected_without(int x) {
  u64 all = allmask() & ~(1ULL << x);
  if (!all) return 1;
  int s = __builtin_ctzll(all);
  u64 vis = 1ULL << s, fr = vis;
  while (fr) {
    u64 nf = 0, f = fr;
    while (f) {
      int u = __builtin_ctzll(f);
      f &= f - 1;
      nf |= adj[u];
    }
    nf &= all & ~vis;
    vis |= nf;
    fr = nf;
  }
  return vis == all;
}

static int biconnected(void) {
  if (n < 3) return 0;
  for (int x = 0; x < n; x++)
    if (!connected_without(x)) return 0;
  return 1;
}

static int cmpint(const void *a, const void *b) { return *(const int *)a - *(const int *)b; }

// ---------- traceability ----------
// DFS with node budget, then exact subset DP fallback.
static long long budget;
static int dfs_path(int v, u64 vis, int cnt) {
  if (cnt == n) return 1;
  if (--budget < 0) return -1;
  u64 cand = adj[v] & ~vis;
  // Simple pruning: remaining graph must be "connected from v" (reachability check).
  u64 rem = allmask() & ~vis;
  {
    u64 r = cand, fr = cand;
    while (fr) {
      u64 nf = 0, f = fr;
      while (f) {
        int u = __builtin_ctzll(f);
        f &= f - 1;
        nf |= adj[u];
      }
      nf &= rem & ~r;
      r |= nf;
      fr = nf;
    }
    if (r != rem) return 0;
  }
  // count unvisited vertices with no unvisited neighbor other than possibly v: dead ends
  int dead = 0;
  {
    u64 f = rem;
    while (f) {
      int u = __builtin_ctzll(f);
      f &= f - 1;
      int du = __builtin_popcountll(adj[u] & rem);
      if (du == 0) {
        if (!(adj[u] & (1ULL << v))) return 0;
        // u isolated in remainder: must be the last vertex, only ok if rem == {u}
        if (rem != (1ULL << u)) return 0;
      } else if (du == 1 && !(adj[u] & (1ULL << v))) {
        dead++;
        if (dead > 1) return 0;  // >1 forced endpoint among remainder (path end only once)
      }
    }
  }
  // order candidates by fewest remaining neighbors (Warnsdorff)
  int cs[MAXN], ck[MAXN], m = 0;
  u64 f = cand;
  while (f) {
    int u = __builtin_ctzll(f);
    f &= f - 1;
    cs[m] = u;
    ck[m] = __builtin_popcountll(adj[u] & rem);
    m++;
  }
  for (int i = 1; i < m; i++) {
    int a = cs[i], b = ck[i], j = i - 1;
    while (j >= 0 && ck[j] > b) {
      cs[j + 1] = cs[j];
      ck[j + 1] = ck[j];
      j--;
    }
    cs[j + 1] = a;
    ck[j + 1] = b;
  }
  for (int i = 0; i < m; i++) {
    int r = dfs_path(cs[i], vis | (1ULL << cs[i]), cnt + 1);
    if (r != 0) return r;
  }
  return 0;
}

static uint32_t *dpbuf = NULL;
static int dp_traceable(void) {
  if (n > 28) return -1;
  size_t N = (size_t)1 << n;
  if (!dpbuf) dpbuf = (uint32_t *)malloc(sizeof(uint32_t) * ((size_t)1 << 28));
  memset(dpbuf, 0, sizeof(uint32_t) * N);
  for (int v = 0; v < n; v++) dpbuf[(size_t)1 << v] = 1u << v;
  for (size_t mask = 1; mask < N; mask++) {
    uint32_t ends = dpbuf[mask];
    if (!ends) continue;
    while (ends) {
      int v = __builtin_ctz(ends);
      ends &= ends - 1;
      u64 ext = adj[v] & ~(u64)mask & allmask();
      while (ext) {
        int w = __builtin_ctzll(ext);
        ext &= ext - 1;
        dpbuf[mask | ((size_t)1 << w)] |= 1u << w;
      }
    }
  }
  return dpbuf[N - 1] != 0;
}

// returns 1 traceable, 0 not traceable, -1 unknown
static int traceable(void) {
  if (n <= 1) return 1;
  // try DFS from each start with budget
  budget = 200000;
  // start preferentially at low degree vertices
  int order[MAXN];
  for (int i = 0; i < n; i++) order[i] = i;
  for (int i = 1; i < n; i++) {
    int a = order[i], da = __builtin_popcountll(adj[a]), j = i - 1;
    while (j >= 0 && __builtin_popcountll(adj[order[j]]) > da) {
      order[j + 1] = order[j];
      j--;
    }
    order[j + 1] = a;
  }
  int unknown = 0;
  for (int i = 0; i < n; i++) {
    int r = dfs_path(order[i], 1ULL << order[i], 1);
    if (r == 1) return 1;
    if (r < 0) {
      unknown = 1;
      break;
    }
  }
  if (!unknown) return 0;
  return dp_traceable();
}

int main(int argc, char **argv) {
  int near = 0, verbose = 0, dump = 0;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-dump")) dump = 1;
    if (!strcmp(argv[i], "-near")) near = 1;
    if (!strcmp(argv[i], "-v")) verbose = 1;
  }
  static char line[1 << 16];
  long long tot = 0, conn = 0, hyp = 0, hyp_bic = 0, hyp_big = 0, hyp_diam3 = 0, hyp_all4 = 0,
            ce = 0, unk = 0, nearcnt = 0;
  long long hyp_by_n[MAXN + 1] = {0};
  long long hyp_sig[MAXN + 1] = {0}, hyp_sig_bic_d3[MAXN + 1] = {0};
  int de[MAXN], ecc[MAXN], deg[MAXN];
  while (fgets(line, sizeof line, stdin)) {
    size_t L = strlen(line);
    while (L && (line[L - 1] == '\n' || line[L - 1] == '\r')) line[--L] = 0;
    if (!L) continue;
    if (parse_g6(line) < 0) {
      fprintf(stderr, "bad line: %s\n", line);
      continue;
    }
    tot++;
    if (n < 2 || !dist_stats(de, ecc)) {
      if (dump) printf("%s 0 - - - -\n", line);
      continue;
    }
    conn++;
    for (int v = 0; v < n; v++) deg[v] = __builtin_popcountll(adj[v]);
    qsort(deg, n, sizeof(int), cmpint);
    int sigma = deg[1];
    int mx = 0, diam = 0;
    for (int v = 0; v < n; v++) {
      if (de[v] > mx) mx = de[v];
      if (ecc[v] > diam) diam = ecc[v];
    }
    int excess = mx - 1 - sigma;
    if (dump) {
      if (excess <= 0) printf("%s 1 %d %d 1 %d\n", line, sigma, mx, traceable());
      else printf("%s 1 %d %d 0 -\n", line, sigma, mx);
      continue;
    }
    if (excess > (near ? 2 : 0)) continue;
    int bic = biconnected();
    if (excess <= 0) {
      hyp++;
      hyp_by_n[n]++;
      hyp_sig[sigma]++;
      if (bic && diam >= 3) hyp_sig_bic_d3[sigma]++;
      if (bic) hyp_bic++;
      if (n >= 2 * sigma + 4) hyp_big++;
      if (diam >= 3) hyp_diam3++;
      if (bic && n >= 2 * sigma + 4 && diam >= 3) hyp_all4++;
      int t = traceable();
      if (t == 0) {
        ce++;
        printf("CE %s n=%d sigma=%d maxde=%d diam=%d bic=%d\n", line, n, sigma, mx, diam, bic);
        fflush(stdout);
      } else if (t < 0) {
        unk++;
        printf("UNK %s n=%d sigma=%d maxde=%d diam=%d bic=%d\n", line, n, sigma, mx, diam, bic);
        fflush(stdout);
      } else if (verbose && bic && n >= 2 * sigma + 4 && diam >= 3) {
        printf("HYP4 %s n=%d sigma=%d maxde=%d diam=%d\n", line, n, sigma, mx, diam);
      }
    } else if (near && bic) {
      int t = traceable();
      if (t == 0) {
        nearcnt++;
        printf("NEAR%d %s n=%d sigma=%d maxde=%d diam=%d\n", excess, line, n, sigma, mx, diam);
      }
    }
  }
  fprintf(stderr,
          "total=%lld connected=%lld hyp=%lld hyp_bic=%lld hyp_n>=2s+4=%lld hyp_diam>=3=%lld "
          "hyp_all4=%lld CE=%lld UNK=%lld near_nontraceable=%lld\n",
          tot, conn, hyp, hyp_bic, hyp_big, hyp_diam3, hyp_all4, ce, unk, nearcnt);
  for (int k = 0; k <= MAXN; k++)
    if (hyp_by_n[k]) fprintf(stderr, "  hyp n=%d: %lld\n", k, hyp_by_n[k]);
  for (int k = 0; k <= MAXN; k++)
    if (hyp_sig[k])
      fprintf(stderr, "  hyp sigma=%d: %lld (bic&diam>=3: %lld)\n", k, hyp_sig[k], hyp_sig_bic_d3[k]);
  return 0;
}
