// mmsearch.cpp -- exhaustive search for valid n-subsets of Z_N (unique multiset-sum problem).
//
// A subset A of Z_N with |A| = n is *valid* if the all-ones multiset is the only multiset of
// size n drawn from A whose sum is sum(A) (mod N).
//
// Search: depth-first over sorted sets {0 = a_0 < a_1 = d < a_2 < ... < a_{n-1}} where
//   d = min over pairs x != y in A of gcd(x - y, N)            (an affine invariant),
// i.e. we enumerate one representative per orbit of the affine group x -> u x + v
// (u a unit), namely the lexicographically smallest sorted image.  Pruning:
//   (1) validity is hereditary (subsets of valid sets are valid);
//   (2) every pairwise difference must have gcd(diff, N) >= d;
//   (3) canonical third element: for every ordered pair (a, b) of the partial set with
//       gcd(b - a, N) = d and every unit u with u (b - a) = d, the image z = u (c - a) of every
//       element c must not satisfy d < z < a_2.  (Such an image would give a lexicographically
//       smaller representative of the same orbit; images can only gain elements later.)
//
// Incremental validity test for adding x to a valid k-set P (sum s, k elements):
//   P + {x} is valid  iff  x + s  is not in (k+1)P  and  s - g x  is not in (k-g)P  for g=1..k,
// where jP is the j-fold multiset sumset (0P = {0}).  Proof: write a rival as k_x = 1 + g with
// g in {-1, 1, 2, ..., k}; the remaining multiplicities form a multiset of size k - g over P.
//
// Usage: mmsearch n Nlo Nhi [threads] [maxprint]
// Output: one line per modulus N with node counts and the number of valid sets found.
#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <mutex>
#include <numeric>
#include <string>
#include <thread>
#include <vector>
#include <chrono>
#include <set>
using namespace std;
typedef uint64_t u64;
static inline chrono::steady_clock::time_point chrono_now() { return chrono::steady_clock::now(); }
static inline double chrono_since(chrono::steady_clock::time_point t0) {
  return chrono::duration<double>(chrono::steady_clock::now() - t0).count();
}

static const int MAXW = 40;  // N <= 2560
static const int MAXN = 16;

struct Ctx {
  int N, n, W, d;
  u64 lastmask;
  vector<int> isunit;       // isunit[u] = gcd(u,N)==1
  vector<int> invN;         // invN[u] = u^{-1} mod N for units, else 0
  u64 fmM;                  // fastmod constant for N
  vector<int> gcdN;         // gcdN[v] = gcd(v,N)
  // state
  int a[MAXN];
  u64 S[MAXN + 1][MAXN + 2][MAXW];  // S[depth][j] = j-fold sumset of the depth-element prefix
  // normalizing maps: z -> u*(z - base) mod N; stored per depth as a flat list with counts
  vector<pair<int, int>> maps;  // (base, u)
  vector<size_t> mapcnt;        // maps.size() at each depth
  long long nodes[MAXN + 1];
  long long found;
  long long deadends;
  vector<vector<int>> sols;
  int maxprint;
  vector<int> cbuf[MAXN + 2];
};

static inline void shl_or(const Ctx& c, u64* out, const u64* in, int s) {
  int ws = s >> 6, bs = s & 63, W = c.W;
  for (int i = W - 1; i >= ws; i--) {
    u64 v = in[i - ws] << bs;
    if (bs && i - ws - 1 >= 0) v |= in[i - ws - 1] >> (64 - bs);
    out[i] |= v;
  }
  out[W - 1] &= c.lastmask;
}
static inline void shr_or(const Ctx& c, u64* out, const u64* in, int t) {
  int ws = t >> 6, bs = t & 63, W = c.W;
  for (int i = 0; i + ws < W; i++) {
    u64 v = in[i + ws] >> bs;
    if (bs && i + ws + 1 < W) v |= in[i + ws + 1] << (64 - bs);
    out[i] |= v;
  }
}
// out |= {(v + s) mod N : v in in}
static inline void rot_or(const Ctx& c, u64* out, const u64* in, int s) {
  if (s == 0) {
    for (int i = 0; i < c.W; i++) out[i] |= in[i];
    return;
  }
  shl_or(c, out, in, s);
  shr_or(c, out, in, c.N - s);
}
static inline bool test(const u64* b, int v) { return (b[v >> 6] >> (v & 63)) & 1ULL; }

// compute S[k+1][*] from S[k][*] after appending x (prefix now has k+1 elements)
static void update_sumsets(Ctx& c, int k, int x) {
  int jmax = c.n + 1;
  u64(*O)[MAXW] = c.S[k];
  u64(*Nw)[MAXW] = c.S[k + 1];
  memset(Nw[0], 0, sizeof(u64) * c.W);
  Nw[0][0] = 1ULL;  // {0}
  for (int j = 1; j <= jmax; j++) {
    memcpy(Nw[j], O[j], sizeof(u64) * c.W);
    rot_or(c, Nw[j], Nw[j - 1], x);
  }
}

static int mod(long long v, int N) {
  v %= N;
  if (v < 0) v += N;
  return (int)v;
}

// enumerate all units u with u*g == d (mod N), where gcd(g,N) == d
static void units_mapping(const Ctx& c, int g, vector<int>& out) {
  out.clear();
  int M = c.N / c.d;
  int gp = (g / c.d) % M;  // g = d*gp, gcd(gp, M) = 1
  // inverse of gp mod M
  int inv = -1;
  if (M == 1) inv = 0;
  else {
    // extended euclid
    long long r0 = M, r1 = gp, t0 = 0, t1 = 1;
    while (r1) {
      long long q = r0 / r1;
      long long r2 = r0 - q * r1; r0 = r1; r1 = r2;
      long long t2 = t0 - q * t1; t0 = t1; t1 = t2;
    }
    inv = mod(t0, M);
  }
  for (int t = 0; t < c.d; t++) {
    int u = inv + t * M;
    if (u < c.N && c.isunit[u]) out.push_back(u);
  }
}

// try to add maps for pairs involving the new element at index k (prefix has k+1 elements),
// and check images of x under old maps.  Returns false if pruned.
static inline int fmod32(const Ctx& c, uint32_t a) {
  u64 low = c.fmM * a;
  return (int)(((__uint128_t)low * (uint32_t)c.N) >> 64);
}

static bool canon_ok(Ctx& c, int k) {
  int x = c.a[k];
  int thr = (k > 2) ? c.a[2] : (k == 2 ? x : 0);  // images must not lie in (d, thr)
  int d = c.d, N = c.N;
  // old maps: image of x
  for (size_t i = 0; i < c.maps.size(); i++) {
    int z = fmod32(c, (uint32_t)c.maps[i].second * (uint32_t)(x - c.maps[i].first + N));
    if (z > d && z < thr) return false;
  }
  // new maps
  static thread_local vector<int> us;
  for (int i = 0; i < k; i++) {
    for (int dir = 0; dir < 2; dir++) {
      int base = dir ? x : c.a[i];
      int other = dir ? c.a[i] : x;
      int g = mod(other - base, N);
      if (c.gcdN[g] != d) continue;
      if (d == 1) {
        us.clear();
        us.push_back(c.invN[g]);
      } else {
        units_mapping(c, g, us);
      }
      for (int u : us) {
        for (int j = 0; j <= k; j++) {
          int z = fmod32(c, (uint32_t)u * (uint32_t)(c.a[j] - base + N));
          if (z > d && z < thr) return false;
        }
        c.maps.push_back({base, u});
      }
    }
  }
  return true;
}

// Inherited candidate lists: cand holds every y > a[k-1] such that a[0..k-1] + {y} is valid,
// passes the gcd filter and (once a[2] is fixed) is not mapped into (d, a[2]) by any current
// normalizing map.  All three properties are inherited by larger prefixes, so the children's
// candidates are a filtered sublist.
static void dfs2(Ctx& c, int k, const vector<int>& cand) {
  int N = c.N, n = c.n, d = c.d;
  long long s = 0;
  for (int i = 0; i < k; i++) s += c.a[i];
  vector<int>& nc = c.cbuf[k + 1];
  size_t m = cand.size();
  int kk = k + 1;  // prefix size after adding x
  for (size_t idx = 0; idx < m; idx++) {
    if ((long long)(m - idx - 1) < (long long)(n - kk)) break;  // look-ahead
    int x = cand[idx];
    c.a[k] = x;
    size_t save = c.maps.size();
    if (kk == n) {
      if (canon_ok(c, k)) {
        c.nodes[kk]++;
        c.found++;
        if ((int)c.sols.size() < c.maxprint) c.sols.push_back(vector<int>(c.a, c.a + n));
      }
      c.maps.resize(save);
      continue;
    }
    // 1. validity filter of the remaining candidates (cheap), before the canonicity test
    update_sumsets(c, k, x);
    const u64(*Sk)[MAXW] = c.S[kk];
    int sm = (int)((s + x) % N);
    nc.clear();
    for (size_t j = idx + 1; j < m; j++) {
      int y = cand[j];
      if (d > 1 && c.gcdN[y - x] < d) continue;
      int v = sm + y; if (v >= N) v -= N;
      if (test(Sk[kk + 1], v)) continue;
      bool bad = false;
      v = sm;
      for (int g = 1; g <= kk; g++) {
        v -= y; if (v < 0) v += N;
        if (test(Sk[kk - g], v)) { bad = true; break; }
      }
      if (!bad) nc.push_back(y);
    }
    if ((long long)nc.size() < (long long)(n - kk)) { c.deadends++; continue; }
    // 2. canonicity of the new prefix
    if (!canon_ok(c, k)) {
      c.maps.resize(save);
      continue;
    }
    c.nodes[kk]++;
    // 3. canonicity filter of the candidates under the maps that are new for them
    size_t mapfrom = (kk == 3) ? 0 : save;
    int thr = (kk >= 3) ? c.a[2] : 0;
    vector<int> mine;
    mine.reserve(nc.size());
    for (int y : nc) {
      bool bad = false;
      for (size_t t = mapfrom; t < c.maps.size(); t++) {
        int z = fmod32(c, (uint32_t)c.maps[t].second * (uint32_t)(y - c.maps[t].first + N));
        if (z > d && z < thr) { bad = true; break; }
      }
      if (!bad) mine.push_back(y);
    }
    if ((long long)mine.size() >= (long long)(n - kk)) dfs2(c, kk, mine);
    c.maps.resize(save);
  }
}

struct Result {
  int N;
  long long nodes[MAXN + 1];
  long long found;
  vector<vector<int>> sols;
  double secs;
};

static Result run_modulus(int n, int N, int maxprint) {
  Result R;
  R.N = N;
  memset(R.nodes, 0, sizeof(R.nodes));
  R.found = 0;
  auto t0 = chrono_now();
  Ctx* cp = new Ctx();
  Ctx& c = *cp;
  c.N = N; c.n = n; c.W = (N + 63) / 64;
  c.lastmask = (N % 64) ? ((1ULL << (N % 64)) - 1) : ~0ULL;
  c.isunit.assign(N, 0); c.gcdN.assign(N, 0);
  for (int v = 0; v < N; v++) { c.gcdN[v] = std::gcd(v, N); c.isunit[v] = (c.gcdN[v] == 1); }
  c.invN.assign(N, 0);
  for (int v = 1; v < N; v++)
    if (c.isunit[v])
      for (int w = 1; w < N; w++)
        if ((long long)v * w % N == 1) { c.invN[v] = w; break; }
  c.fmM = UINT64_C(0xFFFFFFFFFFFFFFFF) / (u64)N + 1;
  c.maxprint = maxprint;
  for (int d = 1; d < N; d++) {
    if (N % d) continue;
    c.d = d;
    memset(c.nodes, 0, sizeof(c.nodes));
    c.found = 0;
    c.maps.clear();
    // depth 1: {0}
    c.a[0] = 0;
    memset(c.S[0], 0, sizeof(c.S[0]));
    c.S[0][0][0] = 1ULL;  // 0-fold sumset {0}; j-fold sumsets of empty set are empty for j>=1
    update_sumsets(c, 0, 0);  // S[1] = sumsets of {0}
    // depth 2: {0, d}  (validity of a 2-set {0,d}: needs d != 0 only)
    c.a[1] = d;
    if (n == 1) break;
    // maps for pair (0,d) and (d,0)
    if (!canon_ok(c, 1)) continue;
    c.nodes[2]++;
    if (n == 2) {
      c.found++;
      if ((int)c.sols.size() < maxprint) c.sols.push_back({0, d});
    } else {
      update_sumsets(c, 1, d);
      vector<int> cand;
      const u64(*Sk)[MAXW] = c.S[2];
      int sm = d % N;
      for (int y = d + 1; y < N; y++) {
        if (d > 1 && (c.gcdN[y] < d || c.gcdN[y - d] < d)) continue;
        if (test(Sk[3], (sm + y) % N)) continue;
        bool bad = false;
        for (int g = 1; g <= 2; g++)
          if (test(Sk[2 - g], mod((long long)sm - (long long)g * y, N))) { bad = true; break; }
        if (!bad) cand.push_back(y);
      }
      dfs2(c, 2, cand);
    }
    for (int i = 0; i <= MAXN; i++) R.nodes[i] += c.nodes[i];
    R.found += c.found;
  }
  R.sols = c.sols;
  delete cp;
  R.secs = chrono_since(t0);
  return R;
}

// lexicographically smallest sorted image of A under x -> u (x - a), a in A, u unit
static vector<int> canonical_form(const vector<int>& A, int N) {
  vector<int> best;
  vector<int> img(A.size());
  for (int a : A)
    for (int u = 1; u < N; u++) {
      if (std::gcd(u, N) != 1) continue;
      for (size_t i = 0; i < A.size(); i++) img[i] = (int)(((long long)u * (A[i] - a + N)) % N);
      sort(img.begin(), img.end());
      if (best.empty() || img < best) best = img;
    }
  return best;
}

int main(int argc, char** argv) {
  if (argc < 4) {
    fprintf(stderr, "usage: %s n Nlo Nhi [threads] [maxsols]\n", argv[0]);
    return 1;
  }
  int n = atoi(argv[1]), Nlo = atoi(argv[2]), Nhi = atoi(argv[3]);
  int threads = argc > 4 ? atoi(argv[4]) : 1;
  int maxsols = argc > 5 ? atoi(argv[5]) : 100000;
  if (n < 2 || n > MAXN - 2 || Nhi >= 64 * MAXW || Nlo < 2) {
    fprintf(stderr, "bad args\n");
    return 1;
  }
  vector<int> Ns;
  for (int N = Nlo; N <= Nhi; N++) if (N >= n) Ns.push_back(N);
  // larger moduli first for load balance
  reverse(Ns.begin(), Ns.end());
  vector<Result> res(Ns.size());
  atomic<size_t> next(0);
  mutex mu;
  auto worker = [&]() {
    for (;;) {
      size_t i = next++;
      if (i >= Ns.size()) return;
      res[i] = run_modulus(n, Ns[i], maxsols);
      lock_guard<mutex> lk(mu);
      const Result& R = res[i];
      long long nn = 0;
      for (int t = 0; t <= MAXN; t++) nn += R.nodes[t];
      set<vector<int>> orbits;
      for (auto& A : R.sols) orbits.insert(canonical_form(A, R.N));
      fprintf(stderr, "CHECKPOINT N=%d found=%lld orbits=%zu nodes=%lld secs=%.3f", R.N, R.found,
              orbits.size(), nn, R.secs);
      for (auto& o : orbits) {
        fprintf(stderr, " [");
        for (size_t t = 0; t < o.size(); t++) fprintf(stderr, t ? " %d" : "%d", o[t]);
        fprintf(stderr, "]");
      }
      fprintf(stderr, "\n");
      fflush(stderr);
    }
  };
  vector<thread> th;
  for (int t = 0; t < threads; t++) th.emplace_back(worker);
  for (auto& t : th) t.join();
  reverse(res.begin(), res.end());
  printf("# mmsearch n=%d N=%d..%d\n", n, Nlo, Nhi);
  long long totnodes = 0;
  double totsecs = 0;
  for (auto& R : res) {
    long long nn = 0;
    for (int i = 0; i <= MAXN; i++) nn += R.nodes[i];
    totnodes += nn;
    totsecs += R.secs;
    set<vector<int>> orbits;
    for (auto& A : R.sols) orbits.insert(canonical_form(A, R.N));
    printf("N=%d found=%lld orbits=%zu%s nodes=%lld secs=%.3f depth:", R.N, R.found, orbits.size(),
           (R.found > (long long)R.sols.size()) ? "+" : "", nn, R.secs);
    for (int i = 2; i <= n; i++) printf(" %lld", R.nodes[i]);
    printf("\n");
    for (auto& o : orbits) {
      printf("  orbit N=%d:", R.N);
      for (int v : o) printf(" %d", v);
      printf("\n");
    }
  }
  printf("# total nodes=%lld cpu_secs=%.1f\n", totnodes, totsecs);
  return 0;
}
