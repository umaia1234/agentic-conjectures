// Erdos problem #307: bounded-support exclusion by a meet-in-the-middle search.
//
// For a given K this program checks exhaustively that no set U of primes
// contained in the first K primes p_1 < ... < p_K satisfies all of
//   (i)   sum_{r in U} 1/r >= 2,
//   (ii)  |U| >= 60,
//   (iii) for every odd r in U:  prod_{s in U, s != r} (s/r) = 1  (Legendre).
// Every solution P,Q of Erdos #307 yields such a U = P u Q: (i) and (iii) are
// proved in Lean (AgenticConjectures/Erdos307.lean) and (ii) is the exact
// 59-prime exclusion of enumerate_59.py (re-run by cross_check_support.py
// fiftynine).  A zero survivor count therefore shows that every solution
// uses a prime larger than p_K.
//
// Build: g++ -O3 -std=c++17 -pthread support_mitm.cpp -o build/support_mitm
//
// Notation: F = {p_1..p_K}, R = F \ U (removed primes), index j <-> p_{j+1}.
//  * (i) is sum_{j in R} 1/p_j <= delta_K := sum_F 1/p - 2.  It is tested with
//    the integer weights w_j = floor(2^64/p_j) against BHI >= 2^64*delta_K, so
//    every R satisfying (i) passes the integer test: a superset is searched.
//    A key-matched set whose ceiling-weight sum exceeds BLO <= 2^64*delta_K
//    is counted as "ambiguous"; when there are none, the key-matched counts
//    are exact.
//  * (iii) is linear over GF(2): with t_j = {odd r != j : (p_j/p_r) = -1} and
//    c = XOR_{j in F} t_j, U passes (iii) iff z = c ^ XOR_{j in R} t_j has no
//    bit outside R.
//
// Search: the key set C consists of the odd coordinates 1..CK.  L = removable
// indices in C, H = removable indices outside C, split alternately into H1
// and H2.  For a fixed X = R n L every coordinate of C \ X must vanish, i.e.
// key(R n H1) ^ key(R n H2) = need(X) on C \ X; the coordinates of X are
// wildcards.  Key bits are ordered so that the most often removed coordinates
// (the largest primes of C) are the low bits, which lets one bucket scan cover
// most wildcard patterns.  Pairs are split by the weight of the H1 part (at
// most half of the remaining budget, or more), so each feasible R is produced
// exactly once while only light halves are iterated.  Every pair meeting the
// key equation, the budget and the size bound receives the full test (iii).
//
// Usage: support_mitm K [--key CK] [--threads T]
// Output: one JSON object on stdout; exit status 0 iff there is no survivor.

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

typedef uint64_t u64;
typedef uint32_t u32;
typedef unsigned __int128 u128;

static int K = 0, CK = 30, NT = 1, MAXR = 0;
static u64 PR[256];
static u64 W[128];
static u64 BLO, BHI;
static u128 TOG[128], C0, ODD;
static u64 KP[128];  // permuted key of t_j
static u64 KPC0;

static u64 powmod(u64 a, u64 e, u64 m) {
  u64 r = 1 % m;
  a %= m;
  while (e) {
    if (e & 1) r = r * a % m;
    a = a * a % m;
    e >>= 1;
  }
  return r;
}

// Legendre symbol by Euler's criterion; p is an odd prime below 2^32.
static int legendre(u64 a, u64 p) {
  u64 t = powmod(a % p, (p - 1) / 2, p);
  if (t == 0) return 0;
  return t == 1 ? 1 : -1;
}

static inline u128 bit(int j) { return (u128)1 << j; }

// Coordinate i in 1..CK becomes key bit CK - i (largest prime of C -> bit 0).
static u64 permkey(u128 x) {
  u64 k = 0;
  for (int i = 1; i <= CK; ++i)
    if ((x >> i) & 1) k |= 1ULL << (CK - i);
  return k;
}

// All subsets S of one half (<= 32 elements) with weight <= BHI and
// |S| <= MAXR, bucketed by key(S) >> shift; the low `shift` key bits are kept.
struct Table {
  std::vector<int> idx;
  std::vector<u64> kv, wv;
  std::vector<u32> start, mask;
  std::vector<uint8_t> low;
  u64 size = 0;
  int shift = 0;

  template <class F>
  void walk(int pos, u64 w, int sz, u32 m, u64 key, F& f) const {
    f(m, key);
    if (sz == MAXR) return;
    for (int q = pos; q < (int)idx.size(); ++q) {
      if (w + wv[q] > BHI) continue;
      walk(q + 1, w + wv[q], sz + 1, m | (1u << q), key ^ kv[q], f);
    }
  }

  void build(const std::vector<int>& elems) {
    idx = elems;
    for (int j : idx) { kv.push_back(KP[j]); wv.push_back(W[j]); }
    u64 n = 0;
    auto counter = [&](u32, u64) { ++n; };
    walk(0, 0, 0, 0, 0, counter);
    if (n >= (1ULL << 32)) { fprintf(stderr, "table too large\n"); exit(1); }
    size = n;
    // About eight entries per bucket, at most 8 low bits, at most 2^28 buckets.
    int b = 0;
    while (b < CK && ((u64)8 << b) < n) ++b;
    if (b > 28) b = 28;
    if (CK - b > 8) b = CK - 8;
    shift = CK - b;
    start.assign((1ULL << b) + 1, 0);
    auto bucketer = [&](u32, u64 key) { start[(key >> shift) + 1]++; };
    walk(0, 0, 0, 0, 0, bucketer);
    for (u64 i = 1; i < start.size(); ++i) start[i] += start[i - 1];
    std::vector<u32> cur(start.begin(), start.end() - 1);
    mask.assign(n, 0);
    low.assign(n, 0);
    const u64 lowmask = (1ULL << shift) - 1;
    auto filler = [&](u32 m, u64 key) {
      u32 pos = cur[key >> shift]++;
      mask[pos] = m;
      low[pos] = (uint8_t)(key & lowmask);
    };
    walk(0, 0, 0, 0, 0, filler);
  }

  void stats_of(u32 m, u64& w, int& sz, u128& t, u128& r) const {
    w = 0; sz = 0; t = 0; r = 0;
    while (m) {
      int q = __builtin_ctz(m);
      m &= m - 1;
      w += wv[q]; ++sz; t ^= TOG[idx[q]]; r |= bit(idx[q]);
    }
  }
};

static Table TAB1, TAB2;
static std::vector<int> LIDX;

struct Stats {
  u64 nodes = 0, buckets = 0, scanned = 0, matched = 0, ambiguous = 0, survivors = 0;
  u64 by_size[128] = {0};
  void add(const Stats& o) {
    nodes += o.nodes; buckets += o.buckets; scanned += o.scanned;
    matched += o.matched; ambiguous += o.ambiguous; survivors += o.survivors;
    for (int i = 0; i < 128; ++i) by_size[i] += o.by_size[i];
  }
};

static std::mutex OUTMU;
static std::vector<std::string> SURVIVORS;

struct XPat { u128 rmask; u64 w; int sz; u128 t; u64 key; };

// Iterated nodes are processed in batches so that bucket and table reads can
// be prefetched; batching changes the order of the work, not the set of checks.
struct Batch {
  std::vector<u32> ma, qnode, qs, qe;
  std::vector<u64> need, qbk;
};
static const size_t NB = 64;

struct Ctx {
  const XPat* x;
  const Table* it;   // half whose light subsets are iterated
  const Table* tab;  // half whose subsets are looked up
  int side;          // 0: iterate H1 (weight <= h); 1: iterate H2, table weight > h
  u64 bx, h, wcap;
  int rx;
  u64 wild;
  Stats* st;
  Batch* bt;
};

static void check_pair(const Ctx& c, u32 ma, u32 mb) {
  u64 wa, wb; int sa, sb; u128 ta, tb, ra, rb;
  c.it->stats_of(ma, wa, sa, ta, ra);
  c.tab->stats_of(mb, wb, sb, tb, rb);
  if (c.side == 1 && wb <= c.h) return;  // this pair belongs to case 0
  if (wa + wb > c.bx || sa + sb > c.rx) return;
  c.st->matched++;
  int total = c.x->sz + sa + sb;
  c.st->by_size[total]++;
  if (c.x->w + wa + wb + (u64)total > BLO) c.st->ambiguous++;
  u128 r = c.x->rmask | ra | rb;
  u128 z = C0 ^ c.x->t ^ ta ^ tb;
  if ((z & ODD & ~r) == 0) {
    c.st->survivors++;
    std::string s = "removed:";
    for (int j = 0; j < K; ++j) if ((r >> j) & 1) s += " " + std::to_string(PR[j]);
    std::lock_guard<std::mutex> g(OUTMU);
    SURVIVORS.push_back(s);
  }
}

static void flush(const Ctx& c) {
  Batch& b = *c.bt;
  const size_t n = b.ma.size();
  if (n == 0) return;
  Stats& st = *c.st;
  const Table& T = *c.tab;
  const u64 lowmask = (1ULL << T.shift) - 1;
  const u64 whigh = c.wild >> T.shift;
  const uint8_t care = (uint8_t)(~c.wild & lowmask);
  b.qnode.clear();
  b.qbk.clear();
  for (size_t i = 0; i < n; ++i) {
    const u64 nhigh = b.need[i] >> T.shift;
    u64 s = whigh;
    while (true) {
      u64 bk = nhigh ^ s;
      b.qnode.push_back((u32)i);
      b.qbk.push_back(bk);
      __builtin_prefetch(&T.start[bk]);
      if (s == 0) break;
      s = (s - 1) & whigh;
    }
  }
  const size_t q = b.qbk.size();
  b.qs.resize(q);
  b.qe.resize(q);
  for (size_t k = 0; k < q; ++k) {
    b.qs[k] = T.start[b.qbk[k]];
    b.qe[k] = T.start[b.qbk[k] + 1];
    __builtin_prefetch(&T.low[b.qs[k]]);
  }
  st.buckets += q;
  for (size_t k = 0; k < q; ++k) {
    const u32 i = b.qnode[k];
    const uint8_t nlow = (uint8_t)(b.need[i] & lowmask);
    st.scanned += b.qe[k] - b.qs[k];
    for (u32 e = b.qs[k]; e < b.qe[k]; ++e)
      if (((T.low[e] ^ nlow) & care) == 0) check_pair(c, b.ma[i], T.mask[e]);
  }
  b.ma.clear();
  b.need.clear();
}

static inline void visit(const Ctx& c, u32 ma, u64 keyacc) {
  c.st->nodes++;
  c.bt->ma.push_back(ma);
  c.bt->need.push_back(KPC0 ^ c.x->key ^ keyacc);
  if (c.bt->ma.size() >= NB) flush(c);
}

static void iterate(const Ctx& c, int pos, u32 ma, u64 wa, int sa, u64 keyacc) {
  visit(c, ma, keyacc);
  if (sa == c.rx) return;
  const Table& I = *c.it;
  for (int q = pos; q < (int)I.idx.size(); ++q) {
    u64 w2 = wa + I.wv[q];
    if (w2 > c.wcap) continue;
    iterate(c, q + 1, ma | (1u << q), w2, sa + 1, keyacc ^ I.kv[q]);
  }
}

static void gen_x(int pos, u128 r, u64 w, int sz, u128 t, std::vector<XPat>& out) {
  out.push_back({r, w, sz, t, 0});
  if (sz == MAXR) return;
  for (int q = pos; q < (int)LIDX.size(); ++q) {
    int j = LIDX[q];
    if (w + W[j] > BHI) continue;
    gen_x(q + 1, r | bit(j), w + W[j], sz + 1, t ^ TOG[j], out);
  }
}

static std::string u128_dec(u128 v) {
  std::string s;
  do { s.insert(s.begin(), char('0' + (int)(v % 10))); v /= 10; } while (v);
  return s;
}

int main(int argc, char** argv) {
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    if (a == "--key" && i + 1 < argc) CK = atoi(argv[++i]);
    else if (a == "--threads" && i + 1 < argc) NT = atoi(argv[++i]);
    else K = atoi(argv[i]);
  }
  if (K < 61 || K > 120 || CK < 8 || CK > 36 || CK >= K - 1 || NT < 1) {
    fprintf(stderr, "usage: %s K [--key CK] [--threads T]  (61 <= K <= 120, 8 <= CK <= 36)\n",
            argv[0]);
    return 2;
  }
  {
    std::vector<char> sv(2000, 1);
    int n = 0;
    for (int i = 2; i < 2000 && n < 256; ++i)
      if (sv[i]) {
        PR[n++] = i;
        for (int j = i * i; j < 2000; j += i) sv[j] = 0;
      }
  }
  MAXR = K - 60;
  const u128 D = (u128)1 << 64;
  u128 lo = 0, hi = 0;
  for (int j = 0; j < K; ++j) {
    W[j] = (u64)(D / PR[j]);
    lo += W[j];
    hi += W[j] + ((D % PR[j]) ? 1 : 0);
  }
  if (lo <= 2 * D) {
    fprintf(stderr, "reciprocal sum of the first K primes is not above 2\n");
    return 1;
  }
  BLO = (u64)(lo - 2 * D);
  BHI = (u64)(hi - 2 * D);
  if (W[0] <= BHI) { fprintf(stderr, "unexpected: prime 2 removable\n"); return 1; }
  for (int j = 0; j < K; ++j) {
    u128 t = 0;
    for (int r = 1; r < K; ++r)
      if (r != j && legendre(PR[j], PR[r]) == -1) t |= bit(r);
    TOG[j] = t;
  }
  C0 = 0;
  for (int j = 0; j < K; ++j) C0 ^= TOG[j];
  ODD = 0;
  for (int r = 1; r < K; ++r) ODD |= bit(r);
  for (int j = 0; j < K; ++j) KP[j] = permkey(TOG[j]);
  KPC0 = permkey(C0);

  std::vector<int> H, H1, H2;
  int fixed_odd = 0;
  for (int j = 1; j < K; ++j) {
    if (W[j] > BHI) { ++fixed_odd; continue; }
    if (j <= CK) LIDX.push_back(j); else H.push_back(j);
  }
  for (size_t i = 0; i < H.size(); ++i) (i % 2 == 0 ? H1 : H2).push_back(H[i]);
  if (H1.size() > 32 || H2.size() > 32) {
    fprintf(stderr, "halves too large; raise --key\n");
    return 1;
  }

  auto t0 = std::chrono::steady_clock::now();
  {
    std::thread b1([&]() { TAB1.build(H1); });
    TAB2.build(H2);
    b1.join();
  }
  std::vector<XPat> xs;
  gen_x(0, 0, 0, 0, 0, xs);
  for (auto& x : xs) x.key = permkey(x.t);
  auto t1 = std::chrono::steady_clock::now();
  fprintf(stderr, "K=%d p_K=%" PRIu64 " CK=%d |L|=%zu |H1|=%zu |H2|=%zu tab1=%" PRIu64
          " tab2=%" PRIu64 " X=%zu build=%.1fs\n", K, PR[K - 1], CK, LIDX.size(), H1.size(),
          H2.size(), TAB1.size, TAB2.size, xs.size(),
          std::chrono::duration<double>(t1 - t0).count());

  // Tasks: (X pattern, case, first element of the iterated subset; -1 = empty).
  struct Task { u32 x; uint8_t side; int8_t first; };
  std::vector<Task> tasks;
  for (u32 xi = 0; xi < xs.size(); ++xi)
    for (int side = 0; side < 2; ++side) {
      const Table& I = side == 0 ? TAB1 : TAB2;
      tasks.push_back({xi, (uint8_t)side, -1});
      for (int q = 0; q < (int)I.idx.size(); ++q) tasks.push_back({xi, (uint8_t)side, (int8_t)q});
    }
  std::atomic<size_t> next(0);
  Stats total;
  std::mutex mu;
  std::vector<std::thread> pool;
  for (int t = 0; t < NT; ++t)
    pool.emplace_back([&]() {
      Stats st;
      Batch bt;
      while (true) {
        size_t i = next.fetch_add(1, std::memory_order_relaxed);
        if (i >= tasks.size()) break;
        const Task& tk = tasks[i];
        const XPat& x = xs[tk.x];
        Ctx c;
        c.x = &x;
        c.side = tk.side;
        c.it = tk.side == 0 ? &TAB1 : &TAB2;
        c.tab = tk.side == 0 ? &TAB2 : &TAB1;
        c.bx = BHI - x.w;
        c.h = c.bx / 2;
        if (tk.side == 1 && c.bx < c.h + 1) continue;  // no pair has H1-weight > h
        c.wcap = tk.side == 0 ? c.h : c.bx - c.h - 1;
        c.rx = MAXR - x.sz;
        c.wild = permkey(x.rmask);
        c.st = &st;
        c.bt = &bt;
        if (tk.first < 0) {
          visit(c, 0, 0);
          flush(c);
          continue;
        }
        int q = tk.first;
        if (c.rx < 1 || c.it->wv[q] > c.wcap) continue;
        iterate(c, q + 1, 1u << q, c.it->wv[q], 1, c.it->kv[q]);
        flush(c);
      }
      std::lock_guard<std::mutex> g(mu);
      total.add(st);
    });
  for (auto& th : pool) th.join();
  auto t2 = std::chrono::steady_clock::now();
  double secs = std::chrono::duration<double>(t2 - t0).count();
  for (auto& s : SURVIVORS) fprintf(stderr, "SURVIVOR %s\n", s.c_str());
  printf("{\"K\": %d, \"largest_support_prime\": %" PRIu64 ", \"next_prime\": %" PRIu64
         ", \"max_removed\": %d, \"budget_lo_2^-64\": \"%s\", \"budget_hi_2^-64\": \"%s\""
         ", \"never_removable_odd_primes\": %d, \"key_coordinates\": %d, \"x_patterns\": %zu"
         ", \"table1\": %" PRIu64 ", \"table2\": %" PRIu64 ", \"iterated_nodes\": %" PRIu64
         ", \"bucket_visits\": %" PRIu64 ", \"scanned\": %" PRIu64
         ", \"key_matched_feasible\": %" PRIu64 ", \"ambiguous_budget\": %" PRIu64
         ", \"survivors\": %" PRIu64 ", \"key_matched_by_removed\": {",
         K, PR[K - 1], PR[K], MAXR, u128_dec(BLO).c_str(), u128_dec(BHI).c_str(), fixed_odd, CK,
         xs.size(), TAB1.size, TAB2.size, total.nodes, total.buckets, total.scanned,
         total.matched, total.ambiguous, total.survivors);
  bool first = true;
  for (int i = 0; i < 128; ++i)
    if (total.by_size[i]) {
      printf("%s\"%d\": %" PRIu64, first ? "" : ", ", i, total.by_size[i]);
      first = false;
    }
  printf("}, \"seconds\": %.1f}\n", secs);
  return total.survivors == 0 ? 0 : 3;
}
