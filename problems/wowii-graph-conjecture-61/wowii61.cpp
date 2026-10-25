// wowii61.cpp -- exhaustive checker for WOWII Graph Conjecture 61
//
//     f(G) >= r(G) + ceil(D(G)/3)     for every connected graph G,
//
// where f = order of a largest induced forest, r = Havel--Hakimi residue
// (exactly as `SimpleGraph.residue` in FormalConjecturesForMathlib:
// sort the degree sequence descending, repeatedly remove the head d,
// decrement the next d entries and re-sort, count the zeros left),
// D = diameter, alpha = independence number.  It also checks, on the same
// data, the inequalities used or proved informally in PROOF.md:
//   fms   : r <= alpha                      (basic inequality (1))
//   thm1  : f >= alpha + ceil(D/4)          (Theorem 1)
//   thm2a : f >= alpha + 1  (n >= 2)        (Theorem 2, first part)
//   thm2b : f == alpha + 1  implies D <= 4  (Theorem 2, second part)
// and counts internal anomalies: hh (a Havel--Hakimi step that would need
// truncated subtraction, impossible for graphic sequences), tree_f (a tree
// with f != n) and, with --crosscheck, the disagreements xf, xa, xd, xr
// between the fast and the brute-force computations of f, alpha, D, r.
//
// Build:  g++ -O3 -std=c++17 wowii61.cpp -o wowii61
// Input modes:
//   geng -cq N [res/mod] | ./wowii61       graph6 lines on stdin (default)
//   gentreeg -pq N | ./wowii61 --parent     parent arrays on stdin (trees)
//   ./wowii61 --labeled N                   every labeled graph on N <= 8
//                                           vertices (no nauty needed);
//                                           disconnected ones are skipped
// Options:
//   --crosscheck  recompute f, alpha, D, r with separate brute-force code
//                 (all 2^n vertex subsets, Floyd-Warshall, counting-array
//                 Havel--Hakimi) and count disagreements; needs n <= 20
//   --examples K  keep the K lexicographically smallest graph6 strings of
//                 each extremal class (default 5)
//   --dump FILE   write "g6 n m D f alpha r" for the sampled graphs
//   --dump-mod M  sample = graphs whose FNV-1a-64 hash of the graph6 string
//                 is 0 mod M (default 1 = every graph)
// Output (stdout): a line-based summary that can be merged across res/mod
// parts with wowii61_summary.py.  Lines:
//   GRAPHS total, DISCONNECTED skipped, N n count, TREES n count,
//   H n D (f-alpha) (alpha-r) count      joint histogram per (n, D),
//   CHECK n name count                   violation / disagreement counters,
//   EX_SLACK n D s g6                    examples at min slack for (n, D),
//   EX_FA n D k g6                       examples at min f-alpha for (n, D).
// slack s = f - r - ceil(D/3) = (f-alpha) + (alpha-r) - ceil(D/3).

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <set>
#include <string>
#include <tuple>
#include <vector>

typedef uint64_t mask;
static const int MAXN = 64;

static inline int popc(mask x) { return __builtin_popcountll(x); }
static inline int ctz(mask x) { return __builtin_ctzll(x); }
static inline mask bit(int v) { return (mask)1 << v; }
static inline mask allmask(int n) { return n >= 64 ? ~(mask)0 : bit(n) - 1; }

struct Graph {
  int n = 0;
  mask adj[MAXN];
};

// ---------------------------------------------------------------- diameter
// Bitmask BFS from every vertex; returns -1 if the graph is disconnected.
static int diameter(const Graph& g) {
  const mask all = allmask(g.n);
  int D = 0;
  for (int s = 0; s < g.n; ++s) {
    mask reach = bit(s), frontier = reach;
    int e = 0;
    while (reach != all) {
      mask nxt = 0;
      for (mask t = frontier; t; t &= t - 1) nxt |= g.adj[ctz(t)];
      nxt &= ~reach;
      if (!nxt) return -1;
      reach |= nxt;
      frontier = nxt;
      ++e;
    }
    if (e > D) D = e;
  }
  return D;
}

// ---------------------------------------------------- independence number
// Branching on vertex sets; a vertex of degree <= 1 in G[P] lies in some
// maximum independent set of G[P], so it is taken without branching.
static int mis(const mask* adj, mask P) {
  if (!P) return 0;
  int vmin = -1, dmin = MAXN + 1, vmax = -1, dmax = -1;
  for (mask t = P; t; t &= t - 1) {
    int v = ctz(t);
    int d = popc(adj[v] & P);
    if (d < dmin) { dmin = d; vmin = v; }
    if (d > dmax) { dmax = d; vmax = v; }
  }
  if (dmin <= 1) return 1 + mis(adj, P & ~(adj[vmin] | bit(vmin)));
  int a = mis(adj, P & ~bit(vmax));
  int b = 1 + mis(adj, P & ~(adj[vmax] | bit(vmax)));
  return a > b ? a : b;
}

// ------------------------------------------------- largest induced forest
// Branch and bound.  State: the chosen vertices S (kept as the list of the
// components of G[S]) and the set R of undecided vertices that can still be
// added, i.e. that have at most one neighbour in every component of G[S]
// (components only grow, so a vertex with two neighbours in one component
// can never be added later).  Bound: |S| + |R|.  A vertex of R with at most
// one neighbour in S u R is added without branching (it is a leaf or an
// isolated vertex of every forest it is added to, so adding it never hurts).
// Otherwise branch on a vertex v of R of maximum degree in G[S u R]: first
// discard v, then add v (merge the components it touches and drop the
// vertices of R that now have two neighbours in the merged component).
struct ForestBB {
  const mask* adj;
  int best;
  bool found;
  void dfs(int sz, mask S, mask R, const mask* comps_in, int nc) {
    mask comps[MAXN];
    for (int c = 0; c < nc; ++c) comps[c] = comps_in[c];
    int v;
    for (;;) {
      if (sz + popc(R) <= best) return;
      if (!R) { best = sz; found = true; return; }
      const mask SR = S | R;
      int u = -1, dv = -1;
      v = -1;
      for (mask t = R; t; t &= t - 1) {
        int w = ctz(t), d = popc(adj[w] & SR);
        if (d <= 1) { u = w; break; }
        if (d > dv) { dv = d; v = w; }
      }
      if (u < 0) break;
      // free vertex u: its only possible neighbour lies in S (join that
      // component) or in R (start a new component)
      mask nb = adj[u] & S;
      int c = 0;
      if (nb) while (!(comps[c] & nb)) ++c;
      if (nb) comps[c] |= bit(u); else comps[nc++] = bit(u);
      S |= bit(u);
      R &= ~bit(u);
      ++sz;
    }
    // first exclude v
    dfs(sz, S, R & ~bit(v), comps, nc);
    // then include v (every vertex of R is addable by the invariant)
    mask nxt[MAXN];
    int nn = 0;
    mask merged = bit(v);
    for (int c = 0; c < nc; ++c) {
      if (adj[v] & comps[c]) merged |= comps[c];
      else nxt[nn++] = comps[c];
    }
    nxt[nn++] = merged;
    mask R2 = R & ~bit(v);
    for (mask t = R2; t; t &= t - 1) {
      int w = ctz(t);
      mask x = adj[w] & merged;
      if (x & (x - 1)) R2 &= ~bit(w);
    }
    dfs(sz + 1, S | bit(v), R2, nxt, nn);
  }
};

// The search only reports sizes of forests it actually constructs.  The
// argument `lower` is used for pruning only (pass alpha): if no forest with
// more than `lower` vertices is found, the search is redone from 0, so the
// result is exact without assuming f >= alpha + 1.
static int max_induced_forest(const Graph& g, int lower) {
  ForestBB bb;
  bb.adj = g.adj;
  bb.best = lower;
  bb.found = false;
  bb.dfs(0, 0, allmask(g.n), nullptr, 0);
  if (!bb.found) {
    bb.best = 0;
    bb.dfs(0, 0, allmask(g.n), nullptr, 0);
  }
  return bb.best;
}

// ------------------------------------------------- Havel--Hakimi residue
// Literal transcription of `havelHakimiStep` / `residueAux`; `anomaly` is
// set if a step would need truncated subtraction (d > rest length or a
// zero entry decremented), which never happens for graphic sequences.
static int residue(const Graph& g, bool& anomaly) {
  int s[MAXN];
  int len = g.n;
  for (int v = 0; v < g.n; ++v) s[v] = popc(g.adj[v]);
  std::sort(s, s + len, [](int a, int b) { return a > b; });
  while (len > 0 && s[0] > 0) {
    int d = s[0];
    int rest = len - 1;
    if (d > rest) { anomaly = true; d = rest; }
    for (int k = 1; k <= d; ++k) {
      if (s[k] == 0) anomaly = true; else --s[k];
    }
    // s[1..d] and s[d+1..rest] are both non-increasing: merge them
    int t[MAXN], i = 1, j = d + 1, k = 0;
    while (i <= d && j <= rest) t[k++] = (s[i] >= s[j]) ? s[i++] : s[j++];
    while (i <= d) t[k++] = s[i++];
    while (j <= rest) t[k++] = s[j++];
    for (k = 0; k < rest; ++k) s[k] = t[k];
    len = rest;
  }
  return len;  // [] -> 0, (0 :: t) -> 1 + length t
}

// ------------------------------------------------ brute-force crosscheck
static int f_brute(const Graph& g) {
  int best = 0;
  const mask lim = bit(g.n);
  for (mask S = 1; S < lim; ++S) {
    int k = popc(S);
    if (k <= best) continue;
    int e2 = 0;
    for (mask t = S; t; t &= t - 1) e2 += popc(g.adj[ctz(t)] & S);
    int comp = 0;
    mask rem = S;
    while (rem) {
      mask r = rem & (~rem + 1), fr = r;
      while (fr) {
        mask nx = 0;
        for (mask t = fr; t; t &= t - 1) nx |= g.adj[ctz(t)];
        nx &= S & ~r;
        r |= nx;
        fr = nx;
      }
      rem &= ~r;
      ++comp;
    }
    if (e2 / 2 == k - comp) best = k;  // acyclic iff |E| = |V| - #components
  }
  return best;
}

static int alpha_brute(const Graph& g) {
  int best = 0;
  const mask lim = bit(g.n);
  for (mask S = 0; S < lim; ++S) {
    int k = popc(S);
    if (k <= best) continue;
    bool ind = true;
    for (mask t = S; t && ind; t &= t - 1)
      if (g.adj[ctz(t)] & S) ind = false;
    if (ind) best = k;
  }
  return best;
}

static int diameter_brute(const Graph& g) {
  const int INF = 1000;
  int d[MAXN][MAXN];
  for (int i = 0; i < g.n; ++i)
    for (int j = 0; j < g.n; ++j)
      d[i][j] = (i == j) ? 0 : ((g.adj[i] >> j) & 1) ? 1 : INF;
  for (int k = 0; k < g.n; ++k)
    for (int i = 0; i < g.n; ++i)
      for (int j = 0; j < g.n; ++j)
        if (d[i][k] + d[k][j] < d[i][j]) d[i][j] = d[i][k] + d[k][j];
  int D = 0;
  for (int i = 0; i < g.n; ++i)
    for (int j = 0; j < g.n; ++j) {
      if (d[i][j] >= INF) return -1;
      if (d[i][j] > D) D = d[i][j];
    }
  return D;
}

// Havel--Hakimi on the multiset of degrees stored as a count array.
static int residue_brute(const Graph& g) {
  int cnt[MAXN + 1] = {0}, nw[MAXN + 1];
  int total = g.n;
  for (int v = 0; v < g.n; ++v) cnt[popc(g.adj[v])]++;
  while (total > 0) {
    int d = g.n;
    while (d > 0 && cnt[d] == 0) --d;
    if (d == 0) return cnt[0];
    cnt[d]--;
    total--;
    std::memcpy(nw, cnt, sizeof cnt);
    int need = d;
    for (int v = g.n; v >= 1 && need > 0; --v) {
      int take = std::min(cnt[v], need);
      nw[v] -= take;
      nw[v - 1] += take;
      need -= take;
    }
    if (need > 0) return -1;  // not graphic (cannot happen)
    std::memcpy(cnt, nw, sizeof cnt);
  }
  return 0;
}

// ---------------------------------------------------------------- graph6
static bool parse_graph6(const char* s, size_t len, Graph& g) {
  if (len < 1 || s[0] < 63 || s[0] > 125) return false;
  int n = s[0] - 63;
  if (n > MAXN) return false;
  g.n = n;
  for (int i = 0; i < n; ++i) g.adj[i] = 0;
  size_t need = 1 + ((size_t)n * (n - 1) / 2 + 5) / 6;
  if (len < need) return false;
  size_t k = 0;
  for (int j = 1; j < n; ++j)
    for (int i = 0; i < j; ++i, ++k) {
      int c = s[1 + k / 6] - 63;
      if ((c >> (5 - (int)(k % 6))) & 1) {
        g.adj[i] |= bit(j);
        g.adj[j] |= bit(i);
      }
    }
  return true;
}

static std::string to_graph6(const Graph& g) {
  std::string out(1, (char)(63 + g.n));
  int acc = 0, nb = 0;
  for (int j = 1; j < g.n; ++j)
    for (int i = 0; i < j; ++i) {
      acc = (acc << 1) | (int)((g.adj[i] >> j) & 1);
      if (++nb == 6) { out += (char)(63 + acc); acc = 0; nb = 0; }
    }
  if (nb) out += (char)(63 + (acc << (6 - nb)));
  return out;
}

static uint64_t fnv1a(const std::string& s) {
  uint64_t h = 1469598103934665603ULL;
  for (unsigned char c : s) { h ^= c; h *= 1099511628211ULL; }
  return h;
}

// ----------------------------------------------------------- statistics
static const char* CHECK_NAMES[] = {"conj", "thm1", "thm2a", "thm2b", "fms",
                                    "hh",   "tree_f", "xf", "xa", "xd", "xr"};
static const int NCHECK = 11;

struct Stats {
  int K = 5;
  bool crosscheck = false;
  uint64_t graphs = 0, disconnected = 0;
  std::map<int, uint64_t> count, trees;
  std::map<std::tuple<int, int, int, int>, uint64_t> hist;
  std::map<int, std::vector<uint64_t>> checks;
  // (n, D) -> (min value, K smallest graph6 strings at that value)
  std::map<std::pair<int, int>, std::pair<int, std::set<std::string>>> exs, exfa;
  FILE* dump = nullptr;
  uint64_t dump_mod = 1;

  static void offer(std::map<std::pair<int, int>, std::pair<int, std::set<std::string>>>& m,
                    int n, int D, int val, const std::string& g6, int K) {
    auto key = std::make_pair(n, D);
    auto it = m.find(key);
    if (it == m.end()) {
      m[key] = {val, {g6}};
      return;
    }
    auto& e = it->second;
    if (val < e.first) {
      e.first = val;
      e.second.clear();
      e.second.insert(g6);
    } else if (val == e.first) {
      if ((int)e.second.size() < K) {
        e.second.insert(g6);
      } else if (g6 < *e.second.rbegin()) {
        e.second.insert(g6);
        if ((int)e.second.size() > K) e.second.erase(std::prev(e.second.end()));
      }
    }
  }
  static bool wants(const std::map<std::pair<int, int>, std::pair<int, std::set<std::string>>>& m,
                    int n, int D, int val) {
    auto it = m.find({n, D});
    return it == m.end() || val <= it->second.first;
  }

  void process(const Graph& g, const std::string* g6in) {
    ++graphs;
    const int n = g.n;
    int D = diameter(g);
    if (D < 0) { ++disconnected; return; }
    auto& ck = checks[n];
    if (ck.empty()) ck.assign(NCHECK, 0);
    int m2 = 0;
    for (int v = 0; v < n; ++v) m2 += popc(g.adj[v]);
    const int m = m2 / 2;
    const int alpha = mis(g.adj, allmask(n));
    const int f = max_induced_forest(g, alpha);
    bool anomaly = false;
    const int r = residue(g, anomaly);
    const int c3 = (D + 2) / 3, c4 = (D + 3) / 4;
    const int slack = f - r - c3;
    count[n]++;
    const bool tree = (m == n - 1);
    if (tree) trees[n]++;
    hist[std::make_tuple(n, D, f - alpha, alpha - r)]++;
    if (slack < 0) ck[0]++;
    if (f < alpha + c4) ck[1]++;
    if (n >= 2 && f < alpha + 1) ck[2]++;
    if (f == alpha + 1 && D > 4) ck[3]++;
    if (r > alpha) ck[4]++;
    if (anomaly) ck[5]++;
    if (tree && f != n) ck[6]++;
    if (crosscheck) {
      if (f_brute(g) != f) ck[7]++;
      if (alpha_brute(g) != alpha) ck[8]++;
      if (diameter_brute(g) != D) ck[9]++;
      if (residue_brute(g) != r) ck[10]++;
    }
    const bool ws = wants(exs, n, D, slack), wf = wants(exfa, n, D, f - alpha);
    std::string g6local;
    const std::string* g6 = g6in;
    if (!g6 && (ws || wf || dump)) { g6local = to_graph6(g); g6 = &g6local; }
    if (ws) offer(exs, n, D, slack, *g6, K);
    if (wf) offer(exfa, n, D, f - alpha, *g6, K);
    if (dump && fnv1a(*g6) % dump_mod == 0)
      fprintf(dump, "%s %d %d %d %d %d %d\n", g6->c_str(), n, m, D, f, alpha, r);
  }

  void print() const {
    printf("WOWII61-SUMMARY v1\n");
    printf("CROSSCHECK %d\n", crosscheck ? 1 : 0);
    printf("GRAPHS %llu\n", (unsigned long long)graphs);
    printf("DISCONNECTED %llu\n", (unsigned long long)disconnected);
    for (auto& [n, c] : count) printf("N %d %llu\n", n, (unsigned long long)c);
    for (auto& [n, c] : trees) printf("TREES %d %llu\n", n, (unsigned long long)c);
    for (auto& [k, c] : hist)
      printf("H %d %d %d %d %llu\n", std::get<0>(k), std::get<1>(k), std::get<2>(k),
             std::get<3>(k), (unsigned long long)c);
    for (auto& [n, v] : checks)
      for (int i = 0; i < NCHECK; ++i)
        printf("CHECK %d %s %llu\n", n, CHECK_NAMES[i], (unsigned long long)v[i]);
    for (auto& [k, e] : exs)
      for (auto& s : e.second) printf("EX_SLACK %d %d %d %s\n", k.first, k.second, e.first, s.c_str());
    for (auto& [k, e] : exfa)
      for (auto& s : e.second) printf("EX_FA %d %d %d %s\n", k.first, k.second, e.first, s.c_str());
  }
};

// ------------------------------------------------------------ input modes
static void run_graph6_stdin(Stats& st, bool parent) {
  static char buf[1 << 16];
  std::string line;
  Graph g;
  while (fgets(buf, sizeof buf, stdin)) {
    size_t len = strlen(buf);
    while (len && (buf[len - 1] == '\n' || buf[len - 1] == '\r')) buf[--len] = 0;
    if (!len || buf[0] == '>') continue;
    if (!parent) {
      if (!parse_graph6(buf, len, g)) {
        fprintf(stderr, "bad graph6 line: %s\n", buf);
        exit(2);
      }
      line.assign(buf, len);
      st.process(g, &line);
    } else {
      // gentreeg -p: parent of vertex 1..n (1-based), 0 for the root
      std::vector<int> par;
      char* p = buf;
      while (*p) {
        char* e;
        long x = strtol(p, &e, 10);
        if (e == p) break;
        par.push_back((int)x);
        p = e;
      }
      if (par.empty() || (int)par.size() > MAXN) {
        fprintf(stderr, "bad parent line: %s\n", buf);
        exit(2);
      }
      g.n = (int)par.size();
      for (int i = 0; i < g.n; ++i) g.adj[i] = 0;
      for (int i = 0; i < g.n; ++i)
        if (par[i] > 0) {
          int u = i, w = par[i] - 1;
          g.adj[u] |= bit(w);
          g.adj[w] |= bit(u);
        }
      st.process(g, nullptr);
    }
  }
}

static void run_labeled(Stats& st, int n) {
  if (n < 1 || n > 8) {
    fprintf(stderr, "--labeled needs 1 <= N <= 8\n");
    exit(2);
  }
  const int E = n * (n - 1) / 2;
  std::vector<std::pair<int, int>> pairs;  // graph6 bit order
  for (int j = 1; j < n; ++j)
    for (int i = 0; i < j; ++i) pairs.push_back({i, j});
  Graph g;
  g.n = n;
  for (uint64_t e = 0; e < ((uint64_t)1 << E); ++e) {
    for (int i = 0; i < n; ++i) g.adj[i] = 0;
    for (int k = 0; k < E; ++k)
      if ((e >> k) & 1) {
        g.adj[pairs[k].first] |= bit(pairs[k].second);
        g.adj[pairs[k].second] |= bit(pairs[k].first);
      }
    st.process(g, nullptr);
  }
}

int main(int argc, char** argv) {
  Stats st;
  bool parent = false;
  int labeled = 0;
  const char* dumpfile = nullptr;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    if (a == "--crosscheck") st.crosscheck = true;
    else if (a == "--parent") parent = true;
    else if (a == "--labeled" && i + 1 < argc) labeled = atoi(argv[++i]);
    else if (a == "--examples" && i + 1 < argc) st.K = atoi(argv[++i]);
    else if (a == "--dump" && i + 1 < argc) dumpfile = argv[++i];
    else if (a == "--dump-mod" && i + 1 < argc) st.dump_mod = strtoull(argv[++i], nullptr, 10);
    else {
      fprintf(stderr, "unknown argument %s\n", argv[i]);
      return 2;
    }
  }
  if (dumpfile) {
    st.dump = fopen(dumpfile, "w");
    if (!st.dump) { perror(dumpfile); return 2; }
  }
  if (labeled) run_labeled(st, labeled);
  else run_graph6_stdin(st, parent);
  if (st.crosscheck)
    for (auto& [n, c] : st.count)
      if (n > 20) { fprintf(stderr, "--crosscheck needs n <= 20\n"); return 2; }
  st.print();
  if (st.dump) fclose(st.dump);
  return 0;
}
