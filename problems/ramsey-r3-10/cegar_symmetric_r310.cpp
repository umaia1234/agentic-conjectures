// SAT+CEGAR back end for symmetric (3,10)-graphs on 40 vertices.
//
// Input: an instance file written by `search_symmetric_r310.py instance`:
//   line 1: N V T R      (N = 40 vertices, V edge-orbit variables,
//                         T triangle clauses, R vertex-orbit representatives)
//   line 2: R representatives
//   line 3: N(N-1)/2 variables, one per pair (u,v), u<v, in lexicographic order
//   then T triangle clauses in DIMACS literal form (terminated by 0).
//
// Loop: CaDiCaL proposes a triangle-free orbit graph; a branch-and-bound
// search looks for independent 10-sets whose clause (the set of edge orbits
// of its 45 pairs) is short; up to K distinct such clauses are added.  If the
// graph has no independent 10-set it is a genuine (3,10)-graph on 40 vertices
// and the model is written out (SAT).  UNSAT exhausts the symmetry class.
//
// Every separator is written as one line of ten comma-separated vertices, so
// the final formula can be rebuilt and audited independently.
//
// Build: c++ -O3 -std=c++17 cegar_symmetric_r310.cpp -lcadical
//        (with -I/-L pointing at a CaDiCaL installation)

#include <cadical.hpp>

#include <algorithm>
#include <chrono>
#include <climits>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <functional>
#include <random>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

typedef uint64_t u64;
static const int N = 40;
static const int T = 10;
static const u64 ALL = (1ULL << N) - 1;

static int V;
static int pv[N][N];
static std::vector<int> reps;
static std::vector<std::vector<int>> triClauses;

static inline int popc(u64 x) { return __builtin_popcountll(x); }
static inline int ctz(u64 x) { return __builtin_ctzll(x); }

// Greedy maximal matching inside P; an independent set meets every matching
// edge at most once, so alpha(G[P]) <= |P| - |matching| for any graph.
static inline int greedyMatching(const u64 *adj, u64 P) {
  int m = 0;
  while (P) {
    int v = ctz(P);
    P &= P - 1;
    u64 nb = adj[v] & P;
    if (nb) {
      P &= ~(1ULL << ctz(nb));
      m++;
    }
  }
  return m;
}

struct Sol {
  int cost;
  int verts[T];
  std::vector<int> clause;
};

struct Searcher {
  const u64 *adj = nullptr;
  int chosen[T];
  int depth = 0;
  std::vector<uint8_t> used;
  std::vector<int> mark;
  int stamp = 0;
  int cost = 0;
  long long nodes = 0, nodeLimit = 0;
  bool hitLimit = false;
  size_t K = 1;
  std::vector<Sol> best;

  int bound() const {
    return best.size() < K ? INT_MAX : best.back().cost;
  }

  void record() {
    Sol s;
    s.cost = cost;
    for (int i = 0; i < T; i++) s.verts[i] = chosen[i];
    std::sort(s.verts, s.verts + T);
    for (int i = 0; i < T; i++)
      for (int j = i + 1; j < T; j++) s.clause.push_back(pv[s.verts[i]][s.verts[j]]);
    std::sort(s.clause.begin(), s.clause.end());
    s.clause.erase(std::unique(s.clause.begin(), s.clause.end()), s.clause.end());
    if ((int)s.clause.size() != cost) {
      fprintf(stderr, "internal cost mismatch\n");
      exit(3);
    }
    for (auto &b : best)
      if (b.clause == s.clause) return;
    best.push_back(s);
    std::sort(best.begin(), best.end(),
              [](const Sol &a, const Sol &b) { return a.cost < b.cost; });
    if (best.size() > K) best.pop_back();
  }

  void rec(u64 P) {
    if (++nodes > nodeLimit) {
      hitLimit = true;
      return;
    }
    if (depth == T) {
      record();
      return;
    }
    int need = T - depth;
    if (popc(P) < need) return;
    if (popc(P) - greedyMatching(adj, P) < need) return;
    if (cost >= bound()) return;
    // order candidates by incremental clause growth
    int cand[N], inc[N], nc = 0;
    u64 Q = P;
    while (Q) {
      int v = ctz(Q);
      Q &= Q - 1;
      stamp++;
      int c = 0;
      for (int i = 0; i < depth; i++) {
        int x = pv[v][chosen[i]];
        if (!used[x] && mark[x] != stamp) {
          mark[x] = stamp;
          c++;
        }
      }
      cand[nc] = v;
      inc[nc] = c;
      nc++;
    }
    int order[N];
    for (int i = 0; i < nc; i++) order[i] = i;
    std::stable_sort(order, order + nc, [&](int a, int b) { return inc[a] < inc[b]; });
    u64 rest = P;
    for (int oi = 0; oi < nc; oi++) {
      int v = cand[order[oi]];
      if (popc(rest) < need) break;
      if (cost + inc[order[oi]] < bound()) {
        int added[T * T];
        int na = 0;
        for (int i = 0; i < depth; i++) {
          int x = pv[v][chosen[i]];
          if (!used[x]) {
            used[x] = 1;
            added[na++] = x;
          }
        }
        cost += na;
        chosen[depth++] = v;
        rec(rest & ~adj[v] & ~(1ULL << v));
        depth--;
        cost -= na;
        for (int i = 0; i < na; i++) used[added[i]] = 0;
        if (hitLimit) return;
      }
      rest &= ~(1ULL << v);
    }
  }

  // Search from every root representative with a per-root node budget.
  void run(const u64 *a, size_t k, long long perRoot) {
    adj = a;
    K = k;
    best.clear();
    used.assign(V + 1, 0);
    mark.assign(V + 1, 0);
    for (int r : reps) {
      nodes = 0;
      nodeLimit = perRoot;
      hitLimit = false;
      depth = 1;
      chosen[0] = r;
      cost = 0;
      rec(ALL & ~adj[r] & ~(1ULL << r));
    }
  }
};

// Exact test: does G have an independent set of size T?  Returns one or empty.
static bool exactIndep(const u64 *adj, u64 P, int depth, int *chosen) {
  if (depth == T) return true;
  int need = T - depth;
  if (popc(P) < need) return false;
  if (popc(P) - greedyMatching(adj, P) < need) return false;
  u64 rest = P;
  while (rest) {
    if (popc(rest) < need) return false;
    int v = ctz(rest);
    rest &= rest - 1;
    chosen[depth] = v;
    if (exactIndep(adj, rest & ~adj[v], depth + 1, chosen)) return true;
  }
  return false;
}

static void readInstance(const char *path) {
  std::ifstream in(path);
  if (!in) {
    fprintf(stderr, "cannot open %s\n", path);
    exit(1);
  }
  int n, t, r;
  in >> n >> V >> t >> r;
  if (n != N) {
    fprintf(stderr, "expected N=40\n");
    exit(1);
  }
  reps.resize(r);
  for (int i = 0; i < r; i++) in >> reps[i];
  for (int u = 0; u < N; u++)
    for (int v = u + 1; v < N; v++) {
      int x;
      in >> x;
      pv[u][v] = pv[v][u] = x;
    }
  for (int u = 0; u < N; u++) pv[u][u] = 0;
  triClauses.resize(t);
  for (int i = 0; i < t; i++) {
    int lit;
    while (in >> lit && lit) triClauses[i].push_back(lit);
  }
}

static std::vector<int> clauseOf(const int *verts) {
  std::vector<int> c;
  for (int i = 0; i < T; i++)
    for (int j = i + 1; j < T; j++) c.push_back(pv[verts[i]][verts[j]]);
  std::sort(c.begin(), c.end());
  c.erase(std::unique(c.begin(), c.end()), c.end());
  return c;
}

// IPASIR-UP propagator.  It tracks which edge orbits are currently assigned
// false; whenever the pairs assigned false contain a 10-clique (a 10-set
// that is already forced to be independent), the corresponding 10-set clause
// is handed to the solver as an external clause (it is falsified, so the
// solver backtracks).  Complete models are checked exactly, so the search
// stays complete.  Every external clause is a genuine 10-set clause and is
// recorded through `emit`, so the final CNF can be rebuilt and audited.
struct IndepProp : CaDiCaL::ExternalPropagator {
  std::vector<int8_t> val;
  std::vector<int> trail;
  std::vector<size_t> levels;
  std::vector<std::vector<std::pair<int, int>>> pairsOf;
  u64 NE[N];
  std::vector<std::vector<int>> pending;
  size_t pendPos = 0;
  bool dirty = false;
  long long perRoot;
  std::function<bool(int *)> emit; // records a separator, false if known
  Searcher se;
  long long searches = 0, conflicts = 0, modelChecks = 0;
  bool foundGraph = false;
  std::vector<int> graphModel;

  IndepProp(long long nodes) : perRoot(nodes) {
    val.assign(V + 1, 0);
    pairsOf.assign(V + 1, {});
    for (int u = 0; u < N; u++)
      for (int v = u + 1; v < N; v++) pairsOf[pv[u][v]].push_back({u, v});
    for (int v = 0; v < N; v++) NE[v] = 0;
  }
  void setFalse(int x, bool on) {
    for (auto &pr : pairsOf[x]) {
      if (on) {
        NE[pr.first] |= 1ULL << pr.second;
        NE[pr.second] |= 1ULL << pr.first;
      } else {
        NE[pr.first] &= ~(1ULL << pr.second);
        NE[pr.second] &= ~(1ULL << pr.first);
      }
    }
  }
  void notify_assignment(const std::vector<int> &lits) override {
    for (int lit : lits) {
      int x = abs(lit);
      if (val[x]) continue;
      val[x] = lit > 0 ? 1 : -1;
      trail.push_back(x);
      if (lit < 0) {
        setFalse(x, true);
        dirty = true;
      }
    }
  }
  void notify_new_decision_level() override { levels.push_back(trail.size()); }
  void notify_backtrack(size_t new_level) override {
    size_t keep = levels[new_level];
    while (trail.size() > keep) {
      int x = trail.back();
      trail.pop_back();
      if (val[x] < 0) setFalse(x, false);
      val[x] = 0;
    }
    levels.resize(new_level);
  }
  bool queue(Sol &s) {
    if (!emit(s.verts)) return false;
    pending.push_back(s.clause);
    return true;
  }
  bool cb_check_found_model(const std::vector<int> &model) override {
    modelChecks++;
    std::vector<int> m(V + 1, 0);
    for (int lit : model)
      if (abs(lit) <= V) m[abs(lit)] = lit > 0;
    u64 adj[N] = {0};
    for (int u = 0; u < N; u++)
      for (int v = u + 1; v < N; v++)
        if (m[pv[u][v]]) {
          adj[u] |= 1ULL << v;
          adj[v] |= 1ULL << u;
        }
    for (int u = 0; u < N; u++)
      for (int v = u + 1; v < N; v++)
        if (((adj[u] >> v) & 1) && (adj[u] & adj[v])) {
          fprintf(stderr, "model has a triangle: encoding bug\n");
          exit(3);
        }
    se.run(adj, 1, perRoot);
    if (!se.best.empty()) {
      if (!queue(se.best[0])) {
        fprintf(stderr, "model separator already known\n");
        exit(3);
      }
      return false;
    }
    int chosen[T];
    for (int r : reps) {
      chosen[0] = r;
      if (exactIndep(adj, ALL & ~adj[r] & ~(1ULL << r), 1, chosen)) {
        Sol s;
        for (int i = 0; i < T; i++) s.verts[i] = chosen[i];
        std::sort(s.verts, s.verts + T);
        s.clause = clauseOf(s.verts);
        s.cost = s.clause.size();
        queue(s);
        return false;
      }
    }
    foundGraph = true;
    graphModel = m;
    return true;
  }
  bool cb_has_external_clause(bool &forgettable) override {
    forgettable = false;
    if (!pending.empty()) return true;
    if (!dirty) return false;
    dirty = false;
    searches++;
    u64 notF[N];
    for (int v = 0; v < N; v++) notF[v] = ALL & ~NE[v] & ~(1ULL << v);
    se.run(notF, 1, perRoot);
    if (se.best.empty()) return false;
    if (!queue(se.best[0])) return false;
    conflicts++;
    return true;
  }
  int cb_add_external_clause_lit() override {
    std::vector<int> &c = pending.front();
    if (pendPos < c.size()) return c[pendPos++];
    pending.erase(pending.begin());
    pendPos = 0;
    return 0;
  }
};

// Sequential-counter "at most 9" over a literal multiset, every clause
// guarded by -act.  Only used to steer the search (phase 1); it is never part
// of the final certificate, which is re-derived without it.
static int addDegreeConstraint(CaDiCaL::Solver &S, const std::vector<int> &x, int act,
                               int nextVar) {
  const int k = 9;
  int n = x.size();
  std::vector<std::vector<int>> s(n, std::vector<int>(k + 1, 0));
  for (int i = 0; i < n - 1; i++)
    for (int j = 1; j <= k; j++) s[i][j] = nextVar++;
  S.clause(-act, -x[0], s[0][1]);
  for (int j = 2; j <= k; j++) S.clause(-act, -s[0][j]);
  for (int i = 1; i < n - 1; i++) {
    S.clause(-act, -x[i], s[i][1]);
    S.clause(-act, -s[i - 1][1], s[i][1]);
    for (int j = 2; j <= k; j++) {
      S.clause({-act, -x[i], -s[i - 1][j - 1], s[i][j]});
      S.clause(-act, -s[i - 1][j], s[i][j]);
    }
    S.clause(-act, -x[i], -s[i - 1][k]);
  }
  S.clause(-act, -x[n - 1], -s[n - 2][k]);
  return nextVar;
}

static std::string key(const std::vector<int> &c) {
  return std::string((const char *)c.data(), c.size() * sizeof(int));
}

int main(int argc, char **argv) {
  const char *inst = nullptr, *out = nullptr, *init = nullptr, *modelOut = nullptr;
  const char *symFile = nullptr, *config = nullptr, *extraFile = nullptr;
  std::vector<std::pair<std::string, int>> opts;
  size_t K = 1;
  long long perRoot = 20000;
  int seed = 0;
  long long logEvery = 1000;
  double timeLimit = 1e18;
  bool degree = false, up = false;
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    auto next = [&]() { return argv[++i]; };
    if (a == "--instance") inst = next();
    else if (a == "--out") out = next();
    else if (a == "--init") init = next();
    else if (a == "--model-out") modelOut = next();
    else if (a == "--sym") symFile = next();
    else if (a == "--extra") extraFile = next();
    else if (a == "--config") config = next();
    else if (a == "--opt") {
      std::string o = next();
      size_t eq = o.find('=');
      opts.push_back({o.substr(0, eq), atoi(o.substr(eq + 1).c_str())});
    } else if (a == "--k") K = atol(next());
    else if (a == "--nodes") perRoot = atoll(next());
    else if (a == "--seed") seed = atoi(next());
    else if (a == "--log-every") logEvery = atoll(next());
    else if (a == "--time-limit") timeLimit = atof(next());
    else if (a == "--degree") degree = true;
    else if (a == "--up") up = true;
    else {
      fprintf(stderr, "unknown option %s\n", a.c_str());
      return 1;
    }
  }
  if (!inst || !out) {
    fprintf(stderr, "usage: --instance F --out SEPS [--init SEPS] [--k K] [--nodes N]\n");
    return 1;
  }
  readInstance(inst);
  std::vector<std::vector<int>> syms;
  if (symFile) {
    std::ifstream in(symFile);
    int P;
    in >> P;
    syms.assign(P, std::vector<int>(N));
    for (int p = 0; p < P; p++)
      for (int v = 0; v < N; v++) in >> syms[p][v];
  }
  auto t0 = std::chrono::steady_clock::now();
  auto elapsed = [&]() {
    return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  };

  CaDiCaL::Solver S;
  if (config) S.configure(config);
  S.set("seed", seed);
  for (auto &o : opts)
    if (!S.set(o.first.c_str(), o.second)) {
      fprintf(stderr, "bad option %s\n", o.first.c_str());
      return 1;
    }
  for (auto &c : triClauses) S.clause(c);
  if (extraFile) {
    // extra clauses (e.g. symmetry-breaking normalisation), DIMACS literals
    std::ifstream in(extraFile);
    std::vector<int> c;
    int lit, count = 0;
    while (in >> lit) {
      if (lit) {
        if (abs(lit) > V) {
          fprintf(stderr, "extra clause literal out of range\n");
          return 1;
        }
        c.push_back(lit);
      } else {
        S.clause(c);
        c.clear();
        count++;
      }
    }
    fprintf(stderr, "added %d extra clauses\n", count);
  }
  int act = 0;
  if (degree) {
    act = V + 1;
    int nextVar = V + 2;
    for (int r : reps) {
      std::vector<int> lits;
      for (int w = 0; w < N; w++)
        if (w != r) lits.push_back(pv[r][w]);
      nextVar = addDegreeConstraint(S, lits, act, nextVar);
    }
  }

  FILE *fo = fopen(out, "w");
  long long nsep = 0;
  std::unordered_set<std::string> known;
  auto addSeparator = [&](int *verts) -> bool {
    std::sort(verts, verts + T);
    std::vector<int> c = clauseOf(verts);
    if (!known.insert(key(c)).second) return false;
    S.clause(c);
    for (int i = 0; i < T; i++) fprintf(fo, i ? ",%d" : "%d", verts[i]);
    fprintf(fo, "\n");
    nsep++;
    return true;
  };
  // propagator mode: the solver adds the clause itself (external clause)
  auto addSeparatorRecordOnly = [&](int *verts) -> bool {
    std::sort(verts, verts + T);
    std::vector<int> c = clauseOf(verts);
    if (!known.insert(key(c)).second) return false;
    for (int i = 0; i < T; i++) fprintf(fo, i ? ",%d" : "%d", verts[i]);
    fprintf(fo, "\n");
    nsep++;
    if (logEvery && nsep % logEvery == 0) {
      fflush(fo);
      fprintf(stderr, "seps %lld elapsed %.1f\n", nsep, elapsed());
    }
    return true;
  };
  if (init) {
    std::ifstream in(init);
    std::string line;
    while (std::getline(in, line)) {
      if (line.empty()) continue;
      int verts[T];
      std::stringstream ss(line);
      std::string tok;
      int k = 0;
      while (std::getline(ss, tok, ',')) verts[k++] = atoi(tok.c_str());
      if (k != T) {
        fprintf(stderr, "bad init line\n");
        return 1;
      }
      addSeparator(verts);
    }
    fflush(fo);
  }

  if (up) {
    IndepProp prop(perRoot);
    prop.emit = [&](int *verts) { return addSeparatorRecordOnly(verts); };
    S.connect_external_propagator(&prop);
    for (int x = 1; x <= V; x++) S.add_observed_var(x);
    int res = S.solve();
    fclose(fo);
    printf("{\"status\": \"%s\", \"mode\": \"ipasir-up\", \"separators\": %lld, "
           "\"searches\": %lld, \"conflict_clauses\": %lld, \"model_checks\": %lld, "
           "\"elapsed\": %.2f, \"nodes_per_root\": %lld}\n",
           res == 20 ? "UNSAT" : res == 10 ? "SAT" : "UNKNOWN", nsep, prop.searches,
           prop.conflicts, prop.modelChecks, elapsed(), perRoot);
    if (res == 10 && modelOut) {
      FILE *fm = fopen(modelOut, "w");
      for (int x = 1; x <= V; x++) fprintf(fm, "%d\n", prop.graphModel[x] ? x : -x);
      fclose(fm);
    }
    S.disconnect_external_propagator();
    return res == 20 ? 0 : (res == 10 ? 10 : 1);
  }

  Searcher se;
  long long iters = 0, exactCalls = 0, images = 0;
  double satTime = 0, searchTime = 0;
  long long histo[64] = {0};
  int status = 0;
  int phase = degree ? 1 : 2;
  while (true) {
    if (elapsed() > timeLimit) {
      status = 0;
      break;
    }
    auto s0 = std::chrono::steady_clock::now();
    if (phase == 1) S.assume(act);
    int res = S.solve();
    satTime += std::chrono::duration<double>(std::chrono::steady_clock::now() - s0).count();
    if (res == 20) {
      if (phase == 1) {
        fprintf(stderr, "phase 1 (degree<=9) UNSAT after %lld iterations, %lld seps, %.1fs\n",
                iters, nsep, elapsed());
        phase = 2;
        S.clause(-act);
        continue;
      }
      status = 20;
      break;
    }
    if (res != 10) {
      fprintf(stderr, "solver returned %d\n", res);
      return 2;
    }
    iters++;
    std::vector<int> model(V + 1, 0);
    for (int x = 1; x <= V; x++) model[x] = S.val(x) > 0 ? 1 : 0;
    u64 adj[N] = {0};
    for (int u = 0; u < N; u++)
      for (int v = u + 1; v < N; v++)
        if (model[pv[u][v]]) {
          adj[u] |= 1ULL << v;
          adj[v] |= 1ULL << u;
        }
    for (int u = 0; u < N; u++)
      for (int v = u + 1; v < N; v++)
        if (((adj[u] >> v) & 1) && (adj[u] & adj[v])) {
          fprintf(stderr, "model has a triangle: encoding bug\n");
          return 3;
        }
    auto q0 = std::chrono::steady_clock::now();
    se.run(adj, K, perRoot);
    std::vector<Sol> found = se.best;
    if (found.empty()) {
      exactCalls++;
      int chosen[T];
      bool any = false;
      for (int r : reps) {
        chosen[0] = r;
        if (exactIndep(adj, ALL & ~adj[r] & ~(1ULL << r), 1, chosen)) {
          any = true;
          break;
        }
      }
      if (!any) {
        status = 10;
        fprintf(stderr, "FOUND (3,10)-graph candidate: no independent 10-set\n");
        if (modelOut) {
          FILE *fm = fopen(modelOut, "w");
          for (int x = 1; x <= V; x++) fprintf(fm, "%d\n", model[x] ? x : -x);
          fclose(fm);
        }
        break;
      }
      Sol s;
      for (int i = 0; i < T; i++) s.verts[i] = chosen[i];
      std::sort(s.verts, s.verts + T);
      s.clause = clauseOf(s.verts);
      s.cost = s.clause.size();
      found.push_back(s);
    }
    searchTime += std::chrono::duration<double>(std::chrono::steady_clock::now() - q0).count();
    for (auto &s : found) {
      for (int x : s.clause)
        if (model[x]) {
          fprintf(stderr, "separator does not block the model\n");
          return 3;
        }
      if (!addSeparator(s.verts)) {
        fprintf(stderr, "separator clause already present: solver bug\n");
        return 3;
      }
      histo[std::min<int>(63, s.cost)]++;
      for (auto &phi : syms) {
        int img[T];
        for (int i = 0; i < T; i++) img[i] = phi[s.verts[i]];
        if (addSeparator(img)) images++;
      }
    }
    if (logEvery && iters % logEvery == 0) {
      fflush(fo);
      fprintf(stderr,
              "iters %lld seps %lld images %lld exact %lld elapsed %.1f sat %.1f search %.1f\n",
              iters, nsep, images, exactCalls, elapsed(), satTime, searchTime);
    }
  }
  fclose(fo);
  printf("{\"status\": \"%s\", \"iterations\": %lld, \"separators\": %lld, "
         "\"exact_calls\": %lld, \"elapsed\": %.2f, \"sat_time\": %.2f, "
         "\"search_time\": %.2f, \"k\": %zu, \"nodes_per_root\": %lld, \"histogram\": {",
         status == 20 ? "UNSAT" : status == 10 ? "SAT" : "UNKNOWN", iters, nsep,
         exactCalls, elapsed(), satTime, searchTime, K, perRoot);
  bool first = true;
  for (int i = 0; i < 64; i++)
    if (histo[i]) {
      printf("%s\"%d\": %lld", first ? "" : ", ", i, histo[i]);
      first = false;
    }
  printf("}}\n");
  return status == 20 ? 0 : (status == 10 ? 10 : 1);
}
