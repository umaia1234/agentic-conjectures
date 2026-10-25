// diampath_gen.cpp -- generate every connected graph with n vertices and
// diameter exactly D (up to isomorphism, with repetitions), as graph6.
//
// Build:  g++ -O3 -std=c++17 diampath_gen.cpp -o diampath_gen
// Usage:  ./diampath_gen N D [res/mod] | ./wowii61
//
// Why this is complete: let G have diameter D and let P = v0 v1 ... vD be a
// shortest path between two vertices at distance D.  Every other vertex x
// has its neighbours on P inside a window {vi, vi+1, vi+2} (two neighbours
// vi, vj with j >= i+3 would shorten P).  So G arises from the path
// 0 - 1 - ... - D, the k = N-D-1 extra vertices, a "window" neighbourhood
// on the path for each extra vertex and an arbitrary graph on the extra
// vertices.  Relabelling the extra vertices we may assume their window
// options are non-decreasing in a fixed order of the options; all graphs on
// the extra vertices are enumerated.  Every generated graph whose diameter
// is exactly D is printed, so every isomorphism class of connected graphs
// with diameter D on N vertices appears at least once (repetitions are
// possible).  res/mod restricts to the option sequences with index = res
// (mod mod), for parallel runs.

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>

typedef uint64_t mask;
static inline mask bit(int v) { return (mask)1 << v; }

int n, D, k, R = 0, M = 1;
std::vector<mask> opts;  // window neighbourhoods on the path vertices 0..D
mask adj[64];
uint64_t seq_index = 0, printed = 0, generated = 0;
int choice[64];

static int diameter() {
  const mask all = n >= 64 ? ~(mask)0 : bit(n) - 1;
  int best = 0;
  for (int s = 0; s < n; ++s) {
    mask reach = bit(s), fr = reach;
    int e = 0;
    while (reach != all) {
      mask nx = 0;
      for (mask t = fr; t; t &= t - 1) nx |= adj[__builtin_ctzll(t)];
      nx &= ~reach;
      if (!nx) return -1;
      reach |= nx;
      fr = nx;
      ++e;
    }
    if (e > best) best = e;
    if (best > D) return best;
  }
  return best;
}

static void emit() {
  std::string out(1, (char)(63 + n));
  int acc = 0, nb = 0;
  for (int j = 1; j < n; ++j)
    for (int i = 0; i < j; ++i) {
      acc = (acc << 1) | (int)((adj[i] >> j) & 1);
      if (++nb == 6) { out += (char)(63 + acc); acc = 0; nb = 0; }
    }
  if (nb) out += (char)(63 + (acc << (6 - nb)));
  out += '\n';
  fwrite(out.data(), 1, out.size(), stdout);
  ++printed;
}

static void run_sequence() {
  // base graph: path plus window neighbourhoods
  for (int v = 0; v < n; ++v) adj[v] = 0;
  for (int i = 0; i < D; ++i) { adj[i] |= bit(i + 1); adj[i + 1] |= bit(i); }
  for (int j = 0; j < k; ++j) {
    int x = D + 1 + j;
    mask w = opts[choice[j]];
    adj[x] |= w;
    for (mask t = w; t; t &= t - 1) adj[__builtin_ctzll(t)] |= bit(x);
  }
  std::vector<std::pair<int, int>> pairs;
  for (int a = 0; a < k; ++a)
    for (int b = a + 1; b < k; ++b) pairs.push_back({D + 1 + a, D + 1 + b});
  mask base[64];
  for (int v = 0; v < n; ++v) base[v] = adj[v];
  const uint64_t E = pairs.size();
  for (uint64_t e = 0; e < ((uint64_t)1 << E); ++e) {
    for (int v = 0; v < n; ++v) adj[v] = base[v];
    for (uint64_t p = 0; p < E; ++p)
      if ((e >> p) & 1) {
        adj[pairs[p].first] |= bit(pairs[p].second);
        adj[pairs[p].second] |= bit(pairs[p].first);
      }
    ++generated;
    if (diameter() == D) emit();
  }
}

static void rec(int j, int from) {
  if (j == k) {
    if ((seq_index++ % M) == (uint64_t)R) run_sequence();
    return;
  }
  for (int o = from; o < (int)opts.size(); ++o) {
    choice[j] = o;
    rec(j + 1, o);
  }
}

int main(int argc, char** argv) {
  if (argc < 3) {
    fprintf(stderr, "usage: diampath_gen N D [res/mod]\n");
    return 2;
  }
  n = atoi(argv[1]);
  D = atoi(argv[2]);
  if (argc > 3 && sscanf(argv[3], "%d/%d", &R, &M) != 2) return 2;
  if (D < 1 || n < D + 1 || n > 62 || n - D - 1 > 8 || M < 1 || R < 0 || R >= M) {
    fprintf(stderr, "need 1 <= D < N <= 62, N-D-1 <= 8, 0 <= res < mod\n");
    return 2;
  }
  k = n - D - 1;
  opts.push_back(0);
  for (int i = 0; i <= D; ++i) {
    opts.push_back(bit(i));
    if (i + 1 <= D) opts.push_back(bit(i) | bit(i + 1));
    if (i + 2 <= D) {
      opts.push_back(bit(i) | bit(i + 2));
      opts.push_back(bit(i) | bit(i + 1) | bit(i + 2));
    }
  }
  rec(0, 0);
  fprintf(stderr, ">Z diampath_gen %d %d: %llu generated, %llu with diameter %d printed\n", n, D,
          (unsigned long long)generated, (unsigned long long)printed, D);
  return 0;
}
