// Exact values of Catch-Up({1..N}) by a turn-level proof search.
//
// A position at the start of a turn is (R, d): R = remaining numbers (bit x-1 <-> number x),
// d >= 0 = how far the player to move is behind. A turn removes a set A with
//     sum(A) >= d  and  sum(A) - max(A) < d      (for d = 0: a single number),
// i.e. the numbers can be picked one at a time, largest last, staying strictly behind before the
// final pick. The opponent then faces (R \ A, sum(A) - d). With R empty the mover draws if d = 0
// and loses otherwise; if sum(R) < d the mover cannot catch up and loses. The fresh game on S is
// (S, 0): the first move is a single pick. DETAILS.md proves this equals the upstream `valueAux`.
//
// NL(R, d): the mover can secure at least a draw.   W(R, d): the mover can force a win.
//   NL(R, d) = exists legal A with not W(R \ A, sum(A) - d)
//   W(R, d)  = exists legal A with not NL(R \ A, sum(A) - d)
// Pruning (proved in DETAILS.md): with u = (sum(R) + d) / 2, a legal A with sum(A) >= u secures a
// draw (sum(A) > u: a win), because the mover's final share of R is at least sum(A); and a move
// with 2 sum(A) = sum(R) + d is exactly a draw. Move order only affects speed.
//
// Usage: catchup_turn N0 [N1]          values for N = N0..N1 (1 <= N <= 40)
//        catchup_turn --positions n     value of every (R, d) with R a subset of {1..n}, d <= n
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <utility>
#include <vector>

typedef uint64_t u64;

// Hash table: one u64 per slot = (key << 4) | flags, key = (R << 6) | d (never 0).
// flags: bit0 NL known, bit1 NL value, bit2 W known, bit3 W value.
struct Table {
  u64 *slots = nullptr;
  u64 cap = 0, cnt = 0;
  void init(u64 c) {
    cap = c;
    cnt = 0;
    slots = (u64 *)calloc(cap, 8);
    if (!slots) { fprintf(stderr, "out of memory\n"); exit(2); }
  }
  void clear() { memset(slots, 0, cap * 8); cnt = 0; }
  static inline u64 h(u64 k) {
    k ^= k >> 33; k *= 0xff51afd7ed558ccdULL;
    k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ULL;
    k ^= k >> 33;
    return k;
  }
  void grow() {
    u64 oc = cap, *os = slots;
    init(oc * 2);
    for (u64 i = 0; i < oc; i++)
      if (os[i]) {
        u64 j = h(os[i] >> 4) & (cap - 1);
        while (slots[j]) j = (j + 1) & (cap - 1);
        slots[j] = os[i];
        cnt++;
      }
    free(os);
  }
  uint8_t get(u64 k) {
    u64 j = h(k) & (cap - 1);
    while (slots[j]) {
      if ((slots[j] >> 4) == k) return slots[j] & 15;
      j = (j + 1) & (cap - 1);
    }
    return 0;
  }
  void set(u64 k, uint8_t bits) {
    if (cnt * 4 > cap * 3) grow();
    u64 j = h(k) & (cap - 1);
    while (slots[j]) {
      if ((slots[j] >> 4) == k) { slots[j] |= bits; return; }
      j = (j + 1) & (cap - 1);
    }
    slots[j] = (k << 4) | bits;
    cnt++;
  }
};
static Table tab;
static long long nNL = 0, nW = 0;

static inline int sumR(u64 R) {
  int s = 0;
  for (; R; R &= R - 1) s += __builtin_ctzll(R) + 1;
  return s;
}
static inline int topElem(u64 R) { return 64 - __builtin_clzll(R); }
// sorted, each element <= 1 + sum of the smaller ones (used for move ordering only)
static inline bool completeSet(u64 R) {
  int pre = 0;
  for (u64 t = R; t; t &= t - 1) {
    int x = __builtin_ctzll(t) + 1;
    if (x > pre + 1) return false;
    pre += x;
  }
  return true;
}
// Largest sum of a legal turn (requires R nonempty, sum(R) >= d, d <= 63): take the largest
// number M plus the largest subset sum of the others that is <= d - 1 (any d for which some
// legal turn exists makes this at least d).
static inline int maxLegalSum(u64 R, int d) {
  int M = topElem(R);
  if (d == 0) return M;
  u64 reach = 1;  // bit s set <=> some subset of R \ {M} has sum s (sums < 64 suffice)
  for (u64 t = R & ~(1ULL << (M - 1)); t; t &= t - 1) reach |= reach << (__builtin_ctzll(t) + 1);
  u64 r = reach & ((1ULL << d) - 1);
  return M + 63 - __builtin_clzll(r);
}

struct Mv { u64 A; int sa; };
// legal turns with largest element m: B subset of the numbers below m, d - m <= sum(B) <= d - 1
static void enumB(int m, const int *el, const int *pre, int i, int s, u64 B, int lo, int hi,
                  std::vector<Mv> &out) {
  if (s + pre[i] < lo) return;
  if (i == 0) {
    if (s >= lo && s <= hi) out.push_back({B | (1ULL << (m - 1)), s + m});
    return;
  }
  int x = el[i - 1];
  if (s + x <= hi) enumB(m, el, pre, i - 1, s + x, B | (1ULL << (x - 1)), lo, hi, out);
  enumB(m, el, pre, i - 1, s, B, lo, hi, out);
}
static void genMoves(u64 R, int d, std::vector<Mv> &out) {
  int el[64], pre[65], k = 0;
  for (u64 t = R; t; t &= t - 1) el[k++] = __builtin_ctzll(t) + 1;
  pre[0] = 0;
  for (int i = 0; i < k; i++) pre[i + 1] = pre[i] + el[i];
  if (d == 0) {
    for (int j = k - 1; j >= 0; j--) out.push_back({1ULL << (el[j] - 1), el[j]});
    return;
  }
  for (int j = k - 1; j >= 0; j--) {
    int lo = d - el[j];
    if (lo < 0) lo = 0;
    enumB(el[j], el, pre, j, 0, 0, lo, d - 1, out);
  }
}
// order: ties leaving a complete set first, then by the opponent's new deficit, ascending
static void orderMoves(u64 R, int d, const std::vector<Mv> &mv, std::vector<std::pair<int, int>> &ord) {
  ord.reserve(mv.size());
  for (int i = 0; i < (int)mv.size(); i++) {
    int e = mv[i].sa - d;
    ord.push_back({(e == 0 && completeSet(R & ~mv[i].A)) ? 0 : 1 + e, i});
  }
  std::sort(ord.begin(), ord.end());
}

static bool W(u64 R, int d);

static bool NL(u64 R, int d) {
  if (R == 0) return d == 0;
  int S = sumR(R);
  if (S < d) return false;
  if (2 * maxLegalSum(R, d) >= S + d) return true;  // immediate draw or win
  u64 key = (R << 6) | (u64)d;
  uint8_t f = tab.get(key);
  if (f & 1) return (f >> 1) & 1;
  nNL++;
  std::vector<Mv> mv;
  genMoves(R, d, mv);
  std::vector<std::pair<int, int>> ord;
  orderMoves(R, d, mv, ord);
  bool res = false;
  for (auto &p : ord) {
    const Mv &m = mv[p.second];
    if (!W(R & ~m.A, m.sa - d)) { res = true; break; }
  }
  tab.set(key, 1 | (res ? 2 : 0));
  return res;
}

static bool W(u64 R, int d) {
  if (R == 0) return false;
  int S = sumR(R);
  if (S < d) return false;
  if (2 * maxLegalSum(R, d) > S + d) return true;  // immediate win
  u64 key = (R << 6) | (u64)d;
  uint8_t f = tab.get(key);
  if (f & 4) return (f >> 3) & 1;
  nW++;
  std::vector<Mv> mv;
  genMoves(R, d, mv);
  std::vector<std::pair<int, int>> ord;
  orderMoves(R, d, mv, ord);
  bool res = false;
  for (auto &p : ord) {
    const Mv &m = mv[p.second];
    if (2 * m.sa == S + d) continue;  // exactly a draw: the opponent takes the rest and ties
    if (!NL(R & ~m.A, m.sa - d)) { res = true; break; }
  }
  tab.set(key, 4 | (res ? 8 : 0));
  return res;
}

static const char *word(int v) { return v > 0 ? "win" : (v < 0 ? "loss" : "draw"); }

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: catchup_turn N0 [N1] | catchup_turn --positions n\n");
    return 1;
  }
  if (!strcmp(argv[1], "--positions")) {
    int n = argc > 2 ? atoi(argv[2]) : 0;
    if (n < 1 || n > 20) { fprintf(stderr, "need 1 <= n <= 20\n"); return 1; }
    tab.init(1ULL << 20);
    for (u64 R = 0; R < (1ULL << n); R++)
      for (int d = 0; d <= n; d++)
        printf("%llu %d %s\n", (unsigned long long)R, d, word(W(R, d) ? 1 : (NL(R, d) ? 0 : -1)));
    return 0;
  }
  int N0 = atoi(argv[1]), N1 = argc > 2 ? atoi(argv[2]) : N0;
  if (N0 < 1 || N1 > 40 || N0 > N1) { fprintf(stderr, "need 1 <= N0 <= N1 <= 40\n"); return 1; }
  tab.init(1ULL << 20);
  for (int N = N0; N <= N1; N++) {
    tab.clear();
    nNL = nW = 0;
    auto t0 = std::chrono::steady_clock::now();
    u64 full = (1ULL << N) - 1;
    int T = N * (N + 1) / 2;
    int value;
    if (T % 2 == 0) {
      // value = best over x of -V({1..N} \ {x}, x)
      bool atLeastDraw = NL(full, 0);
      bool p2AlwaysDraws = true;
      for (int x = 1; x <= N && p2AlwaysDraws; x++)
        if (!NL(full & ~(1ULL << (x - 1)), x)) p2AlwaysDraws = false;
      value = !atLeastDraw ? -1 : (p2AlwaysDraws ? 0 : 1);
    } else {
      value = W(full, 0) ? 1 : -1;  // odd total: no draw (Lean: valueAux_ne_draw)
    }
    double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    printf("N=%d T=%d value=%s NLnodes=%lld Wnodes=%lld table=%llu time=%.2fs\n", N, T, word(value),
           nNL, nW, (unsigned long long)tab.cnt, dt);
    fflush(stdout);
  }
  return 0;
}
