// Independent check of Catch-Up({1..N}) values, written pick by pick after the
// formal-conjectures definition `valueAux` (one number per recursion step). It shares no code
// and no pruning lemma with catchup_turn.cpp: only memoization and short-circuiting are added.
//
// valueAux R s_me s_opp false depends only on R and the gap D = s_opp - s_me >= 0
// (Lean: valueAux_add, valueAux_eq_gapValue). Write P(R, D) for that value:
//   R empty          -> draw if D = 0, loss if D > 0
//   sum R < D        -> loss
//   otherwise best over x in R of
//       x >= D : -P(R \ {x}, x - D)      (turn ends, roles swap)
//       x <  D :  P(R \ {x}, D - x)      (still behind, same player picks again)
// (Lean: gapValue_eq). The game value is best over x of -P(S \ {x}, x): the first move is one
// pick and the roles swap (Lean: value_eq_gapValue). Gaps never exceed N.
//
// Booleans: A(R,D) <=> P >= 0 ("at least a draw"), B(R,D) <=> P = 1 ("win").
//
// Usage: catchup_pick N0 [N1]          values for N = N0..N1 (1 <= N <= 40)
//        catchup_pick --positions n     P(R, D) for every R subset of {1..n}, D <= n
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

typedef uint64_t u64;

// open addressing, linear probing; one u64 per slot = (key << 4) | flags with
// key = R * 64 + D + 1 (never 0, so 0 marks an empty slot) and
// flags bit0: A known, bit1: A value, bit2: B known, bit3: B value
static u64 *T = nullptr;
static u64 cap = 0, used = 0;
static long long calls = 0;

static u64 mix(u64 x) {
  x += 0x9e3779b97f4a7c15ULL;
  x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
  x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
  return x ^ (x >> 31);
}
static void tinit(u64 c) {
  cap = c; used = 0;
  T = (u64 *)calloc(cap, sizeof(u64));
  if (!T) { fprintf(stderr, "out of memory\n"); exit(2); }
}
static u64 slot(u64 key) {
  u64 i = mix(key) & (cap - 1);
  while (T[i] != 0 && (T[i] >> 4) != key) i = (i + 1) & (cap - 1);
  return i;
}
static void rehash() {
  u64 oc = cap; u64 *ot = T;
  tinit(oc * 2);
  for (u64 i = 0; i < oc; i++)
    if (ot[i]) { T[slot(ot[i] >> 4)] = ot[i]; used++; }
  free(ot);
}
static uint8_t lookup(u64 key) { u64 i = slot(key); return T[i] ? (T[i] & 15) : 0; }
static void store(u64 key, uint8_t bits) {
  if (4 * (used + 1) > 3 * cap) rehash();
  u64 i = slot(key);
  if (!T[i]) { T[i] = key << 4; used++; }
  T[i] |= bits;
}

static int total(u64 R) {
  int s = 0;
  for (int x = 1; x <= 63; x++) if (R >> (x - 1) & 1) s += x;
  return s;
}

static bool B(u64 R, int D);

static bool A(u64 R, int D) {
  if (R == 0) return D == 0;
  if (total(R) < D) return false;
  u64 key = R * 64 + (u64)D + 1;
  uint8_t f = lookup(key);
  if (f & 1) return f & 2;
  calls++;
  bool r = false;
  // order (irrelevant for correctness): x = D, then x < D from the top, then x > D from below
  if (D >= 1 && D <= 63 && (R >> (D - 1) & 1)) r = !B(R & ~(1ULL << (D - 1)), 0);
  for (int x = (D - 1 < 63 ? D - 1 : 63); x >= 1 && !r; x--)
    if (R >> (x - 1) & 1) r = A(R & ~(1ULL << (x - 1)), D - x);
  for (int x = (D + 1 > 1 ? D + 1 : 1); x <= 63 && !r; x++)
    if (R >> (x - 1) & 1) r = !B(R & ~(1ULL << (x - 1)), x - D);
  store(key, 1 | (r ? 2 : 0));
  return r;
}

static bool B(u64 R, int D) {
  if (R == 0) return false;
  if (total(R) < D) return false;
  u64 key = R * 64 + (u64)D + 1;
  uint8_t f = lookup(key);
  if (f & 4) return f & 8;
  calls++;
  bool r = false;
  if (D >= 1 && D <= 63 && (R >> (D - 1) & 1)) r = !A(R & ~(1ULL << (D - 1)), 0);
  for (int x = (D - 1 < 63 ? D - 1 : 63); x >= 1 && !r; x--)
    if (R >> (x - 1) & 1) r = B(R & ~(1ULL << (x - 1)), D - x);
  for (int x = (D + 1 > 1 ? D + 1 : 1); x <= 63 && !r; x++)
    if (R >> (x - 1) & 1) r = !A(R & ~(1ULL << (x - 1)), x - D);
  store(key, 4 | (r ? 8 : 0));
  return r;
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: catchup_pick N0 [N1] | catchup_pick --positions n\n");
    return 1;
  }
  if (!strcmp(argv[1], "--positions")) {
    int n = argc > 2 ? atoi(argv[2]) : 0;
    if (n < 1 || n > 20) { fprintf(stderr, "need 1 <= n <= 20\n"); return 1; }
    tinit(1ULL << 20);
    for (u64 R = 0; R < (1ULL << n); R++)
      for (int D = 0; D <= n; D++)
        printf("%llu %d %s\n", (unsigned long long)R, D, B(R, D) ? "win" : (A(R, D) ? "draw" : "loss"));
    return 0;
  }
  int N0 = atoi(argv[1]), N1 = argc > 2 ? atoi(argv[2]) : N0;
  if (N0 < 1 || N1 > 40 || N0 > N1) { fprintf(stderr, "need 1 <= N0 <= N1 <= 40\n"); return 1; }
  for (int N = N0; N <= N1; N++) {
    tinit(1ULL << 20);
    calls = 0;
    auto t0 = std::chrono::steady_clock::now();
    u64 S = (1ULL << N) - 1;
    // first move: P1 picks x, then P2 faces gap x with no first-move rule
    bool p1AtLeastDraw = false, p1Win = false;
    for (int x = N; x >= 1; x--) {
      u64 R2 = S & ~(1ULL << (x - 1));
      if (!B(R2, x)) p1AtLeastDraw = true;   // P2 cannot win after x
      if (!A(R2, x)) p1Win = true;           // P2 cannot even draw after x
    }
    const char *v = p1Win ? "win" : (p1AtLeastDraw ? "draw" : "loss");
    double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    printf("N=%d value=%s calls=%lld states=%llu time=%.2fs\n", N, v, calls, (unsigned long long)used, dt);
    fflush(stdout);
    free(T);
  }
  return 0;
}
