// Experiments on the conjectured invariant of DETAILS.md, Section 5, for set positions.
//
// Class X: positions (R, D) with R a nonempty subset of {1..n}, the multiset R + {D} complete
// (D = 0 adds nothing; complete = sorted, each element <= 1 + sum of the smaller ones) and
// sum(R) - D even. For every X position this program reports
//   loss       V(R, D) = loss, a counterexample to Conjecture L (exact value from a plain
//              memoized turn recursion without any pruning);
//   immediate  some legal turn A has 2 sum(A) >= sum(R) + D, so V >= draw (Lemma 3.1);
//   closed     not immediate, but some turn A makes every opponent reply A2 either an exact
//              draw (2 sum(A2) = sum(R) - D) or a return to X; if every X position were
//              immediate or closed, Conjecture L for sets would follow by induction on |R|;
//   open       neither immediate nor closed;
//   tie        (D >= 1, not immediate) some turn with sum(A) = D leaves a complete set, so the
//              opponent is in X with gap 0;
//   max_bad /
//   min_bad    (D = 0, not immediate) taking the largest / smallest number lets the opponent win.
//
// Usage: closure_check n0 [n1]   (1 <= n0 <= n1 <= 16); exit status 1 iff some loss is found.
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

typedef uint64_t u64;

static int n, maxD;
static int8_t *memo = nullptr;  // V(R, d) + 1, or 3 if unknown

static inline int sumR(u64 R) {
  int s = 0;
  for (; R; R &= R - 1) s += __builtin_ctzll(R) + 1;
  return s;
}

struct Mv { u64 A; int sa; };
// legal turns with largest element m: B subset of the numbers below m, lo <= sum(B) <= hi
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
static void moves(u64 R, int d, std::vector<Mv> &out) {
  int el[64], pre[65], k = 0;
  for (u64 t = R; t; t &= t - 1) el[k++] = __builtin_ctzll(t) + 1;
  pre[0] = 0;
  for (int i = 0; i < k; i++) pre[i + 1] = pre[i] + el[i];
  if (d == 0) {
    for (int j = 0; j < k; j++) out.push_back({1ULL << (el[j] - 1), el[j]});
    return;
  }
  for (int j = 0; j < k; j++) {
    int lo = d - el[j];
    if (lo < 0) lo = 0;
    enumB(el[j], el, pre, j, 0, 0, lo, d - 1, out);
  }
}

// exact value for the player to move, -1 / 0 / 1
static int V(u64 R, int d) {
  if (R == 0) return d > 0 ? -1 : 0;
  if (sumR(R) < d) return -1;
  int8_t &slot = memo[R * (maxD + 1) + d];
  if (slot != 3) return slot - 1;
  std::vector<Mv> mv;
  moves(R, d, mv);
  int best = -1;
  for (auto &m : mv) {
    int v = -V(R & ~m.A, m.sa - d);
    if (v > best) best = v;
    if (best == 1) break;
  }
  slot = (int8_t)(best + 1);
  return best;
}

static bool completeWith(u64 R, int d) {  // multiset R + {d} complete (d = 0 adds nothing)
  long long pre = 0;
  bool used = (d == 0);
  for (u64 t = R; t; t &= t - 1) {
    int x = __builtin_ctzll(t) + 1;
    if (!used && d <= x) {
      if (d > pre + 1) return false;
      pre += d;
      used = true;
    }
    if (x > pre + 1) return false;
    pre += x;
  }
  return used || d <= pre + 1;
}
static bool inX(u64 R, int d) { return (sumR(R) - d) % 2 == 0 && completeWith(R, d); }

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: closure_check n0 [n1]\n"); return 1; }
  int n0 = atoi(argv[1]), n1 = argc > 2 ? atoi(argv[2]) : n0;
  if (n0 < 1 || n1 > 16 || n0 > n1) { fprintf(stderr, "need 1 <= n0 <= n1 <= 16\n"); return 1; }
  long long losses = 0;
  for (n = n0; n <= n1; n++) {
    auto t0 = std::chrono::steady_clock::now();
    maxD = n * (n + 1) / 2;
    size_t cells = (size_t(1) << n) * (maxD + 1);
    memo = (int8_t *)malloc(cells);
    if (!memo) { fprintf(stderr, "out of memory\n"); return 2; }
    memset(memo, 3, cells);
    long long total = 0, loss = 0, draw = 0, win = 0, imm = 0, closed = 0, open = 0;
    long long tieMiss = 0, tieMissN = 0, maxBad = 0, minBad = 0, zeroN = 0;
    for (u64 R = 1; R < (1ULL << n); R++) {
      int S = sumR(R);
      for (int d = 0; d <= S; d++) {
        if (!inX(R, d)) continue;
        total++;
        int v = V(R, d);
        if (v < 0) loss++; else if (v == 0) draw++; else win++;
        std::vector<Mv> mv;
        moves(R, d, mv);
        bool immediate = false;
        for (auto &m : mv) if (2 * m.sa >= S + d) { immediate = true; break; }
        if (immediate) { imm++; continue; }
        int w = (S - d) / 2;  // the opponent's half: a reply summing to more than w wins
        bool ok = false;
        for (auto &m : mv) {
          u64 R1 = R & ~m.A;
          int e = m.sa - d;
          std::vector<Mv> mv2;
          moves(R1, e, mv2);
          bool all = true;
          for (auto &m2 : mv2) {
            if (2 * m2.sa > 2 * w) { all = false; break; }
            if (m2.sa == w) continue;
            if (!inX(R1 & ~m2.A, m2.sa - e)) { all = false; break; }
          }
          if (all) { ok = true; break; }
        }
        if (ok) closed++; else open++;
        if (d >= 1) {
          tieMissN++;
          bool tie = false;
          for (auto &m : mv)
            if (m.sa == d && completeWith(R & ~m.A, 0)) { tie = true; break; }
          if (!tie) tieMiss++;
        } else {
          zeroN++;
          int top = 64 - __builtin_clzll(R), low = __builtin_ctzll(R) + 1;
          if (V(R & ~(1ULL << (top - 1)), top) == 1) maxBad++;
          if (V(R & ~(1ULL << (low - 1)), low) == 1) minBad++;
        }
      }
    }
    free(memo);
    losses += loss;
    double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    printf("n=%d X=%lld loss=%lld draw=%lld win=%lld immediate=%lld closed=%lld open=%lld "
           "no_tie=%lld/%lld max_bad=%lld/%lld min_bad=%lld/%lld time=%.2fs\n",
           n, total, loss, draw, win, imm, closed, open, tieMiss, tieMissN, maxBad, zeroN, minBad,
           zeroN, dt);
    fflush(stdout);
  }
  return losses ? 1 : 0;
}
