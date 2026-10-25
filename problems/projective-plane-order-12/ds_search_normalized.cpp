// Method B: exhaustive search for lambda = 1 (relative) difference sets in Z_v, normalised
// under the full affine group x -> u x + c (u a unit), with Golomb-type gap pruning.
// Written independently of ds_enumerate.cpp (method A); different normal form,
// different data structures (64-bit word bitsets), different pruning.
//
// Usage: ds_search_normalized v k m      (N = m Z_v forbidden subgroup, m | v; m = v: N = {0})
//
// Normal form (proof in README.md).  For a set D, the ratio of an ordered triple (a,b,c) of
// distinct elements with b - a a unit of Z_v is r = (c - a)/(b - a) in {0..v-1}.  Ratios are
// invariant under x -> u x + c.  Let T(D) be the least ratio of D.  If (a,b,c) attains it, the
// image D' = (D - a)/(b - a) contains 0 and 1, every element of D' other than 0, 1 is a ratio
// >= T, and T itself is an element of D'.  Hence every orbit contains a set D with
//   0, 1 in D,   t := min(D \ {0,1}) = T(D)   (no ratio of D is smaller than t).
// For a distinct-difference set no ratio equals 2 (c - b = b - a), so t >= 3.
// We search, for each t = 3..v-1, all D with {0,1,t} in D, D cap [2,t) empty, further
// elements added in increasing order, rejecting an element as soon as
//   (i) a difference repeats or lies in N, or (ii) a ratio < t appears
// (both properties are inherited by supersets, so the pruning is exact), and
//   (iii) the gap bound: if L is the current maximum and r elements are still missing, the
//   r+1 remaining cyclic gaps are distinct unused differences in [1, v-1] summing to v - L.
// Output: per-t node counts, every solution, and the total.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

namespace {

int V, K, M;
std::vector<int> inv;        // inv[x] = x^{-1} mod V if gcd(x,V)=1, else 0
std::vector<int> elems;      // current set
std::vector<uint64_t> used;  // bitset over Z_V: differences already present
int words;
uint64_t nodes_total = 0, sols = 0;

inline bool test(const std::vector<uint64_t>& b, int i) { return (b[i >> 6] >> (i & 63)) & 1; }
inline void setb(std::vector<uint64_t>& b, int i) { b[i >> 6] |= (uint64_t)1 << (i & 63); }
inline void clrb(std::vector<uint64_t>& b, int i) { b[i >> 6] &= ~((uint64_t)1 << (i & 63)); }
inline int md(long long x) { x %= V; return (int)(x < 0 ? x + V : x); }

// ratio (c - a)/(b - a) or -1 if b - a is not a unit
inline int ratio(int a, int b, int c) {
  int iv = inv[md(b - a)];
  if (!iv) return -1;
  return md((long long)md(c - a) * iv);
}

// can x join the current set?  On success the new differences are marked in `used`.
bool try_add(int x, int t) {
  int mark[512];  // 2 * |D| <= 2 * K <= 512 (checked in main)
  int nm = 0;
  for (int e : elems) {
    int d1 = md(x - e), d2 = md(e - x);
    if (d1 % M == 0 || test(used, d1)) goto fail;
    setb(used, d1); mark[nm++] = d1;
    if (test(used, d2)) goto fail;
    setb(used, d2); mark[nm++] = d2;
  }
  // ratio condition: every ordered triple containing x.  At this point D + x has distinct
  // differences, so every ratio is >= 3 (0, 1 need equal points, 2 a repeated difference);
  // for t = 3 the test is therefore vacuous and skipped.
  if (t > 3)
  for (size_t i = 0; i < elems.size(); ++i)
    for (size_t j = 0; j < elems.size(); ++j) {
      if (i == j) continue;
      int a = elems[i], b = elems[j];
      int r1 = ratio(a, b, x), r2 = ratio(a, x, b), r3 = ratio(x, a, b);
      if ((r1 >= 0 && r1 < t) || (r2 >= 0 && r2 < t) || (r3 >= 0 && r3 < t)) goto fail;
    }
  return true;
fail:
  for (int i = 0; i < nm; ++i) clrb(used, mark[i]);
  return false;
}

void undo_add(int x) {
  for (int e : elems) {
    if (e == x) continue;
    clrb(used, md(x - e));
    clrb(used, md(e - x));
  }
}

// gap bound with r >= 1 elements still missing: the r+1 gaps L -> y_1 -> ... -> y_r -> V
// each involve a new element, so they are r+1 distinct unused differences in [1, V-1]
// (outside N) with sum V - L.  With r = 0 there is nothing to bound.
bool gap_ok(int L, int r) {
  if (r <= 0) return true;
  int need = r + 1, sum = 0;
  for (int g = 1; g < V && need > 0; ++g) {
    if (g % M == 0 || test(used, g)) continue;
    sum += g;
    --need;
    if (sum > V - L) return false;
  }
  return need == 0 && sum <= V - L;
}

void rec(int t, std::vector<uint64_t>& cnt) {
  ++nodes_total;
  ++cnt[elems.size()];
  if ((int)elems.size() == K) {
    ++sols;
    std::printf("SOLUTION t=%d", t);
    for (int e : elems) std::printf(" %d", e);
    std::printf("\n");
    return;
  }
  const int L = elems.back();
  const int r = K - (int)elems.size();
  for (int x = L + 1; x < V; ++x) {
    if (!try_add(x, t)) continue;
    elems.push_back(x);
    if (gap_ok(x, r - 1)) rec(t, cnt);
    elems.pop_back();
    undo_add(x);
  }
}

}  // namespace

int main(int argc, char** argv) {
  if (argc != 4) { std::fprintf(stderr, "usage: %s v k m\n", argv[0]); return 2; }
  V = std::atoi(argv[1]); K = std::atoi(argv[2]); M = std::atoi(argv[3]);
  if (V < 5 || K < 3 || K > 256 || M < 2 || V % M) {
    std::fprintf(stderr, "bad parameters\n");
    return 2;
  }
  inv.assign(V, 0);
  for (int x = 1; x < V; ++x)
    for (int y = 1; y < V; ++y)
      if ((long long)x * y % V == 1) { inv[x] = y; break; }
  words = (V + 63) / 64;
  used.assign(words, 0);
  std::vector<uint64_t> cnt(K + 1, 0);
  for (int t = 3; t < V; ++t) {
    std::fill(cnt.begin(), cnt.end(), 0);
    elems = {0};
    if (!try_add(1, t)) continue;   // never fails: 1 is not in N
    elems.push_back(1);
    if (try_add(t, t)) {
      elems.push_back(t);
      if (gap_ok(t, K - 3)) rec(t, cnt);
      elems.pop_back();
      undo_add(t);
    }
    elems.pop_back();
    undo_add(1);
    uint64_t tot = 0;
    for (auto c : cnt) tot += c;
    if (tot) {
      std::printf("BRANCH t=%d nodes=%llu", t, (unsigned long long)tot);
      for (int j = 3; j <= K; ++j) std::printf(" %llu", (unsigned long long)cnt[j]);
      std::printf("\n");
    }
  }
  for (uint64_t w : used)
    if (w) { std::fprintf(stderr, "internal error: bitset not cleared\n"); return 3; }
  std::printf("PARAMS v=%d k=%d m=%d\n", V, K, M);
  std::printf("TOTAL nodes=%llu solutions=%llu\n", (unsigned long long)nodes_total,
              (unsigned long long)sols);
  return 0;
}
