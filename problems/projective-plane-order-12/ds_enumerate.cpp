// Method A: exhaustive forward enumeration of normalised (relative) difference sets
// with lambda = 1 in the cyclic group Z_v.
//
// Usage: ds_enumerate v k m
//   N = m Z_v is the forbidden subgroup (m must divide v; m = v means N = {0}).
//   A subset D of Z_v with |D| = k is a relative difference set with lambda = 1
//   relative to N iff the k(k-1) ordered differences d - e (d != e in D) are pairwise
//   distinct and none lies in N; if moreover k(k-1) = v - |N|, they cover Z_v \ N.
//   * projective plane of order q (planar / Singer type): v = q^2+q+1, k = q+1, m = v;
//   * cyclic affine plane of order q (Bose type, (q+1,q-1,q,1) RDS): v = q^2-1, k = q,
//     m = q+1, so N = (q+1)Z_v has order q-1.
//
// Normalisation (proved in the README): the difference 1 (not in N) is represented by a
// unique pair (a, a+1) of D, and D - a is again such a set, so it suffices to search sets
// containing 0 and 1.  We enumerate EVERY subset S of Z_v with {0,1} in S, all ordered
// differences of S pairwise distinct and outside N, by adding elements in increasing
// order (each such S is visited exactly once), up to size k.  No other pruning is used.
//
// Output: count[j] = number of such S of size j (j = 2..k), every S of size k (solutions),
// and the total count of solutions.  Exit code 0.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

static int v, k, m;
static std::vector<int> D;          // current set, D[0] = 0, D[1] = 1, then increasing
static std::vector<char> used;      // used[d] = 1 iff d in Z_v is a difference of D
static std::vector<uint64_t> cnt;   // cnt[j] = number of valid sets of size j
static uint64_t solutions = 0;

static void report_solution() {
  ++solutions;
  std::printf("SOLUTION");
  for (int x : D) std::printf(" %d", x);
  std::printf("\n");
}

static void extend(int last) {
  const int j = (int)D.size();
  ++cnt[j];
  if (j == k) {
    report_solution();
    return;
  }
  std::vector<int> added;
  added.reserve(2 * j);
  for (int x = last + 1; x < v; ++x) {
    bool ok = true;
    added.clear();
    for (int e : D) {
      const int a = (x - e + v) % v;  // difference x - e
      const int b = (e - x + v) % v;  // difference e - x
      if (a % m == 0 || used[a]) { ok = false; break; }
      used[a] = 1; added.push_back(a);
      if (used[b]) { ok = false; break; }  // also catches b == a and 2x = e + e'
      used[b] = 1; added.push_back(b);
    }
    if (ok) {
      D.push_back(x);
      extend(x);
      D.pop_back();
    }
    for (int d : added) used[d] = 0;
  }
}

int main(int argc, char** argv) {
  if (argc != 4) {
    std::fprintf(stderr, "usage: %s v k m\n", argv[0]);
    return 2;
  }
  v = std::atoi(argv[1]);
  k = std::atoi(argv[2]);
  m = std::atoi(argv[3]);
  if (v < 3 || k < 2 || m < 2 || v % m != 0 || 1 % m == 0) {
    std::fprintf(stderr, "bad parameters\n");
    return 2;
  }
  used.assign(v, 0);
  cnt.assign(k + 1, 0);
  // start from {0, 1}; its differences are +1 and -1 (1 is not in N since m >= 2)
  D = {0, 1};
  used[1] = 1;
  if (used[v - 1]) {  // v = 2 is excluded above, so -1 != 1
    std::fprintf(stderr, "internal error\n");
    return 3;
  }
  used[v - 1] = 1;
  extend(1);
  std::printf("PARAMS v=%d k=%d m=%d |N|=%d\n", v, k, m, v / m);
  for (int j = 2; j <= k; ++j)
    std::printf("COUNT size=%d sets=%llu\n", j, (unsigned long long)cnt[j]);
  std::printf("TOTAL solutions=%llu\n", (unsigned long long)solutions);
  return 0;
}
