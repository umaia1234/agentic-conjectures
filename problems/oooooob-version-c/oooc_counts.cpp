// Outcome solver for Version C of "Generalizing OOOOOOB" (Danai, Ellis, Thanatipanonda,
// arXiv:2605.23213v1), memoized over packed pile counts.
//
// A position is a finite collection of piles.  A move removes one token from one pile, or one
// token from each of two distinct non-empty piles.  Normal play: a player with no move loses.
// A P-position is one that the player to move loses.  A position is stored by its counts
// c[1..N], where c[i] is the number of piles of size i; empty piles are dropped, which changes
// no option.  The counts are packed into one 64-bit key, 6 bits per count, so every position
// needs at most 63 non-empty piles and N <= 10 sizes.
//
// Conjecture 3.1 of the paper: if c[i] >= 2 for 1 <= i <= n, c[i] = 0 for i > n, and the
// position is not (2, 2, 3), then it is a P-position iff the total number of tokens is
// divisible by 3.
//
// usage:
//   oooc_counts --ci                 the four counterexample rows and the two range counts,
//                                    compared with the expected values (exit 1 on mismatch)
//   oooc_counts box n lo hi          every (a_1..a_n) in [lo, hi]^n: print each failure of the
//                                    conjecture and a summary line
//   oooc_counts outcome a_1 ... a_n  outcome of one position given by its counts
//   oooc_counts --version-b          the three Version B positions of the Related note in
//                                    DETAILS.md (exit 1 on mismatch)
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

typedef uint64_t u64;

static const int BITS = 6;
static const u64 MASK = (1u << BITS) - 1;
static int N = 0;  // largest pile size in play

static inline u64 unit(int size) { return size >= 1 ? (u64)1 << (BITS * (size - 1)) : 0; }
static inline int count(u64 key, int size) { return (int)((key >> (BITS * (size - 1))) & MASK); }

// Open-addressing hash table from keys to outcomes.  A slot holds 0 (empty) or
// ((key + 1) << 1) | isP.
struct Memo {
  std::vector<u64> slot;
  size_t used = 0;
  Memo() : slot(1 << 20, 0) {}
  static size_t hash(u64 k) {
    k ^= k >> 33; k *= 0xff51afd7ed558ccdULL; k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ULL;
    return (size_t)(k ^ (k >> 33));
  }
  int get(u64 key) const {  // -1 if absent
    size_t m = slot.size() - 1, i = hash(key) & m;
    for (;; i = (i + 1) & m) {
      if (slot[i] == 0) return -1;
      if ((slot[i] >> 1) == key + 1) return (int)(slot[i] & 1);
    }
  }
  void put(u64 key, int isP) {
    if (2 * (used + 1) > slot.size()) grow();
    size_t m = slot.size() - 1, i = hash(key) & m;
    while (slot[i] != 0) i = (i + 1) & m;
    slot[i] = ((key + 1) << 1) | (u64)isP;
    used++;
  }
  void grow() {
    std::vector<u64> old;
    old.swap(slot);
    slot.assign(old.size() * 2, 0);
    size_t m = slot.size() - 1;
    for (u64 e : old)
      if (e != 0) {
        size_t i = hash((e >> 1) - 1) & m;
        while (slot[i] != 0) i = (i + 1) & m;
        slot[i] = e;
      }
  }
};

static Memo memo;

// true iff the position is a P-position
static bool isP(u64 key) {
  int got = memo.get(key);
  if (got >= 0) return got;
  bool p = true;
  for (int i = 1; i <= N && p; i++) {
    if (count(key, i) == 0) continue;
    u64 k1 = key - unit(i) + unit(i - 1);  // one token from one pile of size i
    if (isP(k1)) { p = false; break; }
    for (int j = i; j <= N && p; j++) {  // one token from a pile of size i and one of size j
      if (j == i ? count(key, i) < 2 : count(key, j) == 0) continue;
      if (isP(k1 - unit(j) + unit(j - 1))) p = false;
    }
  }
  memo.put(key, p);
  return p;
}

// Version B of the paper, only for the Related note in DETAILS.md: a move removes one token from
// one pile, or one token from every pile.  The second move sends each count one size down and
// drops the piles of size 1, which is a shift of the packed key.
static Memo memoB;

static bool isPB(u64 key) {
  int got = memoB.get(key);
  if (got >= 0) return got;
  bool p = key == 0 || !isPB(key >> BITS);
  for (int i = 1; i <= N && p; i++)
    if (count(key, i) > 0 && isPB(key - unit(i) + unit(i - 1))) p = false;
  memoB.put(key, p);
  return p;
}

static u64 pack(const std::vector<int>& a) {  // a[i - 1] piles of size i
  u64 key = 0, piles = 0;
  for (size_t i = 0; i < a.size(); i++) {
    piles += a[i];
    key += (u64)a[i] * unit((int)i + 1);
  }
  if (piles > MASK || (int)a.size() > N) {
    fprintf(stderr, "position too large for the packing\n");
    exit(2);
  }
  return key;
}

static long total(const std::vector<int>& a) {
  long t = 0;
  for (size_t i = 0; i < a.size(); i++) t += (long)(i + 1) * a[i];
  return t;
}

static bool exception(const std::vector<int>& a) {
  return a.size() == 3 && a[0] == 2 && a[1] == 2 && a[2] == 3;
}

static void show(const std::vector<int>& a) {
  printf("(");
  for (size_t i = 0; i < a.size(); i++) printf("%d%s", a[i], i + 1 < a.size() ? "," : "");
  printf(")");
}

struct BoxResult { long checked = 0, failed = 0, failedN = 0, failedP = 0; };

// Every (a_1..a_n) in [lo, hi]^n, in lexicographic order.
static BoxResult box(int n, int lo, int hi, bool print) {
  BoxResult r;
  std::vector<int> a(n, lo);
  for (;;) {
    bool p = isP(pack(a));
    long t = total(a);
    r.checked++;
    if (!exception(a) && p != (t % 3 == 0)) {
      r.failed++;
      (p ? r.failedP : r.failedN)++;
      if (print) {
        printf("FAIL n=%d a=", n);
        show(a);
        printf(" total=%ld mod3=%ld outcome=%s\n", t, t % 3, p ? "P" : "N");
      }
    }
    int i = n - 1;
    while (i >= 0 && a[i] == hi) a[i--] = lo;
    if (i < 0) break;
    a[i]++;
  }
  if (print)
    printf("box n=%d a_i in [%d,%d]: positions=%ld failures=%ld (N with total = 0 mod 3: %ld, "
           "P with total != 0 mod 3: %ld) memo=%zu\n",
           n, lo, hi, r.checked, r.failed, r.failedN, r.failedP, memo.used);
  return r;
}

static int ci() {
  N = 7;
  bool ok = true;
  struct Row { std::vector<int> a; long total; bool isP; };
  const Row rows[] = {{{2, 2, 2, 2, 2, 2, 3}, 63, false},
                      {{2, 2, 2, 2, 2, 2, 4}, 70, true},
                      {{2, 2, 2, 2, 2, 3, 3}, 69, false},
                      {{2, 2, 2, 2, 2, 3, 4}, 76, true},
                      {{0, 2, 2, 2, 2, 2, 3}, 61, true}};
  for (const Row& r : rows) {
    bool p = isP(pack(r.a));
    printf("counts ");
    show(r.a);
    printf(" total=%ld outcome=%s\n", total(r.a), p ? "P" : "N");
    ok &= p == r.isP && total(r.a) == r.total;
  }
  BoxResult b7 = box(7, 2, 4, true);
  ok &= b7.checked == 2187 && b7.failed == 15;
  memo = Memo();
  N = 6;
  BoxResult b6 = box(6, 2, 8, true);
  ok &= b6.checked == 117649 && b6.failed == 0;
  printf(ok ? "OK: all expected values reproduced\n" : "MISMATCH with the expected values\n");
  return ok ? 0 : 1;
}

// Conjecture 2.2 of the paper (Version B) says that if a_n >= 2n - 4, the outcome depends only
// on the parities of a_1..a_{n-1}.  MathDB post 374892: with n = 7 and a_7 = 10, the first two
// positions below have the same parities but different outcomes.
static int versionB() {
  N = 7;
  bool ok = true;
  struct Row { std::vector<int> a; bool isP; };
  const Row rows[] = {{{0, 1, 0, 0, 0, 0, 10}, true},
                      {{0, 1, 0, 0, 0, 4, 10}, false},
                      {{0, 1, 0, 0, 0, 4, 11}, true}};
  for (const Row& r : rows) {
    bool p = isPB(pack(r.a));
    printf("Version B counts ");
    show(r.a);
    printf(" outcome=%s\n", p ? "P" : "N");
    ok &= p == r.isP;
  }
  printf(ok ? "OK: all expected values reproduced\n" : "MISMATCH with the expected values\n");
  return ok ? 0 : 1;
}

int main(int argc, char** argv) {
  if (argc == 2 && !strcmp(argv[1], "--ci")) return ci();
  if (argc == 2 && !strcmp(argv[1], "--version-b")) return versionB();
  if (argc == 5 && !strcmp(argv[1], "box")) {
    int n = atoi(argv[2]), lo = atoi(argv[3]), hi = atoi(argv[4]);
    if (n < 1 || n > 10 || lo < 0 || hi < lo) return 2;
    N = n;
    box(n, lo, hi, true);
    return 0;
  }
  if (argc >= 3 && !strcmp(argv[1], "outcome")) {
    std::vector<int> a;
    for (int i = 2; i < argc; i++) a.push_back(atoi(argv[i]));
    N = (int)a.size();
    printf("counts ");
    show(a);
    printf(" total=%ld outcome=%s\n", total(a), isP(pack(a)) ? "P" : "N");
    return 0;
  }
  fprintf(stderr, "usage: oooc_counts --ci | box n lo hi | outcome a_1 ... a_n | --version-b\n");
  return 2;
}
