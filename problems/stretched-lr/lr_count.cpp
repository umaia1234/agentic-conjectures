// Exact Littlewood--Richardson coefficient counter (row-by-row LR tableau DP).
//
// c^outer_{inner,content} is the number of LR tableaux of skew shape
// outer/inner and content `content`.  Row i of such a tableau contains only
// labels 1..i, so a tableau is the lower-triangular matrix a[i][j] = number of
// labels j in row i.  The DP processes rows top to bottom.  Its state after
// row i is (cumulative content C[0..], prefix sums S_i of row i); this is
// exactly what the next row's column-strictness and lattice-word inequalities
// read.  Counts are unsigned 128-bit with overflow detection.  This code does
// not share any logic with lrcalc or with Normaliz.
//
// Build:  c++ -O2 -std=c++17 -shared -fPIC lr_count.cpp -o liblrcount.so
//         c++ -O2 -std=c++17 -DLR_COUNT_MAIN lr_count.cpp -o lr_count
// CLI:    ./lr_count OUTER INNER CONTENT [STRETCH]   (comma-separated parts)

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

namespace {

typedef unsigned __int128 u128;

const int MAXN = 8;
const size_t MAX_TABLE = size_t(1) << 26;  // entries per hash table (~2 GiB)

enum Status { OK = 0, BAD_INPUT = 1, OVERFLOW_COUNT = 2, CAPACITY = 3 };

// Number of search-tree nodes visited (a deterministic cost measure).
thread_local unsigned long long g_work = 0;

struct Table {
  std::vector<u128> keys;
  std::vector<u128> vals;
  std::vector<uint8_t> used;
  size_t mask = 0, count = 0;
  bool overflow = false, capacity = false;

  explicit Table(size_t cap = 64) { reset(cap); }
  void reset(size_t cap) {
    keys.assign(cap, 0);
    vals.assign(cap, 0);
    used.assign(cap, 0);
    mask = cap - 1;
    count = 0;
  }
  static size_t hash(u128 k) {
    uint64_t x = uint64_t(k) ^ (uint64_t(k >> 64) * 0x9E3779B97F4A7C15ULL);
    x ^= x >> 31;
    x *= 0xBF58476D1CE4E5B9ULL;
    x ^= x >> 29;
    return size_t(x);
  }
  void grow() {
    if (2 * (mask + 1) > MAX_TABLE) {
      capacity = true;
      return;
    }
    std::vector<u128> ok = std::move(keys), ov = std::move(vals);
    std::vector<uint8_t> ou = std::move(used);
    reset(2 * ok.size());
    for (size_t i = 0; i < ok.size(); ++i)
      if (ou[i]) add(ok[i], ov[i]);
  }
  void add(u128 key, u128 val) {
    if (capacity) return;
    if (2 * (count + 1) > mask + 1) {
      grow();
      if (capacity) return;
    }
    size_t h = hash(key) & mask;
    while (used[h] && keys[h] != key) h = (h + 1) & mask;
    if (!used[h]) {
      used[h] = 1;
      keys[h] = key;
      vals[h] = val;
      ++count;
    } else {
      u128 s = vals[h] + val;
      if (s < val) overflow = true;
      vals[h] = s;
    }
  }
};

struct Problem {
  int n = 0, m = 0;          // rows of outer, number of labels (= len(content))
  int lam[MAXN], nu[MAXN], r[MAXN], mu[MAXN];
  long suffix[MAXN + 1];     // suffix[i] = r[i] + ... + r[n-1]
  // lb[i][v]: lower bound on the number of labels < v in row i.  A cell of
  // row i with q skew cells below it in its column needs a label <= m-1-q.
  int lb[MAXN][MAXN + 1];
  // minC[i][k]: lower bound on the count of label k after row i, from the
  // emit() conditions (2) and (3) below; applied early inside the row search.
  int minC[MAXN][MAXN];
  int bits = 0;              // bits per packed value
  u128 total = 0;
  bool overflow = false;
};

inline int labels_in_row(const Problem& P, int i) { return (i < P.m ? i : P.m - 1) + 1; }

// Packed state after row i: C[0..L-1] then S[1..L-1] where L = labels_in_row(i).
struct State {
  int C[MAXN];
  int S[MAXN + 1];  // S[k] = sum_{j<k} a[i][j]
};

u128 pack(const Problem& P, int L, const int* C, const int* S) {
  u128 key = 0;
  for (int j = 0; j < L; ++j) key = (key << P.bits) | u128(C[j]);
  for (int k = 1; k < L; ++k) key = (key << P.bits) | u128(S[k]);
  return key;
}

void unpack(const Problem& P, int L, u128 key, int* C, int* S) {
  const u128 mask = (u128(1) << P.bits) - 1;
  for (int k = L - 1; k >= 1; --k) {
    S[k] = int(key & mask);
    key >>= P.bits;
  }
  for (int j = L - 1; j >= 0; --j) {
    C[j] = int(key & mask);
    key >>= P.bits;
  }
}

// Enumerate the admissible row i+1 given the state of row i.
struct Expander {
  Problem* P;
  int row;          // index of the new row
  int Lold, Lnew;   // labels in previous / new row
  int d;            // lam[row-1] - lam[row]
  const int* C;     // cumulative content after previous row (length >= Lnew, zero padded)
  const int* Sold;  // prefix sums of previous row, S[k] for k = 0..Lold
  u128 mult;
  bool last;
  Table* out;
  int a[MAXN];
  int Snew[MAXN + 1];
  int Cnew[MAXN];

  int sold(int k) const { return k <= Lold ? Sold[k] : Sold[Lold]; }

  void emit() {
    if (last) {
      u128 s = P->total + mult;
      if (s < mult) P->overflow = true;
      P->total = s;
      return;
    }
    // Necessary conditions for completing the tableau in rows row+1..n-1.
    const Problem& Q = *P;
    // (1) Labels >= j can only be placed in rows >= j.
    long need = 0;
    for (int j = Q.m - 1; j >= 0; --j) {
      need += Q.mu[j] - Cnew[j];
      if (need > Q.suffix[j > row + 1 ? j : row + 1]) return;
    }
    // (2) Lattice chain: mu_k = C^(n-1)_k <= C^(n-2)_(k-1) <= ... <= C^(row)_(k-s),
    //     s = n-1-row, so the current count of label l is at least mu_(l+s).
    int s = Q.n - 1 - row;
    for (int l = 0; l + s < Q.m; ++l)
      if (Cnew[l] < Q.mu[l + s]) return;
    // (3) Column strictness: a label occurs at most once per column, and the
    //     future cells of label j lie in columns lam_(n-1)+1..nu_(max(row+1,j)).
    for (int j = 0; j < Q.m; ++j) {
      int first = j > row + 1 ? j : row + 1;
      if (Q.mu[j] - Cnew[j] > Q.nu[first] - Q.lam[Q.n - 1]) return;
    }
    out->add(pack(*P, Lnew, Cnew, Snew), mult);
  }

  void go(int k) {
    ++g_work;
    const Problem& Q = *P;
    int rnew = Q.r[row];
    if (k == Lnew - 1) {
      int v = rnew - Snew[k];
      if (v < 0) return;
      if (rnew > d + sold(k)) return;                // column strictness
      if (k >= 1 && C[k] + v > C[k - 1]) return;     // lattice word
      if (C[k] + v > Q.mu[k]) return;                // content
      a[k] = v;
      Snew[k + 1] = rnew;
      Cnew[k] = C[k] + v;
      emit();
      return;
    }
    int hi = rnew - Snew[k];
    int b = d + sold(k) - Snew[k];
    if (b < hi) hi = b;
    b = Q.mu[k] - C[k];
    if (b < hi) hi = b;
    if (k >= 1) {
      b = C[k - 1] - C[k];
      if (b < hi) hi = b;
    }
    int lo = Q.lb[row][k + 1] - Snew[k];
    b = Q.minC[row][k] - C[k];
    if (b > lo) lo = b;
    for (int v = lo > 0 ? lo : 0; v <= hi; ++v) {
      a[k] = v;
      Snew[k + 1] = Snew[k] + v;
      Cnew[k] = C[k] + v;
      go(k + 1);
    }
  }
};

int count_lr(int n, const int* outer, const int* inner, const int* content, u128* result) {
  *result = 0;
  if (n < 1 || n > MAXN) return BAD_INPUT;
  Problem P;
  P.n = n;
  int nu[MAXN];
  long so = 0, si = 0, sc = 0;
  for (int i = 0; i < n; ++i) {
    nu[i] = outer[i];
    P.lam[i] = inner[i];
    P.mu[i] = content[i];
    if (nu[i] < 0 || P.lam[i] < 0 || P.mu[i] < 0) return BAD_INPUT;
    if (i && (nu[i] > nu[i - 1] || P.lam[i] > P.lam[i - 1] || P.mu[i] > P.mu[i - 1]))
      return BAD_INPUT;
    so += nu[i];
    si += P.lam[i];
    sc += P.mu[i];
  }
  if (so != si + sc) return OK;  // coefficient is zero
  for (int i = 0; i < n; ++i) {
    P.nu[i] = nu[i];
    P.r[i] = nu[i] - P.lam[i];
    if (P.r[i] < 0) return OK;  // inner not contained in outer
  }
  P.suffix[n] = 0;
  for (int i = n - 1; i >= 0; --i) P.suffix[i] = P.suffix[i + 1] + P.r[i];
  P.m = 0;
  while (P.m < n && P.mu[P.m] > 0) ++P.m;
  for (int i = 0; i < n; ++i) {
    for (int v = 0; v <= MAXN; ++v) P.lb[i][v] = 0;
    for (int v = 0; v < P.m; ++v) {
      int c = P.lam[i] + 1;  // first column c (1-based) with q(c) <= m-1-v
      for (; c <= nu[i]; ++c) {
        int q = 0;
        for (int k = i + 1; k < n; ++k)
          if (P.lam[k] < c && c <= nu[k]) ++q;
        if (q <= P.m - 1 - v) break;
      }
      int bound = c - P.lam[i] - 1;
      P.lb[i][v] = bound < P.r[i] ? bound : P.r[i];
    }
    if (P.lb[i][0] > 0) return OK;  // a column would need more than m labels
  }
  for (int i = 0; i < n; ++i)
    for (int k = 0; k < MAXN; ++k) {
      int lo = 0;
      if (k < P.m && i < n - 1) {
        int s = n - 1 - i;
        if (k + s < P.m) lo = P.mu[k + s];
        int first = k > i + 1 ? k : i + 1;
        int w = P.mu[k] - (nu[first] - P.lam[n - 1]);
        if (w > lo) lo = w;
      }
      P.minC[i][k] = lo;
    }
  if (P.m == 0) {
    *result = 1;  // outer == inner here
    return OK;
  }
  int maxv = int(so);
  P.bits = 1;
  while ((1 << P.bits) <= maxv) ++P.bits;
  if (n >= 2) {
    int L = labels_in_row(P, n - 2);
    if ((2 * L - 1) * P.bits > 128) return CAPACITY;
  }

  // Row 0: only label 0.
  if (P.r[0] > P.mu[0]) return OK;
  int C0[MAXN] = {0};
  int S0[MAXN + 1] = {0};
  C0[0] = P.r[0];
  S0[1] = P.r[0];
  if (n == 1) {
    *result = (P.m == 1 && P.r[0] == P.mu[0]) ? 1 : 0;
    return OK;
  }
  Table cur(64), nxt(64);
  cur.add(pack(P, 1, C0, S0), 1);
  for (int row = 1; row < n; ++row) {
    bool last = (row == n - 1);
    nxt.reset(64);
    int Lold = labels_in_row(P, row - 1), Lnew = labels_in_row(P, row);
    for (size_t h = 0; h <= cur.mask; ++h) {
      if (!cur.used[h]) continue;
      State s;
      std::memset(&s, 0, sizeof s);
      unpack(P, Lold, cur.keys[h], s.C, s.S);
      s.S[0] = 0;
      s.S[Lold] = P.r[row - 1];  // unpack wrote S[1..Lold-1]; S[Lold] is the row sum
      Expander e;
      e.P = &P;
      e.row = row;
      e.Lold = Lold;
      e.Lnew = Lnew;
      e.d = P.lam[row - 1] - P.lam[row];
      e.C = s.C;
      e.Sold = s.S;
      e.mult = cur.vals[h];
      e.last = last;
      e.out = &nxt;
      std::memset(e.Cnew, 0, sizeof e.Cnew);
      e.Snew[0] = 0;
      e.go(0);
      if (P.overflow || nxt.overflow) return OVERFLOW_COUNT;
      if (nxt.capacity) return CAPACITY;
    }
    if (last) break;
    std::swap(cur, nxt);
    if (cur.count == 0) return OK;
  }
  if (P.overflow) return OVERFLOW_COUNT;
  *result = P.total;
  return OK;
}

std::string to_decimal(u128 v) {
  if (v == 0) return "0";
  std::string s;
  while (v) {
    s.push_back(char('0' + int(v % 10)));
    v /= 10;
  }
  return std::string(s.rbegin(), s.rend());
}

}  // namespace

extern "C" {

// Writes c^outer_{inner,content} (stretched by `stretch`) as a decimal string.
// All three arrays have length n and are zero padded.  Returns 0 on success,
// 1 on invalid input, 2 on 128-bit overflow, 3 on a capacity limit.
int lr_count_dec(int n, const int* outer, const int* inner, const int* content, int stretch,
                 char* out, int outlen) {
  if (n < 1 || n > MAXN || stretch < 0 || outlen < 41) return BAD_INPUT;
  int o[MAXN], i1[MAXN], c[MAXN];
  for (int i = 0; i < n; ++i) {
    o[i] = outer[i] * stretch;
    i1[i] = inner[i] * stretch;
    c[i] = content[i] * stretch;
  }
  u128 v = 0;
  int status = count_lr(n, o, i1, c, &v);
  std::string s = status == OK ? to_decimal(v) : std::string("-1");
  std::snprintf(out, size_t(outlen), "%s", s.c_str());
  return status;
}

// Values for stretches t = first..last, written comma separated.  Stops after
// the first t at which the running sum of values exceeds `limit` (no limit if
// limit <= 0).  Returns the number of values written, or -status on error.
// If `work` is not null it receives the number of search nodes visited.
int lr_count_series(int n, const int* outer, const int* inner, const int* content, int first,
                    int last, long long limit, char* out, int outlen,
                    unsigned long long* work) {
  if (n < 1 || n > MAXN || first < 0 || last < first - 1 || outlen < 64) return -BAD_INPUT;
  g_work = 0;
  std::string text;
  u128 running = 0;
  int written = 0;
  for (int t = first; t <= last; ++t) {
    int o[MAXN], i1[MAXN], c[MAXN];
    for (int i = 0; i < n; ++i) {
      o[i] = outer[i] * t;
      i1[i] = inner[i] * t;
      c[i] = content[i] * t;
    }
    u128 v = 0;
    int status = count_lr(n, o, i1, c, &v);
    if (status != OK) return -status;
    std::string s = to_decimal(v);
    if (text.size() + s.size() + 2 > size_t(outlen)) return -CAPACITY;
    if (written) text.push_back(',');
    text += s;
    ++written;
    running += v;
    if (running < v) return -OVERFLOW_COUNT;
    if (limit > 0 && running > u128(limit)) break;
  }
  std::snprintf(out, size_t(outlen), "%s", text.c_str());
  if (work) *work = g_work;
  return written;
}
}

#ifdef LR_COUNT_MAIN
static int parse(const char* text, int* parts, int n) {
  for (int i = 0; i < n; ++i) parts[i] = 0;
  int k = 0;
  const char* p = text;
  while (*p) {
    if (k >= n) return -1;
    parts[k++] = int(std::strtol(p, const_cast<char**>(&p), 10));
    if (*p == ',') ++p;
  }
  return k;
}

int main(int argc, char** argv) {
  if (argc < 4) {
    std::fprintf(stderr, "usage: %s OUTER INNER CONTENT [STRETCH]\n", argv[0]);
    return 1;
  }
  int o[MAXN], in[MAXN], c[MAXN];
  int n = parse(argv[1], o, MAXN);
  if (n < 1 || parse(argv[2], in, MAXN) < 0 || parse(argv[3], c, MAXN) < 0) return 1;
  for (int i = n; i < MAXN; ++i)
    if (in[i] || c[i]) {
      std::puts("0");
      return 0;
    }
  int t = argc > 4 ? std::atoi(argv[4]) : 1;
  char buf[64];
  int status = lr_count_dec(n, o, in, c, t, buf, sizeof buf);
  if (status) {
    std::fprintf(stderr, "error status %d\n", status);
    return 2;
  }
  std::puts(buf);
  return 0;
}
#endif
