// OEIS A076141: independent second single-occurrence enumerator.
//
// Written independently of a076141_occ_closed.cpp: no square roots are taken.
// For an odd n of bit length L, an occurrence at bit position t means
//     F(n) = n^2 - 2^t n - (n^2 mod 2^t) == 0  (mod 2^(t+L)).
//
//   bottom: enumerate r = n mod 2^(t-1), put B = r^2 mod 2^t, and determine
//           bits t-1, ..., L-1 of n one at a time by Hensel lifting
//           (F'(n) = 2n - 2^t has 2-adic valuation 1, so each bit is forced by
//           F == 0 modulo the next power of two).  Since F(2^t - n) = F(n), the
//           lift of -r is (2^t - n) mod 2^L, so only the 2^(t-3) odd r < 2^(t-2)
//           are lifted and each lift yields two candidates.
//   top:    enumerate the prefix A = floor(n^2 / 2^(t+L)); the occurrence
//           forces f(n) = n^2 - 2^t n into [A 2^(t+L), A 2^(t+L) + 2^t), so n is
//           n0(A) = least n >= 2^(L-1) with f(n) >= A 2^(t+L) (n0(A) + 1 is
//           also tested).  n0(A) is found by an exact galloping search started
//           from the quadratic extrapolation of n0(A-1), n0(A-2), n0(A-3).
//
// Every candidate is checked against the exact square (4 x 64-bit limbs), and
// every n found has all of its occurrences counted directly.  The position
// plans "full" and "reduced" are the same as in a076141_occ_closed.cpp, so the
// "OCC L t n count" lines and the candidate counts of the two programs must be
// identical.
//
// Usage: a076141_occ_hensel <Lmin> <Lmax> <full|reduced> [threads]

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <thread>
#include <vector>

typedef std::uint64_t limb;
typedef unsigned __int128 wide;

// ---------------------------------------------------------------- big numbers
struct Big {
  limb w[4];  // little-endian 64-bit limbs, value < 2^256
};

static Big big_zero() {
  Big b = {{0, 0, 0, 0}};
  return b;
}

// a * a for a < 2^128, schoolbook on two 64-bit limbs.
static Big big_square(wide a) {
  const limb x[2] = {static_cast<limb>(a), static_cast<limb>(a >> 64)};
  Big r = big_zero();
  for (int i = 0; i < 2; ++i) {
    limb carry = 0;
    for (int j = 0; j < 2; ++j) {
      const wide cur = static_cast<wide>(x[i]) * x[j] + r.w[i + j] + carry;
      r.w[i + j] = static_cast<limb>(cur);
      carry = static_cast<limb>(cur >> 64);
    }
    r.w[i + 2] = carry;
  }
  return r;
}

static Big big_sub(const Big& a, const Big& b) {  // requires a >= b
  Big r;
  limb borrow = 0;
  for (int i = 0; i < 4; ++i) {
    const limb x = a.w[i], y = b.w[i];
    r.w[i] = x - y - borrow;
    borrow = (x < y || (x == y && borrow)) ? 1 : 0;
  }
  return r;
}

static bool big_less(const Big& a, const Big& b) {
  for (int i = 3; i >= 0; --i)
    if (a.w[i] != b.w[i]) return a.w[i] < b.w[i];
  return false;
}

static Big big_shifted(wide a, int k) {  // a * 2^k, no overflow assumed
  Big r = big_zero();
  const limb x[2] = {static_cast<limb>(a), static_cast<limb>(a >> 64)};
  const int ls = k / 64, bs = k % 64;
  for (int i = 0; i < 2; ++i) {
    if (i + ls < 4) r.w[i + ls] |= (bs ? (x[i] << bs) : x[i]);
    if (bs && i + ls + 1 < 4) r.w[i + ls + 1] |= x[i] >> (64 - bs);
  }
  return r;
}

static limb limb_at(const Big& a, int i) { return (i >= 0 && i < 4) ? a.w[i] : 0; }

// bits [s, s+len) of a, as a number (len <= 128)
static wide big_bits(const Big& a, int s, int len) {
  const int ls = s / 64, bs = s % 64;
  limb lo = limb_at(a, ls) >> bs, hi = limb_at(a, ls + 1) >> bs;
  if (bs) {
    lo |= limb_at(a, ls + 1) << (64 - bs);
    hi |= limb_at(a, ls + 2) << (64 - bs);
  }
  wide v = (static_cast<wide>(hi) << 64) | lo;
  if (len < 128) v &= (static_cast<wide>(1) << len) - 1;
  return v;
}

static int big_bitlen(const Big& a) {
  for (int i = 3; i >= 0; --i)
    if (a.w[i]) return 64 * i + 64 - __builtin_clzll(a.w[i]);
  return 0;
}

static int bits_of(wide x) {
  int b = 0;
  while (x) { ++b; x >>= 1; }
  return b;
}

static bool occurs_at(wide n, int L, int t) { return big_bits(big_square(n), t, L) == n; }

static int occurrence_count(wide n) {
  const int L = bits_of(n);
  const Big sq = big_square(n);
  const int M = big_bitlen(sq);
  int c = 0;
  for (int s = 0; s + L <= M; ++s)
    if (big_bits(sq, s, L) == n) ++c;
  return c;
}

// ------------------------------------------------------------------- methods
// Bottom: lift r = n mod 2^(t-1) to n mod 2^L; test n and (2^t - n) mod 2^L.
static int bottom_pair(int L, int t, wide r, wide out[2]) {
  // F(n) = n^2 - 2^t n - B with B = r^2 mod 2^t.  For n_j = n mod 2^j
  // (t-1 <= j <= L) write F(n_j) = 2^(j+1) G_j.  Since
  //   F(n_j + 2^j) = F(n_j) + 2^(j+1) D_j,  D_j = n_j + 2^(j-1) - 2^(t-1) (odd),
  // bit j of n is G_j mod 2 and G_(j+1) = (G_j + bit * D_j) / 2.  G and D are
  // kept modulo 2^128; after s <= L - t + 1 < 128 halvings G is still exact
  // modulo 2^(128 - s), which covers the bit 0 that is used.
  wide n = r;
  wide G = ((r * r) >> t) - r;                       // F(r) / 2^t
  wide P = static_cast<wide>(1) << (t - 2);          // 2^(j-1)
  wide D = r - P;                                    // r + 2^(t-2) - 2^(t-1)
  for (int j = t - 1; j < L; ++j) {
    const wide take = -(G & 1);                      // all ones iff bit j is 1
    const wide add = (P << 1) & take;                // bit * 2^j
    G = (G + (D & take)) >> 1;
    n += add;
    D += P + add;
    P <<= 1;
  }
  const wide maskL = (static_cast<wide>(1) << L) - 1;
  const wide cand[2] = {n, ((static_cast<wide>(1) << t) - n) & maskL};
  int k = 0;
  for (wide c : cand)
    if (((c >> (L - 1)) & 1) && occurs_at(c, L, t)) out[k++] = c;  // bit length L
  return k;
}

static Big f_value(wide n, int t) { return big_sub(big_square(n), big_shifted(n, t)); }

// Least n in [lowest, none) with f(n) >= target, or none; exact galloping
// search from the guess g (any value in [lowest, none)).
static wide least_at_least(int t, const Big& target, wide lowest, wide none, wide g) {
  auto ge = [&](wide n) { return !big_less(f_value(n, t), target); };
  wide lo, hi;  // invariant for the final bisection: f(lo) < target <= f(hi)
  if (ge(g)) {
    hi = g;
    for (wide step = 1;; step <<= 1) {
      if (hi - lowest <= step) {
        if (ge(lowest)) return lowest;
        lo = lowest;
        break;
      }
      if (!ge(hi - step)) {
        lo = hi - step;
        break;
      }
      hi -= step;
    }
  } else {
    lo = g;
    for (wide step = 1;; step <<= 1) {
      if (none - 1 - lo <= step) {
        if (!ge(none - 1)) return none;
        hi = none - 1;
        break;
      }
      if (ge(lo + step)) {
        hi = lo + step;
        break;
      }
      lo += step;
    }
  }
  while (hi - lo > 1) {
    const wide mid = lo + (hi - lo) / 2;
    if (ge(mid))
      hi = mid;
    else
      lo = mid;
  }
  return hi;
}

// Top: process the consecutive prefixes A = first .. last-1 of one thread.
static void top_range(int L, int t, wide first, wide last, std::vector<wide>* hits) {
  typedef __int128 swide;
  const wide lowest = static_cast<wide>(1) << (L - 1), none = static_cast<wide>(1) << L;
  wide prev[3] = {0, 0, 0};  // n0(A-1), n0(A-2), n0(A-3)
  int have = 0;
  for (wide A = first; A < last; ++A) {
    const Big target = big_shifted(A, t + L);
    swide guess = have == 0 ? static_cast<swide>(lowest)
                  : have < 3 ? static_cast<swide>(prev[0])
                             : 3 * static_cast<swide>(prev[0]) -
                                   3 * static_cast<swide>(prev[1]) +
                                   static_cast<swide>(prev[2]);
    if (guess < static_cast<swide>(lowest)) guess = static_cast<swide>(lowest);
    if (guess > static_cast<swide>(none - 1)) guess = static_cast<swide>(none - 1);
    const wide n0 = least_at_least(t, target, lowest, none, static_cast<wide>(guess));
    if (n0 == none) break;  // f(2^L - 1) < A 2^(t+L): no n for this or larger A
    prev[2] = prev[1];
    prev[1] = prev[0];
    prev[0] = n0;
    if (have < 3) ++have;
    for (wide n = n0; n < n0 + 2 && n < none; ++n) {
      if ((n & 1) == 0) continue;
      // for n < 2^L: occurrence at t <=> A 2^(t+L) <= f(n) < A 2^(t+L) + 2^t
      const Big f = f_value(n, t);
      if (big_less(f, target)) continue;
      if (big_bitlen(big_sub(f, target)) > t) continue;  // f - A 2^(t+L) >= 2^t
      if (occurs_at(n, L, t)) hits->push_back(n);
    }
  }
}

// ---------------------------------------------------------------------- main
static std::string to_dec(wide x) {
  char buf[64];
  int p = 63;
  buf[p] = 0;
  do { buf[--p] = static_cast<char>('0' + static_cast<int>(x % 10)); x /= 10; } while (x);
  return std::string(buf + p);
}

struct Hit {
  int t;
  wide n;
  bool operator<(const Hit& o) const { return t != o.t ? t < o.t : n < o.n; }
  bool operator==(const Hit& o) const { return t == o.t && n == o.n; }
};

int main(int argc, char** argv) {
  if (argc < 4) {
    std::fprintf(stderr, "usage: %s Lmin Lmax full|reduced [threads]\n", argv[0]);
    return 2;
  }
  const int Lmin = std::atoi(argv[1]), Lmax = std::atoi(argv[2]);
  const std::string mode = argv[3];
  const int T = argc > 4 ? std::atoi(argv[4]) : 4;
  if (Lmin < 3 || Lmax > 120 || Lmin > Lmax || T < 1 || (mode != "full" && mode != "reduced")) {
    std::fprintf(stderr, "need 3 <= Lmin <= Lmax <= 120, mode full|reduced\n");
    return 2;
  }
  wide all_bottom = 0, all_top = 0;
  long long all_occ = 0, bad_n = 0;
  for (int L = Lmin; L <= Lmax; ++L) {
    int bottom_last, top_first;
    if (mode == "full") {
      bottom_last = std::min((L + 2) / 2, L - 1);
      top_first = bottom_last + 1;
    } else {
      const int sigma = L / 3 + 1;
      int tau = 2 * sigma + 2;
      const int half = (L + sigma + 1 + 1) / 2;  // ceil((L + sigma + 1) / 2)
      if (half > tau) tau = half;
      bottom_last = std::min(sigma, L - 1);
      top_first = std::max(tau, bottom_last + 1);
    }
    std::vector<Hit> hits;
    wide cnt_bottom = 0, cnt_top = 0;
    for (int t = 3; t <= L - 1; ++t) {
      const bool bottom = t <= bottom_last;
      if (!bottom && t < top_first) continue;
      wide first, last;  // candidate range [first, last)
      if (bottom) {
        first = 0;  // r = 2 i + 1 < 2^(t-2), i < 2^(t-3)
        last = static_cast<wide>(1) << (t - 3);
      } else {
        // A runs over floor(n^2 / 2^(t+L)) for 2^(L-1) <= n < 2^L
        const wide top = (static_cast<wide>(1) << L) - 1;
        last = big_bits(big_square(top), t + L, L - t + 1) + 1;
        first = (2 * L - 2 >= t + L) ? (static_cast<wide>(1) << (2 * L - 2 - t - L)) : 0;
      }
      const wide total = last - first;
      std::vector<std::vector<wide>> part(T);
      std::vector<std::thread> pool;
      for (int id = 0; id < T; ++id) {
        pool.emplace_back([&, id]() {
          const wide a = first + total * id / T, b = first + total * (id + 1) / T;
          if (bottom) {
            for (wide i = a; i < b; ++i) {
              wide out[2];
              const int k = bottom_pair(L, t, 2 * i + 1, out);
              for (int j = 0; j < k; ++j) part[id].push_back(out[j]);
            }
          } else {
            top_range(L, t, a, b, &part[id]);
          }
        });
      }
      for (auto& th : pool) th.join();
      for (auto& p : part)
        for (wide n : p) hits.push_back({t, n});
      if (bottom)
        cnt_bottom += total;
      else
        cnt_top += total;
    }
    std::sort(hits.begin(), hits.end());
    hits.erase(std::unique(hits.begin(), hits.end()), hits.end());
    std::vector<wide> distinct;
    for (auto& h : hits) distinct.push_back(h.n);
    std::sort(distinct.begin(), distinct.end());
    distinct.erase(std::unique(distinct.begin(), distinct.end()), distinct.end());
    int maxc = 0;
    for (wide n : distinct) {
      const int c = occurrence_count(n);
      if (c > maxc) maxc = c;
      if (c >= 2) {
        ++bad_n;
        std::printf("COUNTEREXAMPLE L=%d n=%s count=%d\n", L, to_dec(n).c_str(), c);
      }
    }
    std::printf("L=%d mode=%s bottom_t=3..%d top_t=%d..%d cand_bottom=%s cand_top=%s "
                "occurrences=%zu distinct_n=%zu max_count=%d\n",
                L, mode.c_str(), bottom_last, top_first, L - 1, to_dec(cnt_bottom).c_str(),
                to_dec(cnt_top).c_str(), hits.size(), distinct.size(), maxc);
    for (auto& h : hits)
      std::printf("OCC %d %d %s %d\n", L, h.t, to_dec(h.n).c_str(), occurrence_count(h.n));
    std::fflush(stdout);
    all_bottom += cnt_bottom;
    all_top += cnt_top;
    all_occ += static_cast<long long>(hits.size());
  }
  std::printf("SUMMARY L=%d..%d mode=%s cand_bottom=%s cand_top=%s occurrences=%lld "
              "counterexamples=%lld\n",
              Lmin, Lmax, mode.c_str(), to_dec(all_bottom).c_str(), to_dec(all_top).c_str(),
              all_occ, bad_n);
  return bad_n ? 1 : 0;
}
