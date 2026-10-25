// OEIS A076141: list every occurrence of an odd n (bit length L) in n^2.
//
// Primary single-occurrence enumerator ("closed form").  For an odd n of bit
// length L and a window position t (bit 0 = least significant bit), the
// occurrence "bits [t, t+L) of n^2 equal n" is found in one of two ways:
//
//   bottom: B = n^2 mod 2^t is one of the 2^(t-3) residues = 1 (mod 8), and
//           x = n - 2^(t-1) is the unique square root of B + 4^(t-1) modulo
//           2^(L+2) in [0, 2^L).  Computed by 2-adic inverse-square-root Newton.
//   top:    A = floor(n^2 / 2^(t+L)); then n is n_A or n_A + 1 with
//           n_A = 2^(t-1) + ceil(sqrt(A*2^(t+L) + 4^(t-1))).
//
// Every candidate is re-checked by extracting the window from the exact
// square, and every n found has all of its occurrences counted directly.
// See DETAILS.md for the completeness argument and for the position plans:
//
//   full:    every position 3 <= t <= L-1 (bottom iff t <= floor((L+2)/2)).
//   reduced: positions 3..sigma (bottom) and tau..L-1 (top), with
//            sigma = floor(L/3)+1, tau = max(2*sigma+2, ceil((L+sigma+1)/2));
//            complete for pairs by the Lean lemmas of OeisA076141.lean.
//   both:    every position by both methods; the two sets must coincide.
//
// Usage: a076141_occ_closed <Lmin> <Lmax> <full|reduced|both> [threads]
// Output: per L, one summary line followed by its "OCC L t n count" lines;
// finally a SUMMARY line.
// Exit status 0 iff no n with two or more occurrences was found and all
// internal consistency checks passed.

#include <algorithm>
#include <atomic>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <thread>
#include <utility>
#include <vector>

using u64 = std::uint64_t;
using u128 = unsigned __int128;

struct U256 {
  u128 hi, lo;
};

static U256 mul128(u128 a, u128 b) {
  const u128 a0 = static_cast<u64>(a), a1 = a >> 64;
  const u128 b0 = static_cast<u64>(b), b1 = b >> 64;
  const u128 p00 = a0 * b0, p01 = a0 * b1, p10 = a1 * b0, p11 = a1 * b1;
  const u128 mid = p01 + p10;
  const u128 carry_mid = (mid < p01) ? (u128{1} << 64) : 0;
  const u128 lo = p00 + (mid << 64);
  const u128 carry_lo = (lo < p00) ? 1 : 0;
  return {p11 + (mid >> 64) + carry_mid + carry_lo, lo};
}

static U256 shl(u128 a, unsigned k) {  // a * 2^k, assumed < 2^256
  if (k == 0) return {0, a};
  if (k < 128) return {a >> (128 - k), a << k};
  if (k < 256) return {a << (k - 128), 0};
  return {0, 0};
}

static U256 add(U256 a, U256 b) {
  const u128 lo = a.lo + b.lo;
  return {a.hi + b.hi + (lo < a.lo ? 1 : 0), lo};
}

static U256 sub(U256 a, U256 b) {  // assumes a >= b
  return {a.hi - b.hi - (a.lo < b.lo ? 1 : 0), a.lo - b.lo};
}

static int cmp(U256 a, U256 b) {
  if (a.hi != b.hi) return a.hi < b.hi ? -1 : 1;
  if (a.lo != b.lo) return a.lo < b.lo ? -1 : 1;
  return 0;
}

static u128 shr_low(U256 a, unsigned k) {  // (a >> k) mod 2^128
  if (k == 0) return a.lo;
  if (k < 128) return (a.lo >> k) | (a.hi << (128 - k));
  if (k < 256) return a.hi >> (k - 128);
  return 0;
}

static unsigned bitlen128(u128 x) {
  const u64 h = static_cast<u64>(x >> 64);
  if (h) return 128 - __builtin_clzll(h);
  const u64 l = static_cast<u64>(x);
  return l ? 64 - __builtin_clzll(l) : 0;
}

static unsigned bitlen256(U256 x) {
  return x.hi ? 128 + bitlen128(x.hi) : bitlen128(x.lo);
}

static u128 mask(unsigned L) {
  return L >= 128 ? ~u128{0} : ((u128{1} << L) - 1);
}

static double to_double(U256 x) {
  return std::ldexp(static_cast<double>(x.hi), 128) + static_cast<double>(x.lo);
}

// floor(sqrt(x)) for x < 2^254.
static u128 isqrt256(U256 x) {
  double est = std::sqrt(to_double(x));
  if (est >= std::ldexp(1.0, 127)) est = std::ldexp(1.0, 127) - std::ldexp(1.0, 74);
  u128 y = static_cast<u128>(est);
  for (int round = 0; round < 4; ++round) {
    const U256 y2 = mul128(y, y);
    double delta;
    if (cmp(y2, x) <= 0)
      delta = to_double(sub(x, y2)) / (2.0 * static_cast<double>(y) + 1.0);
    else
      delta = -to_double(sub(y2, x)) / (2.0 * static_cast<double>(y) + 1.0);
    if (std::fabs(delta) < 4.0) break;
    const double step = std::floor(delta);
    if (step >= 0)
      y += static_cast<u128>(step);
    else
      y -= static_cast<u128>(-step);
  }
  int guard = 0;
  while (cmp(mul128(y, y), x) > 0) {
    --y;
    if (++guard > 1000) { std::fprintf(stderr, "isqrt256 failed\n"); std::exit(3); }
  }
  while (cmp(mul128(y + 1, y + 1), x) <= 0) {
    ++y;
    if (++guard > 1000) { std::fprintf(stderr, "isqrt256 failed\n"); std::exit(3); }
  }
  return y;
}

static bool window_equals(u128 n, unsigned L, unsigned t) {
  const U256 sq = mul128(n, n);
  return (shr_low(sq, t) & mask(L)) == n;
}

static int count_occurrences(u128 n) {
  const unsigned L = bitlen128(n);
  const U256 sq = mul128(n, n);
  const unsigned M = bitlen256(sq);
  int count = 0;
  for (unsigned s = 0; s + L <= M; ++s)
    if ((shr_low(sq, s) & mask(L)) == n) ++count;
  return count;
}

// Bottom method: candidate n for residue B = n^2 mod 2^t (B = 1 mod 8).
static bool bottom_candidate(unsigned L, unsigned t, u128 B, u128* out) {
  const unsigned K = L + 2;  // work modulo 2^K, K <= 127
  u128 c = B;
  if (2 * t - 2 < 128) c += u128{1} << (2 * t - 2);
  c &= mask(K);
  // y = c^(-1/2) mod 2^126 by Newton: y <- y (3 - c y^2) / 2.
  u128 y = 1;
  for (int it = 0; it < 8; ++it) y = y * ((u128{3} - c * y * y) >> 1);
  u128 x0 = (c * y) & mask(K);
  if (((x0 * x0) & mask(K)) != c) {
    std::fprintf(stderr, "2-adic square root failed L=%u t=%u\n", L, t);
    std::exit(3);
  }
  // Canonical root in [0, 2^L): reduce mod 2^(K-1), then reflect.
  u128 x1 = x0 & mask(K - 1);
  const u128 x = x1 < (u128{1} << L) ? x1 : (u128{1} << (K - 1)) - x1;
  const u128 n = x + (u128{1} << (t - 1));
  if (bitlen128(n) != L || (n & 1) == 0) return false;
  if (!window_equals(n, L, t)) return false;
  *out = n;
  return true;
}

static u128 ceil_sqrt(U256 X) {
  u128 r = isqrt256(X);
  if (cmp(mul128(r, r), X) < 0) ++r;
  return r;
}

// Top method: candidates n_A and n_A + 1.
static int top_candidates(unsigned L, unsigned t, u128 A, u128 out[2]) {
  const U256 X = add(shl(A, t + L), shl(1, 2 * t - 2));
  const u128 nA = (u128{1} << (t - 1)) + ceil_sqrt(X);
  int k = 0;
  for (u128 n = nA; n <= nA + 1; ++n) {
    if (bitlen128(n) != L || (n & 1) == 0) continue;
    if (window_equals(n, L, t)) out[k++] = n;
  }
  return k;
}

struct Range {
  unsigned t;
  bool bottom;
  u128 lo, hi;  // inclusive index range (bottom: B = 8 i + 1; top: A)
};

static std::string dec(u128 x) {
  if (x == 0) return "0";
  std::string s;
  while (x) { s.push_back(char('0' + static_cast<int>(x % 10))); x /= 10; }
  std::reverse(s.begin(), s.end());
  return s;
}

static u128 top_lo(unsigned L, unsigned t) {
  // floor(4^(L-1) / 2^(t+L))
  return (2 * L - 2 >= t + L) ? (u128{1} << (2 * L - 2 - t - L)) : 0;
}

static u128 top_hi(unsigned L, unsigned t) {
  const u128 m = mask(L);
  return shr_low(mul128(m, m), t + L);
}

using Found = std::vector<std::pair<unsigned, u128>>;  // (t, n)

static void run_ranges(unsigned L, const std::vector<Range>& ranges, unsigned threads,
                       Found* found, u128* cand_bottom, u128* cand_top) {
  const u128 CHUNK = u128{1} << 16;
  struct Item { std::size_t r; u128 lo, hi; };
  std::vector<Item> items;
  for (std::size_t r = 0; r < ranges.size(); ++r) {
    for (u128 lo = ranges[r].lo; lo <= ranges[r].hi; lo += CHUNK) {
      u128 hi = lo + CHUNK - 1;
      if (hi > ranges[r].hi) hi = ranges[r].hi;
      items.push_back({r, lo, hi});
      if (hi == ranges[r].hi) break;
    }
  }
  std::atomic<std::size_t> next{0};
  std::vector<Found> local(threads);
  std::vector<u128> cb(threads, 0), ct(threads, 0);
  auto worker = [&](unsigned id) {
    for (;;) {
      const std::size_t k = next.fetch_add(1);
      if (k >= items.size()) break;
      const Item& it = items[k];
      const Range& rg = ranges[it.r];
      for (u128 i = it.lo;; ++i) {
        if (rg.bottom) {
          ++cb[id];
          u128 n;
          if (bottom_candidate(L, rg.t, 8 * i + 1, &n)) local[id].push_back({rg.t, n});
        } else {
          ++ct[id];
          u128 out[2];
          const int c = top_candidates(L, rg.t, i, out);
          for (int j = 0; j < c; ++j) local[id].push_back({rg.t, out[j]});
        }
        if (i == it.hi) break;
      }
    }
  };
  std::vector<std::thread> pool;
  for (unsigned id = 0; id < threads; ++id) pool.emplace_back(worker, id);
  for (auto& th : pool) th.join();
  for (unsigned id = 0; id < threads; ++id) {
    found->insert(found->end(), local[id].begin(), local[id].end());
    *cand_bottom += cb[id];
    *cand_top += ct[id];
  }
  std::sort(found->begin(), found->end());
  found->erase(std::unique(found->begin(), found->end()), found->end());
}

int main(int argc, char** argv) {
  if (argc < 4) {
    std::fprintf(stderr, "usage: %s Lmin Lmax full|reduced|both [threads]\n", argv[0]);
    return 2;
  }
  const unsigned Lmin = std::strtoul(argv[1], nullptr, 10);
  const unsigned Lmax = std::strtoul(argv[2], nullptr, 10);
  const std::string mode = argv[3];
  const unsigned threads = argc > 4 ? std::strtoul(argv[4], nullptr, 10) : 4;
  if (Lmin < 3 || Lmax > 120 || Lmin > Lmax || threads == 0 ||
      (mode != "full" && mode != "reduced" && mode != "both")) {
    std::fprintf(stderr, "need 3 <= Lmin <= Lmax <= 120, mode full|reduced|both\n");
    return 2;
  }
  u128 tot_b = 0, tot_t = 0;
  std::size_t tot_occ = 0, counterexamples = 0;
  for (unsigned L = Lmin; L <= Lmax; ++L) {
    std::vector<Range> ranges, alt;
    unsigned b_hi = 2, t_lo = L;  // bottom positions 3..b_hi, top positions t_lo..L-1
    if (mode == "full" || mode == "both") {
      b_hi = std::min((L + 2) / 2, L - 1);
      t_lo = b_hi + 1;
    } else {
      const unsigned sigma = L / 3 + 1;
      const unsigned tau = std::max(2 * sigma + 2, (L + sigma + 2) / 2);
      b_hi = std::min(sigma, L - 1);
      t_lo = std::max(tau, b_hi + 1);
    }
    for (unsigned t = 3; t <= b_hi; ++t)
      ranges.push_back({t, true, 0, (u128{1} << (t - 3)) - 1});
    for (unsigned t = t_lo; t + 1 <= L; ++t)
      ranges.push_back({t, false, top_lo(L, t), top_hi(L, t)});
    u128 cb = 0, ct = 0;
    Found found;
    run_ranges(L, ranges, threads, &found, &cb, &ct);
    if (mode == "both") {
      // Same positions with the opposite method; the occurrence sets must agree.
      for (unsigned t = 3; t + 1 <= L; ++t) {
        if (t <= b_hi)
          alt.push_back({t, false, top_lo(L, t), top_hi(L, t)});
        else
          alt.push_back({t, true, 0, (u128{1} << (t - 3)) - 1});
      }
      Found found2;
      run_ranges(L, alt, threads, &found2, &cb, &ct);
      if (found2 != found) {
        std::fprintf(stderr, "METHOD MISMATCH at L=%u (%zu vs %zu)\n", L, found.size(),
                     found2.size());
        return 4;
      }
    }
    // Count all occurrences of every n found.
    std::vector<u128> ns;
    for (auto& f : found) ns.push_back(f.second);
    std::sort(ns.begin(), ns.end());
    ns.erase(std::unique(ns.begin(), ns.end()), ns.end());
    int maxc = 0;
    for (u128 n : ns) {
      const int c = count_occurrences(n);
      maxc = std::max(maxc, c);
      if (c >= 2) {
        ++counterexamples;
        std::printf("COUNTEREXAMPLE L=%u n=%s count=%d\n", L, dec(n).c_str(), c);
      }
    }
    std::printf("L=%u mode=%s bottom_t=3..%u top_t=%u..%u cand_bottom=%s cand_top=%s "
                "occurrences=%zu distinct_n=%zu max_count=%d\n",
                L, mode.c_str(), b_hi, t_lo, L - 1, dec(cb).c_str(), dec(ct).c_str(),
                found.size(), ns.size(), maxc);
    for (auto& f : found)
      std::printf("OCC %u %u %s %d\n", L, f.first, dec(f.second).c_str(),
                  count_occurrences(f.second));
    std::fflush(stdout);
    tot_b += cb;
    tot_t += ct;
    tot_occ += found.size();
  }
  std::printf("SUMMARY L=%u..%u mode=%s cand_bottom=%s cand_top=%s occurrences=%zu "
              "counterexamples=%zu\n",
              Lmin, Lmax, mode.c_str(), dec(tot_b).c_str(), dec(tot_t).c_str(), tot_occ,
              counterexamples);
  return counterexamples ? 1 : 0;
}
