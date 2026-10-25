// a056777_search.cpp -- exact exhaustive search for OEIS A056777 / Choudhury-Wei Conjecture 1.1.
//
// For every n in [start, end] it computes phi(n), sigma(n), phi(n+12), sigma(n+12) exactly and
// reports every n with
//     phi(n+12) == phi(n) + 12   and   sigma(n+12) == sigma(n) + 12.
// A prime n satisfies both equations exactly when n + 12 is prime too; such n are only counted
// per block (primehits=), while every composite n (the members of A056777) is printed (HIT).
//
// Method (implementation 1, segmented factorization sieve). For a segment of consecutive m,
// every m starts as rem = odd part of m, with phi and sigma of the 2-part taken from ctz(m).
// Every odd prime p <= sqrt(end + 12) is then divided out of its multiples completely, using
// exact division by the 2-adic inverse pinv of p (for x < 2^64: p | x iff x*pinv mod 2^64 <=
// floor((2^64-1)/p), and then x/p == x*pinv mod 2^64). A cofactor rem > 1 left at the end has
// all prime factors > sqrt(end + 12) >= sqrt(m), so it is a single prime. All values stay below
// 2^64 (sigma(m) < 7m for m <= 10^13), so phi and sigma are exact 64-bit integers.
//
// Blocks: block k covers k*B < n <= (k+1)*B (B = --block), clipped to [start, end]. For each
// block the program prints the exact sums of phi(n) and sigma(n) and the position-weighted
// hash sum((phi(n)*C + sigma(n)) * (2n+1)) mod 2^64, C = 0x9E3779B97F4A7C15; the independent
// implementation a056777_independent.py prints the same quantities for comparison.
//
// Build: g++ -O3 -std=c++17 -pthread -o a056777_search a056777_search.cpp
// Usage: ./a056777_search --start 1 --end 100000000000 [--threads 3] [--block 1000000000]
//                         [--seg 131072]
#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

typedef uint64_t u64;
typedef unsigned __int128 u128;

static const u64 HASH_C = 0x9E3779B97F4A7C15ULL;

struct OddPrime {
  u64 p, pinv, lim;
};

struct Elem {
  u64 rem, phi, sig;
};

struct Hit {
  u64 n, phin, sign, phiN, sigN;
};

struct BlockResult {
  u64 lo = 0, hi = 0;
  u128 sumphi = 0, sumsig = 0;
  u64 hash = 0, primehits = 0;
  std::vector<Hit> hits;
  double secs = 0;
};

static std::string u128str(u128 x) {
  if (x == 0) return "0";
  std::string s;
  while (x) {
    s += char('0' + (int)(x % 10));
    x /= 10;
  }
  std::reverse(s.begin(), s.end());
  return s;
}

static u64 isqrt_u64(u64 x) {
  u64 r = (u64)std::sqrt((double)x);
  while (r > 0 && r * r > x) --r;
  while ((r + 1) * (r + 1) <= x) ++r;
  return r;
}

// odd primes <= limit, with 2-adic inverse and divisibility limit
static std::vector<OddPrime> odd_primes_upto(u64 limit) {
  std::vector<char> comp(limit + 1, 0);
  std::vector<OddPrime> out;
  for (u64 i = 2; i <= limit; ++i) {
    if (comp[i]) continue;
    for (u64 j = i * i; j <= limit; j += i) comp[j] = 1;
    if (i == 2) continue;
    u64 inv = i;  // correct mod 2^3 for odd i
    for (int k = 0; k < 5; ++k) inv *= 2 - i * inv;
    if (i * inv != 1) {
      fprintf(stderr, "inverse failure at %llu\n", (unsigned long long)i);
      exit(2);
    }
    out.push_back({i, inv, ~0ULL / i});
  }
  return out;
}

static inline void divide_out(Elem& e, u64 p, u64 pinv, u64 lim) {
  u64 r = e.rem * pinv;  // p | e.rem here, so this is the exact quotient
  u64 f = p - 1, s = p + 1;
  u64 t = r * pinv;
  while (t <= lim) {  // p still divides r
    r = t;
    f *= p;
    s = s * p + 1;
    t = r * pinv;
  }
  e.rem = r;
  e.phi *= f;
  e.sig *= s;
}

// all n in [lo, hi] (inclusive); uses m in [lo, hi + 12]
static void process_block(u64 lo, u64 hi, u64 S, const std::vector<OddPrime>& P,
                          std::vector<Elem>& buf, std::vector<u64>& off, BlockResult& R) {
  const size_t np = P.size();
  for (size_t k = 0; k < np; ++k) {
    u64 p = P[k].p, r = lo % p;
    off[k] = r ? p - r : 0;  // offset of the first multiple of p that is >= lo
  }
  Elem* E = buf.data();
  for (u64 L = lo; L <= hi; L += S) {
    const u64 cnt = std::min(S, hi - L + 1);  // n in [L, L + cnt)
    const u64 W = cnt + 12;                   // m in [L, L + W)
    for (u64 i = 0; i < W; ++i) {
      u64 m = L + i;
      int e = __builtin_ctzll(m);
      E[i].rem = m >> e;
      E[i].phi = e ? (1ULL << (e - 1)) : 1;
      E[i].sig = (2ULL << e) - 1;
    }
    for (size_t k = 0; k < np; ++k) {
      const u64 p = P[k].p, pinv = P[k].pinv, lim = P[k].lim;
      u64 j = off[k];
      for (; j < cnt; j += p) divide_out(E[j], p, pinv, lim);
      const u64 jn = j;  // first multiple at or beyond the next segment start
      for (; j < W; j += p) divide_out(E[j], p, pinv, lim);
      off[k] = jn - cnt;
    }
    for (u64 i = 0; i < W; ++i) {
      u64 r = E[i].rem;
      if (r > 1) {  // a single prime > sqrt(end + 12)
        E[i].phi *= r - 1;
        E[i].sig *= r + 1;
      }
    }
    u64 sp = 0, ss = 0, h = 0;
    for (u64 i = 0; i < cnt; ++i) {
      const u64 n = L + i, ph = E[i].phi, sg = E[i].sig;
      sp += ph;
      ss += sg;
      h += (ph * HASH_C + sg) * (2 * n + 1);
      if (E[i + 12].phi == ph + 12 && E[i + 12].sig == sg + 12) {
        if (n > 1 && ph == n - 1)
          ++R.primehits;  // n prime (and then n + 12 is prime as well)
        else
          R.hits.push_back({n, ph, sg, E[i + 12].phi, E[i + 12].sig});
      }
    }
    R.sumphi += sp;
    R.sumsig += ss;
    R.hash += h;
  }
}

static u64 parse_u64(const char* s) {
  char* endp = nullptr;
  double d = strtod(s, &endp);  // accept 1e11 style
  if (endp && *endp == 0 && std::strpbrk(s, "eE.")) return (u64)d;
  return strtoull(s, nullptr, 10);
}

int main(int argc, char** argv) {
  u64 start = 1, end = 0, block = 1000000000ULL, seg = 131072;
  int threads = 3;
  for (int i = 1; i + 1 < argc; i += 2) {
    if (!strcmp(argv[i], "--start")) start = parse_u64(argv[i + 1]);
    else if (!strcmp(argv[i], "--end")) end = parse_u64(argv[i + 1]);
    else if (!strcmp(argv[i], "--block")) block = parse_u64(argv[i + 1]);
    else if (!strcmp(argv[i], "--seg")) seg = parse_u64(argv[i + 1]);
    else if (!strcmp(argv[i], "--threads")) threads = atoi(argv[i + 1]);
    else {
      fprintf(stderr, "unknown option %s\n", argv[i]);
      return 2;
    }
  }
  if (start < 1 || end < start || end > 10000000000000ULL || block < 1 || seg < 1 ||
      threads < 1) {
    fprintf(stderr, "usage: %s --start A --end B [--threads T] [--block B] [--seg S]\n"
                    "       (1 <= A <= B <= 10^13)\n", argv[0]);
    return 2;
  }
  const u64 plim = isqrt_u64(end + 12);
  const std::vector<OddPrime> P = odd_primes_upto(plim);
  const u64 k0 = (start - 1) / block, k1 = (end - 1) / block;  // block k: k*B < n <= (k+1)*B
  const u64 nblocks = k1 - k0 + 1;
  printf("# a056777_search start=%llu end=%llu threads=%d block=%llu seg=%llu "
         "sieve_primes<=%llu (%zu odd primes) blocks=%llu\n",
         (unsigned long long)start, (unsigned long long)end, threads,
         (unsigned long long)block, (unsigned long long)seg, (unsigned long long)plim,
         P.size(), (unsigned long long)nblocks);
  fflush(stdout);

  std::vector<BlockResult> results(nblocks);
  std::atomic<u64> next(0);
  std::mutex mu;
  const auto t0 = std::chrono::steady_clock::now();
  auto worker = [&]() {
    std::vector<Elem> buf(seg + 12);
    std::vector<u64> off(P.size());
    for (;;) {
      const u64 b = next.fetch_add(1);
      if (b >= nblocks) break;
      const u64 k = k0 + b;
      BlockResult& R = results[b];
      R.lo = std::max(start, k * block + 1);
      R.hi = std::min(end, (k + 1) * block);
      const auto tb = std::chrono::steady_clock::now();
      process_block(R.lo, R.hi, seg, P, buf, off, R);
      R.secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - tb).count();
      const double el = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
      std::lock_guard<std::mutex> g(mu);
      printf("BLOCK %llu lo=%llu hi=%llu hits=%zu primehits=%llu sumphi=%s sumsigma=%s "
             "hash=%016llx secs=%.2f elapsed=%.1f\n",
             (unsigned long long)k, (unsigned long long)R.lo, (unsigned long long)R.hi,
             R.hits.size(), (unsigned long long)R.primehits, u128str(R.sumphi).c_str(),
             u128str(R.sumsig).c_str(), (unsigned long long)R.hash, R.secs, el);
      for (const Hit& h : R.hits)
        printf("HIT %llu phi=%llu sigma=%llu phi12=%llu sigma12=%llu\n",
               (unsigned long long)h.n, (unsigned long long)h.phin,
               (unsigned long long)h.sign, (unsigned long long)h.phiN,
               (unsigned long long)h.sigN);
      fflush(stdout);
    }
  };
  std::vector<std::thread> pool;
  for (int t = 0; t < threads; ++t) pool.emplace_back(worker);
  for (auto& th : pool) th.join();

  u128 sp = 0, ss = 0;
  u64 h = 0, nprime = 0;
  std::vector<u64> hits;
  for (const BlockResult& R : results) {
    sp += R.sumphi;
    ss += R.sumsig;
    h += R.hash;
    nprime += R.primehits;
    for (const Hit& x : R.hits) hits.push_back(x.n);
  }
  std::sort(hits.begin(), hits.end());
  const double el = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  printf("DONE start=%llu end=%llu hits=%zu primehits=%llu sumphi=%s sumsigma=%s "
         "hash=%016llx secs=%.1f\n",
         (unsigned long long)start, (unsigned long long)end, hits.size(),
         (unsigned long long)nprime, u128str(sp).c_str(), u128str(ss).c_str(),
         (unsigned long long)h, el);
  printf("HITS");
  for (u64 x : hits) printf(" %llu", (unsigned long long)x);
  printf("\n");
  return 0;
}
