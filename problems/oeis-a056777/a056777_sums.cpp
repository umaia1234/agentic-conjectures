// a056777_sums.cpp -- closed-form totals used to audit the A056777 sieve logs.
//
// For each argument x it prints
//     PHISUM x = sum_{n<=x} phi(n)     and     SIGMASUM x = sum_{n<=x} sigma(n)
// computed without factoring any n:
//   * sum sigma(n) = sum_{d<=x} d*floor(x/d), evaluated over the O(sqrt x) ranges of d on which
//     floor(x/d) is constant;
//   * Phi(x) = x(x+1)/2 - sum_{d=2}^{x} Phi(floor(x/d)) (every pair 1 <= a <= b <= x has a unique
//     gcd d), with a linear sieve table of Phi below a cutoff and memoised values Phi(floor(x/k))
//     above it.
// Both are exact (unsigned 128-bit). The search logs record the sums of phi(n) and sigma(n) per
// block, so their totals over [1, x] must equal these values.
//
// Build: g++ -O3 -std=c++17 -o a056777_sums a056777_sums.cpp
// Usage: ./a056777_sums 1000000 100000000000 ...      (each x <= 10^13)
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>

typedef uint64_t u64;
typedef unsigned __int128 u128;

static std::string str(u128 x) {
  if (x == 0) return "0";
  std::string s;
  while (x) {
    s += char('0' + (int)(x % 10));
    x /= 10;
  }
  std::reverse(s.begin(), s.end());
  return s;
}

static u128 tri(u64 m) { return (u128)m * (m + 1) / 2; }

static u128 sigma_sum(u64 x) {
  u128 s = 0;
  for (u64 l = 1; l <= x;) {
    const u64 q = x / l, r = x / q;
    s += (u128)q * (tri(r) - tri(l - 1));
    l = r + 1;
  }
  return s;
}

static u128 phi_sum(u64 x) {
  if (x == 0) return 0;
  u64 cut = (u64)std::cbrt((double)x);
  cut = std::max<u64>(cut * cut, 1000);
  cut = std::min<u64>(cut, std::min<u64>(x, 20000000));
  // linear sieve for phi on [0, cut], then prefix sums
  std::vector<uint32_t> phi(cut + 1, 0);
  std::vector<uint32_t> primes;
  phi[1] = 1;
  for (u64 i = 2; i <= cut; ++i) {
    if (phi[i] == 0) {
      phi[i] = (uint32_t)(i - 1);
      primes.push_back((uint32_t)i);
    }
    for (uint32_t p : primes) {
      const u64 ip = i * p;
      if (ip > cut) break;
      if (i % p == 0) {
        phi[ip] = phi[i] * p;
        break;
      }
      phi[ip] = phi[i] * (p - 1);
    }
  }
  std::vector<u64> small(cut + 1, 0);
  for (u64 i = 1; i <= cut; ++i) small[i] = small[i - 1] + phi[i];
  phi.clear();
  phi.shrink_to_fit();
  if (x <= cut) return small[x];
  const u64 K = x / (cut + 1);  // floor(x/k) > cut  <=>  k <= K
  std::vector<u128> big(K + 1, 0);
  for (u64 k = K; k >= 1; --k) {
    const u64 v = x / k;
    u128 s = tri(v);
    for (u64 d = 2; d <= v;) {
      const u64 q = v / d, dmax = v / q;
      const u128 val = (q <= cut) ? (u128)small[q] : big[k * d];  // here q = floor(x/(kd))
      s -= (u128)(dmax - d + 1) * val;
      d = dmax + 1;
    }
    big[k] = s;
  }
  return big[1];
}

int main(int argc, char** argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s x [x ...]   (1 <= x <= 10^13)\n", argv[0]);
    return 2;
  }
  for (int i = 1; i < argc; ++i) {
    const u64 x = strtoull(argv[i], nullptr, 10);
    if (x < 1 || x > 10000000000000ULL) {
      fprintf(stderr, "bad x %s\n", argv[i]);
      return 2;
    }
    printf("PHISUM %llu %s\n", (unsigned long long)x, str(phi_sum(x)).c_str());
    printf("SIGMASUM %llu %s\n", (unsigned long long)x, str(sigma_sum(x)).c_str());
    fflush(stdout);
  }
  return 0;
}
