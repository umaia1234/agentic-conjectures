// a135508_scan.cpp -- exhaustive scan for OEIS A135508 (McEachen's conjecture).
//
// Definitions (upstream FormalConjectures OEIS/135508.lean, OEIS offset 1):
//   x(1) = 1,  x(n+1) = 2 x(n) + lcm(x(n), n+1)   (n >= 1),
//   a(n) = x(n+1)/x(n) - 2                         (n >= 1).
// Since lcm(x, m) = x * (m / gcd(x, m)), one has
//   a(n) = (n+1) / gcd(x(n), n+1)   and   x(n+1) = x(n) * (a(n) + 2),
// so x(n) is determined by its prime exponents.  This program tracks
// min(v_q(x(n)), 255) for every prime q <= N+3 (exponents in numbers below
// 2^32 are < 32, so the cap never changes a gcd) and evaluates a(1..N).
//
// Checks (exit status 1 if any of them fails):
//  [C1] a(n) is 1 or a prime for every 1 <= n <= N (OEIS comment);
//  [C2] the conjecture: a(p-1) = p for every prime p <= N+1 with p-2 not
//       prime;
//  [C3] the Lean equivalence a_pred_eq_iff: for primes 5 <= p <= N+1,
//       a(p-1) = p  <=>  gcd(x(p-3), p-2) > 1  (i.e. a(p-3) != p-2);
//  [C4] for every prime p <= N+1 with p-2 composite, minFac(p-2) | x(p-3);
//  [C5] for every prime r with r^2 <= N+1: r | x(r^2-1), i.e. F(r) <= r^2-1
//       where F(r) = min{n : r | x(n)} is the first-entry index.
// It also prints a fingerprint of a(1..N) (counts, sum, rolling hash) that
// the independent implementation a135508_scan_numba.py reproduces.
//
// Usage: a135508_scan N [--certs]
//   N <= 4000000000.  --certs prints F(r) for every prime r < 1009 (the
//   certificate table used in AgenticConjectures/OeisA135508.lean).
// Build: g++ -O3 -std=c++17 a135508_scan.cpp -o a135508_scan
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

typedef unsigned long long ull;

static std::vector<uint16_t> spfo;  // smallest prime factor of odd c; 0 if c is prime

static inline uint64_t spf(uint64_t c) {
  if ((c & 1) == 0) return 2;
  uint16_t s = spfo[c >> 1];
  return s ? s : c;
}
static inline bool is_prime(uint64_t c) { return c >= 2 && spf(c) == c; }

int main(int argc, char** argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s N [--certs]\n", argv[0]);
    return 2;
  }
  const uint64_t N = strtoull(argv[1], nullptr, 10);
  const bool certs = argc > 2 && strcmp(argv[2], "--certs") == 0;
  if (N < 10 || N > 4000000000ULL) {
    fprintf(stderr, "N must lie in [10, 4000000000]\n");
    return 2;
  }
  const uint64_t M = N + 4;  // every number we factor or test is <= N+3
  spfo.assign(M / 2 + 1, 0);
  for (uint64_t p = 3; p * p <= M; p += 2) {
    if (spfo[p >> 1]) continue;
    for (uint64_t j = p * p; j <= M; j += 2 * p)
      if (!spfo[j >> 1]) spfo[j >> 1] = (uint16_t)p;
  }
  std::vector<uint8_t> vodd(M / 2 + 1, 0);  // min(v_q(x(n)), 255) for odd q
  uint64_t v2 = 0;                          // v_2(x(n)), exact
  uint64_t rmax = (uint64_t)std::sqrt((double)(N + 1));
  while ((rmax + 1) * (rmax + 1) <= N + 1) ++rmax;
  while (rmax * rmax > N + 1) --rmax;
  const uint64_t FMAX = std::max<uint64_t>(rmax, 1009);
  std::vector<uint64_t> F(FMAX + 1, 0);  // first-entry indices for q <= FMAX

  ull fails_c1 = 0, fails_c2 = 0, fails_c3 = 0, fails_c4 = 0, fails_c5 = 0;
  ull cnt1 = 0, cnt2 = 0, sum_a = 0, hash = 0, nprimes = 0, nconj = 0, ncomposite_pm2 = 0;
  ull twin_hits = 0;
  uint64_t a_prev1 = 0, a_prev2 = 0;  // a(n-1), a(n-2)
  for (uint64_t n = 1; n <= N; ++n) {
    const uint64_t m = n + 1;
    // C4 bookkeeping: m = p-2 with p prime and m composite.
    const bool c4case = m >= 4 && m + 2 <= N + 1 && is_prime(m + 2) && !is_prime(m);
    uint64_t a = 1, c = m;
    int nfac = 0;
    bool first = true, c4ok = false;
    while (c > 1) {
      const uint64_t q = spf(c);
      int e = 0;
      while (c % q == 0) { c /= q; ++e; }
      const int vq = q == 2 ? (int)std::min<uint64_t>(v2, 255) : vodd[q >> 1];
      if (first && vq > 0) c4ok = true;  // smallest prime factor divides x(n)
      first = false;
      for (int i = vq; i < e; ++i) { a *= q; ++nfac; }
    }
    if (c4case) {
      ++ncomposite_pm2;
      if (!c4ok) {
        if (fails_c4 < 10) printf("C4 FAIL: p=%llu\n", (ull)(m + 2));
        ++fails_c4;
      }
    }
    if (nfac >= 2) {
      if (fails_c1 < 10) printf("C1 FAIL: a(%llu)=%llu is composite\n", (ull)n, (ull)a);
      ++fails_c1;
    }
    if (is_prime(m)) {  // p = m = n+1, a(p-1) = a(n)
      const uint64_t p = m;
      ++nprimes;
      const bool pm2prime = p >= 4 && is_prime(p - 2);
      if (!pm2prime) {
        ++nconj;
        if (a != p) {
          if (fails_c2 < 10) printf("C2 FAIL: p=%llu a(p-1)=%llu\n", (ull)p, (ull)a);
          ++fails_c2;
        }
      } else if (a == p) {
        ++twin_hits;
        if (twin_hits <= 10) printf("note: p=%llu has p-2 prime and a(p-1)=p\n", (ull)p);
      }
      if (p >= 5 && ((a == p) != (a_prev2 != p - 2))) {
        if (fails_c3 < 10) printf("C3 FAIL: p=%llu\n", (ull)p);
        ++fails_c3;
      }
    }
    cnt1 += a == 1;
    cnt2 += a == 2;
    sum_a += a;
    hash = hash * 1000003ULL + a;
    // x(n+1) = x(n) * (a(n) + 2)
    c = a + 2;
    while (c > 1) {
      const uint64_t q = spf(c);
      int e = 0;
      while (c % q == 0) { c /= q; ++e; }
      if (q == 2) {
        if (v2 == 0 && q <= FMAX) F[q] = n + 1;
        v2 += e;
      } else {
        const int old = vodd[q >> 1];
        if (old == 0 && q <= FMAX) F[q] = n + 1;
        vodd[q >> 1] = (uint8_t)std::min(old + e, 255);
      }
    }
    a_prev2 = a_prev1;
    a_prev1 = a;
  }
  uint64_t worst_r = 0;
  double worst = 0;
  ull nr = 0;
  for (uint64_t r = 2; r <= rmax; ++r) {
    if (!is_prime(r)) continue;
    ++nr;
    if (F[r] == 0 || F[r] > r * r - 1) {
      if (fails_c5 < 10) printf("C5 FAIL: r=%llu F=%llu\n", (ull)r, (ull)F[r]);
      ++fails_c5;
      continue;
    }
    const double ratio = (double)F[r] / (double)(r * r);
    if (ratio > worst) { worst = ratio; worst_r = r; }
  }
  if (certs) {
    for (uint64_t r = 2; r < 1009 && r <= FMAX; ++r)
      if (is_prime(r)) printf("cert r=%llu F=%llu\n", (ull)r, (ull)F[r]);
  }
  printf("N=%llu\n", (ull)N);
  printf("fingerprint: count_a1=%llu count_a2=%llu sum_a=%llu hash=%016llx\n", cnt1, cnt2, sum_a,
         hash);
  printf("primes p<=N+1: %llu; with p-2 not prime: %llu; p-2 composite (p>=5): %llu\n", nprimes,
         nconj, ncomposite_pm2);
  printf("primes p<=N+1 with p-2 prime and a(p-1)=p: %llu\n", twin_hits);
  printf("C5 range: %llu primes r<=%llu; max F(r)/r^2 = %.4f at r=%llu (F=%llu)\n", nr,
         (ull)rmax, worst, (ull)worst_r, (ull)(worst_r ? F[worst_r] : 0));
  printf("C1 fails=%llu C2 fails=%llu C3 fails=%llu C4 fails=%llu C5 fails=%llu\n", fails_c1,
         fails_c2, fails_c3, fails_c4, fails_c5);
  const bool ok = !(fails_c1 || fails_c2 || fails_c3 || fails_c4 || fails_c5);
  printf("RESULT %s\n", ok ? "PASS" : "FAIL");
  return ok ? 0 : 1;
}
