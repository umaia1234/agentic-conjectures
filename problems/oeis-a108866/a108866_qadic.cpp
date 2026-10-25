// a108866_qadic.cpp: q-adic check of Ordowski's conjecture on OEIS A108866.
//
// E_n = -2/n + sum_{k=1}^n 2^k/k.  The conjecture says that for n > 3, n^2 divides the
// numerator of E_n iff n is prime.  Since E_n != 0, n^2 divides the numerator iff
// v_q(E_n) >= 2 v_q(n) for every prime q | n.  For a prime q this program computes the
// capped valuation min(v_q(E_n), 2 v_q(n)) from running sums of 2^k q^L / k modulo q^(3L),
// where q^L is at least the largest power of q not exceeding n.  The sum is kept as a
// fraction num / den with den a q-adic unit, so no modular inverse is needed.
//
// Usage: a108866_qadic N [Q0 [P0]]
//   1. every prime q <= Q0 (default floor(sqrt(N))): all multiples n of q, 4 <= n <= N;
//   2. every composite n <= N not excluded by step 1 (some prime q | n with
//      v_q(E_n) < 2 v_q(n)): its prime factors q > Q0, each by a running sum up to n;
//   3. every prime p with Q0 < p <= P0 (default min(N, 100000)): the pair (p, p).
// Writes lines "n q v" (sorted by n, then q) to stdout and a summary to stderr.  Exits with
// status 1 if a composite n in 3 < n <= N is not excluded or a checked prime p >= 5 has
// v_p(E_p) < 2.  Needs q^(3L) < 2^63, which holds for N <= 2000000.
//
// Build: g++ -O2 -std=c++17 -o a108866_qadic a108866_qadic.cpp

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

typedef unsigned long long u64;
typedef unsigned __int128 u128;

static inline u64 mulmod(u64 a, u64 b, u64 m) { return (u64)((u128)a * b % m); }

struct Rec {
  uint32_t n, q;
  int32_t v;
};

// Largest L with q^L <= x.
static int floor_log(u64 q, u64 x) {
  int L = 0;
  for (u64 p = q; p <= x; p *= q) ++L;
  return L;
}

// Running sum for the prime q with precision q^L (modulus q^(3L)) over k = 1..last.  Calls
// emit(k, a, capped) for each k >= 4 with v_q(k) = a >= 1 (only k == last if only_last).
template <class F>
static void run_prime(u64 q, int L, u64 last, bool only_last, F emit) {
  std::vector<u64> qpow(L + 1, 1);
  for (int i = 1; i <= L; ++i) qpow[i] = qpow[i - 1] * q;
  const u64 M = qpow[L] * qpow[L] * qpow[L];
  u64 num = 0, den = 1, pow2 = 1, r = 0;  // sum_{j<=k} 2^j q^L / j == num / den (mod M)
  for (u64 k = 1; k <= last; ++k) {
    pow2 <<= 1;
    if (pow2 >= M) pow2 -= M;
    if (++r == q) r = 0;
    u64 kp = k;
    int v = 0;
    if (r == 0)
      while (kp % q == 0) kp /= q, ++v;
    const u64 kpm = kp % M;
    const u64 c = mulmod(pow2, qpow[L - v], M);
    num = (mulmod(num, kpm, M) + mulmod(c, den, M)) % M;
    den = mulmod(den, kpm, M);
    if (v > 0 && k >= 4 && (!only_last || k == last)) {
      // q^L E_k = (num * kp - 2 q^(L - v) den) / (den * kp); the denominator is a unit.
      const u64 t = mulmod(2 * qpow[L - v] % M, den, M);
      u64 z = (mulmod(num, kpm, M) + M - t) % M;
      int w = 0;
      if (z == 0)
        w = 3 * L;
      else
        while (z % q == 0) z /= q, ++w;
      emit(k, v, std::min(w - L, 2 * v));
    }
  }
}

int main(int argc, char** argv) {
  if (argc < 2) {
    std::fprintf(stderr, "usage: %s N [Q0 [P0]]\n", argv[0]);
    return 2;
  }
  const u64 N = std::strtoull(argv[1], nullptr, 10);
  if (N < 4 || N > 2000000) {
    std::fprintf(stderr, "N must satisfy 4 <= N <= 2000000\n");
    return 2;
  }
  u64 Q0 = 1;
  while ((Q0 + 1) * (Q0 + 1) <= N) ++Q0;
  if (argc > 2) Q0 = std::strtoull(argv[2], nullptr, 10);
  u64 P0 = argc > 3 ? std::strtoull(argv[3], nullptr, 10) : std::min<u64>(N, 100000);
  if (P0 > N) P0 = N;

  std::vector<uint32_t> spf(N + 1, 0);
  for (u64 i = 2; i <= N; ++i)
    if (spf[i] == 0)
      for (u64 j = i; j <= N; j += i)
        if (spf[j] == 0) spf[j] = (uint32_t)i;

  std::vector<Rec> out;
  std::vector<char> excluded(N + 1, 0);
  bool ok = true;

  // Step 1: small primes, all multiples.
  for (u64 q = 2; q <= Q0 && q <= N; ++q) {
    if (spf[q] != q) continue;
    const u64 last = N / q * q;
    run_prime(q, floor_log(q, N), last, false, [&](u64 k, int a, int c) {
      out.push_back({(uint32_t)k, (uint32_t)q, c});
      if (c < 2 * a) excluded[k] = 1;
    });
  }

  // Step 2: composites without a witness among q <= Q0.
  u64 composites = 0, fallback_n = 0, fallback_pairs = 0, unexcluded = 0;
  for (u64 n = 4; n <= N; ++n) {
    if (spf[n] == n) continue;
    ++composites;
    if (excluded[n]) continue;
    ++fallback_n;
    for (u64 m = n; m > 1;) {
      const u64 q = spf[m];
      while (m % q == 0) m /= q;
      if (q <= Q0) continue;
      ++fallback_pairs;
      run_prime(q, floor_log(q, n), n, true, [&](u64 k, int a, int c) {
        out.push_back({(uint32_t)k, (uint32_t)q, c});
        if (c < 2 * a) excluded[k] = 1;
      });
    }
    if (!excluded[n]) {
      ++unexcluded;
      ok = false;
      std::fprintf(stderr, "composite n = %llu has n^2 | numerator(E_n)\n", n);
    }
  }

  // Step 3: primes above Q0, the pair (p, p).
  u64 primes_checked = 0;
  int min_prime_val = 2;
  for (const Rec& rec : out)
    if (rec.n == rec.q && rec.n >= 5) {
      ++primes_checked;
      min_prime_val = std::min(min_prime_val, (int)rec.v);
    }
  for (u64 p = std::max<u64>(Q0 + 1, 5); p <= P0; ++p) {
    if (spf[p] != p) continue;
    run_prime(p, floor_log(p, p), p, true, [&](u64 k, int, int c) {
      out.push_back({(uint32_t)k, (uint32_t)p, c});
      ++primes_checked;
      min_prime_val = std::min(min_prime_val, c);
    });
  }
  if (min_prime_val < 2) ok = false;

  std::sort(out.begin(), out.end(), [](const Rec& a, const Rec& b) {
    return a.n != b.n ? a.n < b.n : a.q < b.q;
  });
  for (const Rec& rec : out) std::printf("%u %u %d\n", rec.n, rec.q, rec.v);

  std::fprintf(stderr,
               "N=%llu Q0=%llu P0=%llu: composites %llu, needing fallback %llu (pairs %llu), "
               "not excluded %llu; primes 5 <= p checked %llu, min min(v_p(E_p),2) = %d; "
               "pairs written %zu\n",
               N, Q0, P0, composites, fallback_n, fallback_pairs, unexcluded, primes_checked,
               min_prime_val, out.size());
  std::fprintf(stderr, ok ? "OK\n" : "FAILED\n");
  return ok ? 0 : 1;
}
