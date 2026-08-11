#include <algorithm>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <set>

using u128 = unsigned __int128;
using u64 = std::uint64_t;

static u128 isqrt128(u128 x) {
  u128 lo = 0;
  u128 hi = (u128{1} << 64);  // exclusive; sufficient for x < 2^128
  while (lo + 1 < hi) {
    const u128 mid = lo + (hi - lo) / 2;
    if (mid <= x / mid)
      lo = mid;
    else
      hi = mid;
  }
  return lo;
}

static unsigned bit_width128(u128 x) {
  unsigned ans = 0;
  while (x) {
    ++ans;
    x >>= 1;
  }
  return ans;
}

static u64 periodic_prefix(u64 seed, unsigned d, unsigned r) {
  // seed is an exactly d-bit word. Return the first r bits of its periodic
  // continuation.
  u64 q = 0;
  for (unsigned i = 0; i < r; ++i) {
    const unsigned seed_pos = d - 1 - (i % d);
    q = (q << 1) | ((seed >> seed_pos) & 1ULL);
  }
  return q;
}

static unsigned count_occurrences(u64 n, unsigned* first = nullptr,
                                  unsigned* second = nullptr) {
  const unsigned L = std::bit_width(n);
  const u128 square = static_cast<u128>(n) * n;
  const unsigned M = bit_width128(square);
  const u128 mask = (u128{1} << L) - 1;
  unsigned count = 0;
  for (unsigned s = 0; s + L <= M; ++s) {
    if (((square >> s) & mask) == n) {
      if (count == 0 && first) *first = s;
      if (count == 1 && second) *second = s;
      ++count;
    }
  }
  return count;
}

int main(int argc, char** argv) {
  const unsigned max_L = argc > 1 ? std::strtoul(argv[1], nullptr, 10) : 40;
  if (max_L > 62) {
    std::cerr << "This __int128 implementation supports max_L <= 62.\n";
    return 2;
  }

  u64 geometries = 0;
  u64 q_candidates = 0;
  u64 quadratic_candidates = 0;
  std::set<u64> roots;

  for (unsigned L = 2; L <= max_L; ++L) {
    for (unsigned r = 1; r < L; ++r) {
      const unsigned d = L - r;  // distance between the two starts
      const unsigned key_bits = std::min(r, d);
      const u64 key_lo = u64{1} << (key_bits - 1);
      const u64 key_hi = u64{1} << key_bits;

      for (unsigned eps = 0; eps <= 1; ++eps) {
        // M = 2L-eps and prefix+suffix = r-eps.  Both are nonempty,
        // since prefix/suffix occurrences were disposed of separately.
        if (r < eps + 2) continue;
        for (unsigned s = 1; s + 1 <= r - eps; ++s) {
          const unsigned p = r - eps - s;
          ++geometries;
          const unsigned E = L + d + s;  // number of bits below prefix A

          for (u64 key = key_lo; key < key_hi; ++key) {
            ++q_candidates;
            const u64 q = r <= d ? key : periodic_prefix(key, d, r);
            const u64 low = q << d;
            const u64 high = ((q + 1) << d) - 1;
            u64 Amin = static_cast<u64>((static_cast<u128>(low) * low) >> E);
            u64 Amax = static_cast<u64>((static_cast<u128>(high) * high) >> E);
            Amin = std::max(Amin, u64{1} << (p - 1));
            Amax = std::min(Amax, (u64{1} << p) - 1);
            if (Amin > Amax) continue;

            const u64 Bmask = (u64{1} << s) - 1;
            const u64 B = (static_cast<u128>(q) * q) & Bmask;
            const u128 C = (u128{1} << s) * ((u128{1} << d) + 1);
            for (u64 A = Amin; A <= Amax; ++A) {
              ++quadratic_candidates;
              // n^2 - C n = A*2^E - q*2^(d+s) + B.
              const u128 D = (static_cast<u128>(A) << E)
                           - (static_cast<u128>(q) << (d + s)) + B;
              const u128 disc = C * C + 4 * D;
              const u128 root = isqrt128(disc);
              if (root * root != disc || ((C + root) & 1)) continue;
              const u128 n128 = (C + root) / 2;
              if (n128 > std::numeric_limits<u64>::max()) continue;
              const u64 n = static_cast<u64>(n128);
              if (std::bit_width(n) != L) continue;
              const u128 square = static_cast<u128>(n) * n;
              if (bit_width128(square) != 2 * L - eps) continue;
              const u128 mask = (u128{1} << L) - 1;
              if (((square >> s) & mask) != n) continue;
              if (((square >> (s + d)) & mask) != n) continue;
              roots.insert(n);
              std::cout << "COUNTEREXAMPLE n=" << n << " L=" << L
                        << " offsets=" << s << ',' << s + d << '\n';
            }
          }
        }
      }
    }
    if (L % 5 == 0 || L == max_L)
      std::cerr << "completed L=" << L << " q_candidates=" << q_candidates
                << " quadratic_candidates=" << quadratic_candidates << '\n';
  }

  std::cout << "max_L=" << max_L << " geometries=" << geometries
            << " q_candidates=" << q_candidates
            << " quadratic_candidates=" << quadratic_candidates
            << " counterexamples=" << roots.size() << '\n';
  return roots.empty() ? 0 : 1;
}
