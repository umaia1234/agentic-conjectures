#include <algorithm>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <tuple>
#include <vector>

// Exhaustive scanner for OEIS A076141.  For each n, compare every L-bit
// window of n^2 with n, where L is the binary length of n.
int main(int argc, char** argv) {
  const std::uint64_t limit = argc > 1 ? std::strtoull(argv[1], nullptr, 10)
                                        : 10000000ULL;
  std::uint64_t positives = 0;
  std::uint64_t doubles = 0;
  std::uint64_t max_n = 0;
  std::map<std::tuple<unsigned, unsigned, unsigned>, std::uint64_t> geometry;

  for (std::uint64_t n = 1; n <= limit; ++n) {
    const unsigned L = std::bit_width(n);
    const unsigned __int128 square =
        static_cast<unsigned __int128>(n) * n;
    unsigned M = 0;
    for (auto x = square; x != 0; x >>= 1) ++M;
    const unsigned __int128 mask =
        (static_cast<unsigned __int128>(1) << L) - 1;
    std::vector<unsigned> offsets;
    for (unsigned s = 0; s + L <= M; ++s) {
      if (((square >> s) & mask) == n) offsets.push_back(s);
    }
    if (!offsets.empty()) {
      ++positives;
      max_n = n;
      for (unsigned s : offsets) {
        const unsigned prefix = M - L - s;
        geometry[{L, prefix, s}]++;
      }
    }
    if (offsets.size() >= 2) {
      ++doubles;
      std::cout << "COUNTEREXAMPLE n=" << n << " L=" << L << " M=" << M
                << " offsets=";
      for (unsigned s : offsets) std::cout << s << ',';
      std::cout << '\n';
      return 1;
    }
  }
  std::cout << "checked=1.." << limit << " positives=" << positives
            << " doubles=" << doubles << " largest_positive=" << max_n
            << '\n';

  // Aggregate by (prefix length, suffix length), suppressing bit length.
  std::map<std::pair<unsigned, unsigned>, std::uint64_t> shape;
  for (const auto& [key, count] : geometry) {
    auto [L, prefix, suffix] = key;
    (void)L;
    shape[{prefix, suffix}] += count;
  }
  std::vector<std::pair<std::uint64_t, std::pair<unsigned, unsigned>>> ranked;
  for (const auto& [key, count] : shape) ranked.push_back({count, key});
  std::sort(ranked.rbegin(), ranked.rend());
  for (std::size_t i = 0; i < std::min<std::size_t>(ranked.size(), 30); ++i) {
    std::cout << "shape prefix=" << ranked[i].second.first
              << " suffix=" << ranked[i].second.second
              << " count=" << ranked[i].first << '\n';
  }
}
