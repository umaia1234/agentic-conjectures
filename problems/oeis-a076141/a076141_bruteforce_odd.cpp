// OEIS A076141: brute-force occurrence lister for odd n with bit length
// Lmin..Lmax (Lmax <= 40).  Every L-bit window of n^2 is compared with n.
//
// Prints, per L, the number of occurrences and of distinct n followed by the
// lines "OCC L t n count" for every occurrence (same format as the structural
// enumerators); finally a SUMMARY line.  It also asserts the elementary facts used
// by the structural enumerators: for odd n >= 3 no occurrence starts at a bit
// position t < 3 or t >= L.
//
// Usage: a076141_bruteforce_odd <Lmin> <Lmax> [threads]

#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <thread>
#include <tuple>
#include <vector>

using u64 = std::uint64_t;
using u128 = unsigned __int128;

int main(int argc, char** argv) {
  if (argc < 3) {
    std::fprintf(stderr, "usage: %s Lmin Lmax [threads]\n", argv[0]);
    return 2;
  }
  const unsigned Lmin = std::strtoul(argv[1], nullptr, 10);
  const unsigned Lmax = std::strtoul(argv[2], nullptr, 10);
  const unsigned threads = argc > 3 ? std::strtoul(argv[3], nullptr, 10) : 4;
  if (Lmin < 2 || Lmax > 40 || Lmin > Lmax || threads == 0) return 2;
  std::atomic<bool> bad{false};
  std::size_t total = 0, counterexamples = 0;
  for (unsigned L = Lmin; L <= Lmax; ++L) {
    const u64 lo = (u64{1} << (L - 1)) | 1, hi = u64{1} << L;
    const u64 mask = hi - 1;
    std::vector<std::vector<std::tuple<unsigned, u64, int>>> local(threads);
    auto worker = [&](unsigned id) {
      // odd n = lo + 2 k, k = id, id + threads, ...
      for (u64 n = lo + 2 * u64{id}; n < hi; n += 2 * u64{threads}) {
        const u128 z = u128{n} * n;
        unsigned M = 0;
        for (u128 y = z; y; y >>= 1) ++M;
        int count = 0;
        unsigned pos[64];
        for (unsigned s = 0; s + L <= M; ++s)
          if (static_cast<u64>(z >> s & mask) == n) pos[count++] = s;
        for (int i = 0; i < count; ++i) {
          if (n >= 3 && (pos[i] < 3 || pos[i] >= L)) bad = true;
          local[id].push_back({pos[i], n, count});
        }
      }
    };
    std::vector<std::thread> pool;
    for (unsigned id = 0; id < threads; ++id) pool.emplace_back(worker, id);
    for (auto& th : pool) th.join();
    std::vector<std::tuple<unsigned, u64, int>> all;
    for (auto& v : local) all.insert(all.end(), v.begin(), v.end());
    std::sort(all.begin(), all.end());
    std::vector<u64> ns;
    int maxc = 0;
    for (auto& [t, n, c] : all) {
      ns.push_back(n);
      maxc = std::max(maxc, c);
    }
    std::sort(ns.begin(), ns.end());
    ns.erase(std::unique(ns.begin(), ns.end()), ns.end());
    for (auto& [t, n, c] : all)
      if (c >= 2) ++counterexamples;
    std::printf("L=%u odd_n_tested=%llu occurrences=%zu distinct_n=%zu max_count=%d\n", L,
                static_cast<unsigned long long>((hi - lo + 1) / 2), all.size(), ns.size(), maxc);
    for (auto& [t, n, c] : all)
      std::printf("OCC %u %u %llu %d\n", L, t, static_cast<unsigned long long>(n), c);
    std::fflush(stdout);
    total += all.size();
  }
  std::printf("SUMMARY L=%u..%u occurrences=%zu counterexamples=%zu position_check=%s\n", Lmin,
              Lmax, total, counterexamples, bad ? "FAILED" : "ok");
  return (counterexamples || bad) ? 1 : 0;
}
