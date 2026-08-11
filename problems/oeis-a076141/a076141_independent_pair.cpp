#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <string>
#include <vector>
#ifdef _OPENMP
#include <omp.h>
#endif

using u64 = std::uint64_t;
using u128 = unsigned __int128;

static int bitlen128(u128 x) {
    const u64 hi = u64(x >> 64);
    if (hi) return 128 - __builtin_clzll(hi);
    return 64 - __builtin_clzll(u64(x));
}

static std::string decimal(u128 x) {
    if (!x) return "0";
    std::string s;
    while (x) {
        s.push_back(char('0' + x % 10));
        x /= 10;
    }
    std::reverse(s.begin(), s.end());
    return s;
}

int main(int argc, char** argv) {
    const int maxL = argc > 1 ? std::stoi(argv[1]) : 32;
    if (maxL > 62) {
        std::cerr << "This exhaustive driver accepts maxL <= 62.\n";
        return 1;
    }
    std::atomic<u64> witness{0};
    u128 tested = 0;
    for (int L = 3; L <= maxL && !witness.load(); ++L) {
        const u64 lo = u64(1) << (L - 1);
        const u64 hi = u64(1) << L;
        u64 hits = 0;
        u64 pairs = 0;
        const u128 mask = (u128(1) << L) - 1;
        #pragma omp parallel for schedule(static) reduction(+:hits,pairs)
        for (u64 n = lo | 1; n < hi; n += 2) {
            if (witness.load(std::memory_order_relaxed)) continue;
            const u128 z = u128(n) * n;
            const int M = bitlen128(z);
            const int maxs = std::min(L - 1, M - L);
            int first = -1;
            for (int s = 3; s <= maxs; ++s) {
                if (((z >> s) & mask) != n) continue;
                ++hits;
                if (first >= 0) {
                    ++pairs;
                    witness.store(n, std::memory_order_relaxed);
                    break;
                }
                first = s;
            }
        }
        tested += u128(hi - lo) / 2;
        std::cout << "L=" << std::setw(2) << L
                  << " odd_tested=" << (hi-lo)/2
                  << " occurrences=" << hits
                  << " pairs=" << pairs << '\n' << std::flush;
    }
    if (u64 n = witness.load()) {
        std::cout << "COUNTEREXAMPLE " << n << '\n';
        return 2;
    }
    std::cout << "NO_ODD_COUNTEREXAMPLE maxL=" << maxL
              << " total_odd_tested=" << decimal(tested) << '\n';
}
