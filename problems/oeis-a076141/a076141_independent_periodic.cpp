#include <algorithm>
#include <atomic>
#include <cstdint>
#include <iomanip>
#include <immintrin.h>
#include <iostream>
#include <string>

using u64 = std::uint64_t;
using u128 = unsigned __int128;

static std::string decimal(u128 x) {
    if (!x) return "0";
    std::string s;
    while (x) { s.push_back(char('0' + x % 10)); x /= 10; }
    std::reverse(s.begin(), s.end());
    return s;
}

int main(int argc, char** argv) {
    const int minL = argc > 1 ? std::stoi(argv[1]) : 3;
    const int maxL = argc > 2 ? std::stoi(argv[2]) : 35;
    if (minL < 3 || maxL > 62 || minL > maxL) return 1;
    std::atomic<u64> witness{0};
    std::atomic<int> witness_s{-1}, witness_t{-1};
    u128 all_candidates = 0;
    for (int L=minL; L<=maxL && !witness.load(); ++L) {
        const u128 wordmask = (u128(1) << L) - 1;
        u128 level_candidates = 0;
        u64 pair_specs = 0;
        // k=L-d is the overlap length.  Odd nontrivial occurrences have
        // 3 <= s < t <= L-1, hence k>=4 and 3<=s<=k-1.
        for (int k=4; k<=L-1 && !witness.load(); ++k) {
            const int d=L-k;
            const u64 dmask=(u64(1)<<d)-1;
            const int topclass=(L-1)%d;
            const u64 required=(u64(1)<<0) | (u64(1)<<topclass);
            const u64 free_mask=dmask & ~required;
            const int free_count=__builtin_popcountll(free_mask);
            const u64 limit=u64(1)<<free_count;

            const int q=L/d, r=L%d;
            u64 repunit=0;
            for (int j=0;j<q;++j) repunit |= u64(1) << (j*d);
            const u64 rmask=r ? ((u64(1)<<r)-1) : 0;

            for (int s=3; s<=k-1 && !witness.load(); ++s) {
                const int t=s+d;
                ++pair_specs;
                u64 checked=0;
                #pragma omp parallel for if(limit >= (u64(1)<<18)) schedule(static) reduction(+:checked)
                for (u64 x=0; x<limit; ++x) {
                    if (witness.load(std::memory_order_relaxed)) continue;
                    const u64 u=_pdep_u64(x, free_mask) | required;
                    const u64 n=u*repunit + (r ? ((u&rmask) << (q*d)) : 0);
                    const u128 z=u128(n)*n;
                    ++checked;
                    if (((z>>s)&wordmask)==n && ((z>>t)&wordmask)==n) {
                        witness.store(n, std::memory_order_relaxed);
                        witness_s.store(s, std::memory_order_relaxed);
                        witness_t.store(t, std::memory_order_relaxed);
                    }
                }
                level_candidates += checked;
            }
        }
        all_candidates += level_candidates;
        std::cout << "L=" << std::setw(2) << L
                  << " pair_specs=" << pair_specs
                  << " candidates=" << decimal(level_candidates) << '\n' << std::flush;
    }
    if (u64 n=witness.load()) {
        std::cout << "COUNTEREXAMPLE n=" << n
                  << " s=" << witness_s.load()
                  << " t=" << witness_t.load() << '\n';
        return 2;
    }
    std::cout << "NO_PERIODIC_COUNTEREXAMPLE through_L=" << maxL
              << " tested_pair_candidates=" << decimal(all_candidates) << '\n';
}
