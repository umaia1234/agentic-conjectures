#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

// Independent finite experiment for Erdos problem #430.
// For composite m, every n in [m+1, m+spf(m)-1] has the required
// composite witness m, since every prime factor of m is > n-m.
int main(int argc, char** argv) {
    std::uint32_t limit = 10000000;
    if (argc > 1) limit = static_cast<std::uint32_t>(std::strtoul(argv[1], nullptr, 10));

    std::vector<std::uint32_t> spf(limit + 1, 0), primes;
    primes.reserve(limit / 10);
    for (std::uint32_t i = 2; i <= limit; ++i) {
        if (spf[i] == 0) {
            spf[i] = i;
            primes.push_back(i);
        }
        for (std::uint32_t p : primes) {
            std::uint64_t v = std::uint64_t(i) * p;
            if (v > limit || p > spf[i]) break;
            spf[static_cast<std::uint32_t>(v)] = p;
        }
    }

    std::uint64_t farthest = 0;
    std::uint32_t farthest_witness = 0;
    std::vector<std::uint32_t> exceptional;
    std::uint32_t max_min_gap = 0, max_gap_n = 0, max_gap_witness = 0;
    std::uint64_t covered = 0;
    const std::vector<std::int64_t> thresholds{0, 1, 2, 3, 5, 10, 20, 50, 100, 200, 500, 1000};
    std::vector<std::uint32_t> last_at_most(thresholds.size(), 0);
    for (std::uint32_t n = 3; n <= limit; ++n) {
        std::uint32_t m = n - 1;
        if (spf[m] != m) {
            std::uint64_t endpoint = std::uint64_t(m) + spf[m] - 1;
            if (endpoint > farthest) {
                farthest = endpoint;
                farthest_witness = m;
            }
        }
        if (farthest < n) {
            exceptional.push_back(n);
        } else {
            ++covered;
            std::uint32_t gap = n - farthest_witness;
            if (gap > max_min_gap) {
                max_min_gap = gap;
                max_gap_n = n;
                max_gap_witness = farthest_witness;
            }
        }
        // farthest is max(m + spf(m) - 1), so F(n)-n=farthest+1-n.
        std::int64_t slack = static_cast<std::int64_t>(farthest + 1) - n;
        auto it = std::lower_bound(thresholds.begin(), thresholds.end(), slack);
        for (std::size_t j = static_cast<std::size_t>(it - thresholds.begin());
             j < thresholds.size(); ++j)
            last_at_most[j] = n;
    }

    std::cout << "limit " << limit << "\n";
    std::cout << "covered " << covered << " exceptional " << exceptional.size() << "\n";
    std::cout << "exceptional:";
    for (auto n : exceptional) std::cout << ' ' << n;
    std::cout << "\n";
    std::cout << "last_exceptional " << (exceptional.empty() ? 0 : exceptional.back()) << "\n";
    std::cout << "max_selected_gap " << max_min_gap << " at_n " << max_gap_n
              << " witness " << max_gap_witness << " spf "
              << (max_gap_witness ? spf[max_gap_witness] : 0) << "\n";
    std::cout << "last_n_with_slack_at_most:";
    for (std::size_t j = 0; j < thresholds.size(); ++j)
        std::cout << ' ' << thresholds[j] << ':' << last_at_most[j];
    std::cout << "\n";
}
