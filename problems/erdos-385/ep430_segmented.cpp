#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

// Segmented independent search for the exceptional n in Erdos #385/#430.
// Only odd composites m matter for even n; every odd n is covered by m=n-1.
int main(int argc, char** argv) {
    std::uint64_t limit = 1000000000ULL;
    if (argc > 1) limit = std::strtoull(argv[1], nullptr, 10);
    const std::uint64_t span = 16000000ULL;

    std::uint32_t root = static_cast<std::uint32_t>(std::sqrt((long double)limit)) + 1;
    std::vector<bool> is_prime(root + 1, true);
    is_prime[0] = is_prime[1] = false;
    std::vector<std::uint32_t> primes;
    for (std::uint32_t i = 2; i <= root; ++i) {
        if (!is_prime[i]) continue;
        primes.push_back(i);
        if (std::uint64_t(i) * i <= root)
            for (std::uint64_t j = std::uint64_t(i) * i; j <= root; j += i)
                is_prime[static_cast<std::size_t>(j)] = false;
    }

    std::uint64_t farthest_endpoint = 0;
    std::uint64_t record_witness = 0;
    std::vector<std::uint64_t> exceptional;
    std::uint64_t processed_odd = 0;
    const std::vector<std::uint64_t> thresholds{0, 1, 2, 3, 5, 10, 20, 50, 100, 200, 500, 1000};
    std::vector<std::uint64_t> last_at_most(thresholds.size(), 0);

    auto record_slack = [&](std::uint64_t n, std::uint64_t slack) {
        if (n < 6 || n > limit) return;
        auto it = std::lower_bound(thresholds.begin(), thresholds.end(), slack);
        for (std::size_t j = static_cast<std::size_t>(it - thresholds.begin());
             j < thresholds.size(); ++j)
            last_at_most[j] = n;
    };

    for (std::uint64_t block_low = 3; block_low < limit; block_low += span) {
        std::uint64_t low = block_low | 1ULL;
        std::uint64_t high = std::min(limit, block_low + span);
        std::size_t count = static_cast<std::size_t>((high - low + 1) / 2);
        std::vector<std::uint16_t> spf(count, 0);

        for (std::uint32_t p : primes) {
            if (p == 2) continue;
            std::uint64_t pp = std::uint64_t(p) * p;
            if (pp >= high && p > (high - 1) / p) break;
            std::uint64_t first = ((low + p - 1) / p) * p;
            if (first < pp) first = pp;
            if ((first & 1ULL) == 0) first += p;
            for (std::uint64_t m = first; m < high; m += 2ULL * p) {
                std::size_t idx = static_cast<std::size_t>((m - low) / 2);
                if (spf[idx] == 0) spf[idx] = static_cast<std::uint16_t>(p);
            }
        }

        for (std::size_t i = 0; i < count; ++i) {
            std::uint64_t m = low + 2ULL * i;
            if (m >= limit) break;
            ++processed_odd;
            if (spf[i] != 0) {
                std::uint64_t endpoint = m + spf[i] - 1ULL;
                if (endpoint > farthest_endpoint) {
                    farthest_endpoint = endpoint;
                    record_witness = m;
                }
            }
            std::uint64_t n = m + 1;
            std::uint64_t even_slack = farthest_endpoint < n ? 0 : farthest_endpoint + 1 - n;
            record_slack(n, even_slack);
            if (n >= 6 && n <= limit && even_slack == 0)
                exceptional.push_back(n);
            // The following odd n has the even composite n-1 available, hence
            // slack at least one; odd composite records may make it larger.
            std::uint64_t odd_n = m + 2;
            std::uint64_t odd_slack = std::max<std::uint64_t>(
                1, farthest_endpoint + 1 > odd_n ? farthest_endpoint + 1 - odd_n : 0);
            record_slack(odd_n, odd_slack);
        }
        std::cerr << "processed below " << high << ", last exceptional "
                  << (exceptional.empty() ? 0 : exceptional.back()) << "\n";
    }

    std::cout << "limit " << limit << " processed_odd " << processed_odd << "\n";
    std::cout << "exceptional_count " << exceptional.size() << "\n";
    std::cout << "exceptional:";
    for (std::uint64_t n : exceptional) std::cout << ' ' << n;
    std::cout << "\nlast_exceptional "
              << (exceptional.empty() ? 0 : exceptional.back()) << "\n";
    std::cout << "final_farthest_endpoint " << farthest_endpoint
              << " record_witness " << record_witness << "\n";
    std::cout << "last_n_with_slack_at_most:";
    for (std::size_t j = 0; j < thresholds.size(); ++j)
        std::cout << ' ' << thresholds[j] << ':' << last_at_most[j];
    std::cout << "\n";
}
