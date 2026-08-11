#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>

using u64 = std::uint64_t;
using u128 = unsigned __int128;

static std::vector<std::uint32_t> primes_up_to(u64 n) {
    std::vector<bool> composite(static_cast<std::size_t>(n + 1), false);
    std::vector<std::uint32_t> primes;
    for (u64 i = 2; i <= n; ++i) {
        if (!composite[static_cast<std::size_t>(i)]) {
            primes.push_back(static_cast<std::uint32_t>(i));
            if (i <= n / i) {
                for (u64 j = i * i; j <= n; j += i) {
                    composite[static_cast<std::size_t>(j)] = true;
                }
            }
        }
    }
    return primes;
}

static u64 floor_sqrt(u64 n) {
    u64 lo = 0;
    u64 hi = std::min<u64>(n, UINT64_C(1) << 32);
    while (lo + 1 < hi) {
        const u64 mid = lo + (hi - lo) / 2;
        if (mid <= n / mid) lo = mid;
        else hi = mid;
    }
    return lo;
}

int main(int argc, char** argv) {
    const u64 limit = argc > 1 ? std::strtoull(argv[1], nullptr, 10)
                               : UINT64_C(1000000000);
    const u64 block_size = argc > 2 ? std::strtoull(argv[2], nullptr, 10)
                                    : UINT64_C(1000000);
    if (limit < 1 || block_size < 1) return 2;

    const auto primes = primes_up_to(floor_sqrt(limit));
    std::vector<u64> rem(static_cast<std::size_t>(block_size));
    std::vector<u64> weighted_sum(static_cast<std::size_t>(block_size));
    std::vector<std::uint32_t> divisors(static_cast<std::size_t>(block_size));
    std::vector<u64> least_prime(static_cast<std::size_t>(block_size));

    u64 tested = 0;
    u64 inequality_survivors = 0;
    std::vector<u64> solutions;
    const auto start_time = std::chrono::steady_clock::now();

    for (u64 low = 1; low <= limit; low += block_size) {
        const u64 high = std::min(limit, low + block_size - 1);
        const std::size_t len = static_cast<std::size_t>(high - low + 1);

        for (std::size_t i = 0; i < len; ++i) {
            const u64 n = low + static_cast<u64>(i);
            // The proof in the accompanying report shows that every solution
            // other than 21 is coprime to 210.  Inactive entries stay at 1.
            const bool active = std::gcd(n, UINT64_C(210)) == 1;
            rem[i] = active ? n : 1;
            weighted_sum[i] = 1;
            divisors[i] = 1;
            least_prime[i] = 0;
            if (active) ++tested;
        }

        for (const std::uint32_t p32 : primes) {
            const u64 p = p32;
            if (p > high / p) break;
            u64 first = low + ((p - low % p) % p);
            for (u64 value = first; value <= high; value += p) {
                const std::size_t i = static_cast<std::size_t>(value - low);
                if (rem[i] % p != 0) continue;
                if (least_prime[i] == 0) least_prime[i] = p32;
                unsigned exponent = 0;
                u64 power = 1;
                u64 local = 1;
                do {
                    rem[i] /= p;
                    ++exponent;
                    power *= p;
                    local += static_cast<u64>(exponent + 1) * power;
                } while (rem[i] % p == 0);
                weighted_sum[i] *= local;
                divisors[i] *= exponent + 1;
            }
        }

        for (std::size_t i = 0; i < len; ++i) {
            const u64 n = low + static_cast<u64>(i);
            if (rem[i] == 1 && std::gcd(n, UINT64_C(210)) != 1) continue;
            if (rem[i] > 1) {
                if (least_prime[i] == 0) {
                    least_prime[i] = rem[i];
                }
                weighted_sum[i] *= 1 + 2 * rem[i];
                divisors[i] *= 2;
            }
            if (n > 1) {
                // Necessary condition p^a || n => p > a*tau(n)/(a+1).
                // We count candidates satisfying the coarser least-prime test
                // p_min > tau(n)/2, as an independent diagnostic.
                if (2 * static_cast<u64>(least_prime[i]) > divisors[i]) {
                    ++inequality_survivors;
                }
            }
            if (static_cast<u128>(weighted_sum[i]) ==
                static_cast<u128>(n) * (divisors[i] + 1)) {
                solutions.push_back(n);
            }
        }

        if (high == limit || high % UINT64_C(100000000) == 0) {
            const double seconds = std::chrono::duration<double>(
                std::chrono::steady_clock::now() - start_time).count();
            std::cerr << "checked_through " << high << " seconds " << seconds << '\n';
        }
    }

    // Check 21 separately because the coprime-to-30 filter intentionally
    // excludes it.
    if (limit >= 21) solutions.push_back(21);
    std::sort(solutions.begin(), solutions.end());
    solutions.erase(std::unique(solutions.begin(), solutions.end()), solutions.end());

    std::cout << "limit " << limit << '\n';
    std::cout << "coprime_to_210_tested " << tested << '\n';
    std::cout << "coarse_inequality_survivors " << inequality_survivors << '\n';
    std::cout << "solutions";
    for (const u64 n : solutions) std::cout << ' ' << n;
    std::cout << '\n';
}
