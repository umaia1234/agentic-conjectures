#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>

// Exact ascending generator for Erdős problem #424.
// For n >= 4, n is generated iff n + 1 = xy for two distinct, previously
// generated integers x,y.  Both factors are then strictly smaller than n.

int main(int argc, char **argv) {
    const int limit = argc > 1 ? std::atoi(argv[1]) : 1000000;
    const int max_modulus = argc > 2 ? std::atoi(argv[2]) : 500;

    std::vector<int> spf(limit + 2);
    std::iota(spf.begin(), spf.end(), 0);
    for (int p = 2; 1LL * p * p <= limit + 1; ++p) {
        if (spf[p] != p) continue;
        for (int m = p * p; m <= limit + 1; m += p) {
            if (spf[m] == m) spf[m] = p;
        }
    }

    std::vector<std::uint8_t> generated(limit + 1, 0);
    generated[2] = generated[3] = 1;
    std::uint64_t count = 2;
    int last_missing_0_mod_3 = 0;
    int last_missing_2_mod_3 = 0;

    std::vector<int> divisors;
    std::vector<std::pair<int, int>> factorization;
    for (int n = 4; n <= limit; ++n) {
        int value = n + 1;
        factorization.clear();
        while (value > 1) {
            int p = spf[value], exponent = 0;
            do {
                value /= p;
                ++exponent;
            } while (value > 1 && spf[value] == p);
            factorization.emplace_back(p, exponent);
        }

        divisors.assign(1, 1);
        for (auto [p, exponent] : factorization) {
            const std::size_t old_size = divisors.size();
            int power = 1;
            for (int e = 1; e <= exponent; ++e) {
                power *= p;
                for (std::size_t i = 0; i < old_size; ++i) {
                    divisors.push_back(divisors[i] * power);
                }
            }
        }

        bool appears = false;
        for (int x : divisors) {
            const int y = (n + 1) / x;
            if (x >= y) continue;
            if (x >= 2 && generated[x] && generated[y]) {
                appears = true;
                break;
            }
        }
        if (appears) {
            generated[n] = 1;
            ++count;
        } else if (n % 3 == 0) {
            last_missing_0_mod_3 = n;
        } else if (n % 3 == 2) {
            last_missing_2_mod_3 = n;
        }
    }

    std::cout << "limit " << limit << " count " << count << " density "
              << static_cast<long double>(count) / limit << '\n';
    std::cout << "last missing residues mod 3: r0=" << last_missing_0_mod_3
              << " r2=" << last_missing_2_mod_3 << '\n';

    // Look for residue classes whose last missing member is unusually small.
    for (int modulus = 2; modulus <= max_modulus; ++modulus) {
        std::vector<int> last_missing(modulus, 0), class_count(modulus, 0);
        for (int n = 2; n <= limit; ++n) {
            if (generated[n]) {
                ++class_count[n % modulus];
            } else {
                last_missing[n % modulus] = n;
            }
        }
        for (int residue = 0; residue < modulus; ++residue) {
            if (last_missing[residue] > 0 && last_missing[residue] <= limit / 1000) {
                std::cout << "candidate class " << residue << " mod " << modulus
                          << " last_missing " << last_missing[residue]
                          << " generated_count " << class_count[residue] << '\n';
            }
        }
    }
}
