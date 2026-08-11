#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

static std::int64_t mod_pow(std::int64_t a, std::int64_t e, int mod) {
  std::int64_t out = 1;
  while (e) {
    if (e & 1) out = out * a % mod;
    a = a * a % mod;
    e >>= 1;
  }
  return out;
}

int main(int argc, char** argv) {
  const int begin = argc > 1 ? std::atoi(argv[1]) : 30001;
  const int end = argc > 2 ? std::atoi(argv[2]) : 40000;
  const int prime_bound = argc > 3 ? std::atoi(argv[3]) : 100000;
  constexpr int K = 201886;
  const int count = end - begin + 1;
  std::vector<bool> composite(prime_bound + 1);
  std::vector<int> primes;
  for (int i = 2; i <= prime_bound; ++i) {
    if (!composite[i]) primes.push_back(i);
    for (int p : primes) {
      if (1LL * i * p > prime_bound) break;
      composite[i * p] = true;
      if (i % p == 0) break;
    }
  }

  std::vector<bool> survives(count, true);
  for (int p : primes) {
    if (p == 2 || p == 3) continue;
    std::int64_t value = (K % p) * mod_pow(3, begin, p) % p;
    for (int i = 0; i < count; ++i) {
      if (value == 1) survives[i] = false;
      value = value * 3 % p;
    }
  }
  int total = 0;
  for (int i = 0; i < count; ++i)
    if (survives[i]) {
      std::cout << begin + i << '\n';
      ++total;
    }
  std::cerr << "range=" << begin << ".." << end
            << " prime_bound=" << prime_bound << " survivors=" << total << '\n';
}
