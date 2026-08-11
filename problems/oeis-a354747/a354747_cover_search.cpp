#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>

struct Class {
  int residue;  // 0 <= residue < order
  int order;
  int prime;
};

static std::int64_t mod_pow(std::int64_t a, std::int64_t e, int mod) {
  std::int64_t ans = 1;
  while (e) {
    if (e & 1) ans = ans * a % mod;
    a = a * a % mod;
    e >>= 1;
  }
  return ans;
}

int main(int argc, char** argv) {
  const int L = argc > 1 ? std::atoi(argv[1]) : 2520;
  const int bound = argc > 2 ? std::atoi(argv[2]) : 20000000;
  constexpr int K = 201886;
  std::vector<bool> composite(bound + 1);
  std::vector<int> primes;
  for (int i = 2; i <= bound; ++i) {
    if (!composite[i]) primes.push_back(i);
    for (int p : primes) {
      if (1LL * i * p > bound) break;
      composite[i * p] = true;
      if (i % p == 0) break;
    }
  }

  std::vector<Class> classes;
  for (int p : primes) {
    if (p == 2 || p == 3 || K % p == 0) continue;
    if (mod_pow(3, L, p) != 1) continue;
    int order = L;
    int x = order;
    for (int q = 2; 1LL * q * q <= x; ++q) {
      if (x % q) continue;
      while (x % q == 0) x /= q;
      while (order % q == 0 && mod_pow(3, order / q, p) == 1) order /= q;
    }
    if (x > 1)
      while (order % x == 0 && mod_pow(3, order / x, p) == 1) order /= x;

    const int target = mod_pow(K, p - 2, p);
    std::int64_t power = 1;
    int residue = -1;
    for (int r = 0; r < order; ++r) {
      if (power == target) {
        residue = r;
        break;
      }
      power = power * 3 % p;
    }
    if (residue >= 0) classes.push_back({residue, order, p});
  }
  std::cerr << "L=" << L << " bound=" << bound << " classes=" << classes.size()
            << '\n';

  std::vector<bool> covered(L, false);
  std::vector<Class> chosen;
  while (true) {
    int remaining = 0;
    for (bool v : covered) remaining += !v;
    if (!remaining) break;
    int best = -1, best_gain = 0;
    for (int i = 0; i < static_cast<int>(classes.size()); ++i) {
      int gain = 0;
      for (int r = classes[i].residue; r < L; r += classes[i].order)
        gain += !covered[r];
      if (gain > best_gain ||
          (gain == best_gain && best >= 0 && classes[i].prime < classes[best].prime)) {
        best = i;
        best_gain = gain;
      }
    }
    if (best < 0 || best_gain == 0) {
      std::cerr << "GREEDY STUCK remaining=" << remaining << " residues:";
      int shown = 0;
      for (int r = 0; r < L && shown < 100; ++r)
        if (!covered[r]) {
          std::cerr << ' ' << r;
          ++shown;
        }
      std::cerr << '\n';
      return 1;
    }
    const Class c = classes[best];
    chosen.push_back(c);
    for (int r = c.residue; r < L; r += c.order) covered[r] = true;
    std::cerr << "choose m=" << c.residue << " mod " << c.order
              << " p=" << c.prime << " gain=" << best_gain
              << " remaining=" << remaining - best_gain << '\n';
  }

  std::cout << "COVER FOUND size=" << chosen.size() << '\n';
  for (const auto& c : chosen)
    std::cout << c.residue << ' ' << c.order << ' ' << c.prime << '\n';
}
