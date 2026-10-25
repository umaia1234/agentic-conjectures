// Method C: S(k) straight from the definition (no identities used),
//   S(k) = sum_{h=1}^{k-1} sum_{j=1}^{k-1} (-1)^(j + 1 + floor(h*j/k)),
// with floor(h*j/k) computed as the integer quotient (h*j)/k. Primes k in [lo,hi],
// or every k in [lo,hi] when a third argument "all" is given.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int isprime(int64_t n) {
  if (n < 2) return 0;
  for (int64_t d = 2; d * d <= n; d++) if (n % d == 0) return 0;
  return 1;
}
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s lo hi [all]\n", argv[0]); return 1; }
  int64_t lo = atoll(argv[1]), hi = atoll(argv[2]);
  int all = (argc > 3 && strcmp(argv[3], "all") == 0);
  for (int64_t k = lo; k <= hi; k++) {
    if (k < 1 || (!all && !isprime(k))) continue;
    int64_t S = 0;
    for (int64_t h = 1; h <= k - 1; h++)
      for (int64_t j = 1; j <= k - 1; j++)
        S += ((j + 1 + (h * j) / k) & 1) ? -1 : 1;
    printf("%lld %lld\n", (long long)k, (long long)S);
  }
  return 0;
}
