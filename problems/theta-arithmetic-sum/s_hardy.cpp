// Method B: S(k) for odd primes k via the reciprocity form (DETAILS.md, section 4)
//   S(k) = sum_{h odd, 1<=h<=k-2} s4(h,k),
//   12h*s4(h,k) = 12k - 12h + 4*T(c,h) - 8*T(2c mod h,h),  c = k mod h,
// where T(c,h) = 12h*s(c,h) is computed by Dedekind reciprocity:
//   c*T(c,h) + h*T(h mod c,c) = c^2 + h^2 + 1 - 3ch,   T(1,h) = (h-1)(h-2).
// Every division is checked to be exact and every product to fit in int64.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static void die(const char *what, int64_t a, int64_t b) {
  fprintf(stderr, "%s at (%lld,%lld)\n", what, (long long)a, (long long)b);
  exit(2);
}
static int64_t mul(int64_t a, int64_t b) {
  int64_t r;
  if (__builtin_mul_overflow(a, b, &r)) die("overflow", a, b);
  return r;
}
static int64_t T(int64_t c, int64_t h) {        // 0 < c < h, gcd(c,h) = 1
  if (c == 1) return mul(h - 1, h - 2);
  int64_t num = mul(c, c) + mul(h, h) + 1 - mul(3, mul(c, h)) - mul(h, T(h % c, c));
  if (num % c != 0) die("T not integral", c, h);
  return num / c;
}
static int isprime(int64_t n) {
  if (n < 2) return 0;
  for (int64_t d = 2; d * d <= n; d++) if (n % d == 0) return 0;
  return 1;
}
int main(int argc, char **argv) {
  if (argc != 3) { fprintf(stderr, "usage: %s lo hi\n", argv[0]); return 1; }
  int64_t lo = atoll(argv[1]), hi = atoll(argv[2]);
  if (hi > 2000000) { fprintf(stderr, "hi > 2e6: int64 bounds not checked beyond\n"); return 1; }
  for (int64_t k = lo; k <= hi; k++) {
    if (k < 3 || !isprime(k)) continue;
    int64_t S = k - 1;                           // h = 1: s4(1,k) = k - 1
    for (int64_t h = 3; h <= k - 2; h += 2) {
      int64_t c = k % h, c2 = (2 * c) % h;
      int64_t num = 12 * k - 12 * h + 4 * T(c, h) - 8 * T(c2, h);
      if (num % (12 * h) != 0) die("s4 not integral", k, h);
      S += num / (12 * h);
    }
    printf("%lld %lld\n", (long long)k, (long long)S);
  }
  return 0;
}
