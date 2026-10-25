// Method A: S(k) for odd primes k from the Dedekind-sum closed form (DETAILS.md, section 3)
//   S(k) = sum_{m=1}^{(k-1)/2} [8 s(m,k) - 20 s(2m mod k, k) + 8 s(4m mod k, k)],
// where each 12k s(h,k) is an integer evaluated exactly by the continued-fraction formula
//   12k s(h,k) = h + h' + k (q_1 - q_2 + ... + (-1)^(r+1) q_r - 2 + (-1)^r),
// k/h = [q_1; q_2, ..., q_r] from Euclid's algorithm on (k, h) and h h' = 1 (mod k), 0 < h' < k.
// The total is accumulated in __int128 and checked to be divisible by 12k.
// Usage: s_dedekind lo hi    prints "k S(k)" for every prime k >= 3 in [lo, hi].
#include <cstdint>
#include <cstdio>
#include <cstdlib>
typedef __int128 i128;
static int64_t X12(int64_t h, int64_t k) {  // 12 k s(h,k), 0 < h < k, gcd(h,k) = 1
  int64_t r0 = k, r1 = h, t0 = 0, t1 = 1, alt = 0;
  int sgn = 1, r = 0;
  while (r1) {  // invariant: r_i = t_i h (mod k)
    int64_t q = r0 / r1, r2 = r0 - q * r1, t2 = t0 - q * t1;
    alt += sgn * q; sgn = -sgn; r++;
    r0 = r1; r1 = r2; t0 = t1; t1 = t2;
  }
  int64_t hinv = t0 % k; if (hinv < 0) hinv += k;  // r0 = 1 = t0 h (mod k)
  return h + hinv + k * (alt - 2 + (r % 2 == 0 ? 1 : -1));
}
static int isprime(int64_t n) {
  if (n < 2) return 0;
  for (int64_t d = 2; d * d <= n; d++) if (n % d == 0) return 0;
  return 1;
}
int main(int argc, char **argv) {
  if (argc != 3) { fprintf(stderr, "usage: %s lo hi\n", argv[0]); return 1; }
  int64_t lo = atoll(argv[1]), hi = atoll(argv[2]);
  if (hi > 100000000) { fprintf(stderr, "hi > 1e8: int64 bounds not checked beyond\n"); return 1; }
  for (int64_t k = lo; k <= hi; k++) {
    if (k < 3 || !isprime(k)) continue;
    int64_t n = (k - 1) / 2; i128 tot = 0;
    for (int64_t m = 1; m <= n; m++)
      tot += 8 * (i128)X12(m, k) - 20 * (i128)X12((2 * m) % k, k) + 8 * (i128)X12((4 * m) % k, k);
    i128 kk = 12 * (i128)k;
    if (tot % kk != 0) { fprintf(stderr, "not divisible by 12k at k=%lld\n", (long long)k); return 2; }
    printf("%lld %lld\n", (long long)k, (long long)(tot / kk));
  }
  return 0;
}
