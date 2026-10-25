/*
 * Direct enumeration for (a + r)/b + (b + r)/a = k with a, b positive and k an integer.
 *
 * Usage: vieta_brute N [r]      (r defaults to 2)
 *
 * Tests every pair 1 <= a <= b <= N for a*b | a^2 + r a + b^2 + r b and prints each solution
 * as "a b k g m", where g = gcd(a, b) and m = r (a + b) / g^2. It then prints the values m
 * seen for each k.
 *
 * Checks, with exit status 1 on any failure:
 *   - m is an integer and divides r (k + 2), and 3 <= k <= 2 r + 2;
 *   - for r = 2 (Conjecture 4.2 of arXiv:2605.19083v2): k is 3, 4 or 6, the values for
 *     k = 3, 4, 6 lie in {1, 5}, {2, 3}, {4, 8}, and once N >= 6 each of these six values
 *     occurs.
 */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

#define MAX_SOLUTIONS 1000000

typedef struct {
  uint64_t k, m;
} km_t;

static uint64_t gcd_u64(uint64_t x, uint64_t y) {
  while (y != 0) {
    uint64_t t = x % y;
    x = y;
    y = t;
  }
  return x;
}

static int cmp_km(const void *p, const void *q) {
  const km_t *s = p, *t = q;
  if (s->k != t->k) return s->k < t->k ? -1 : 1;
  if (s->m != t->m) return s->m < t->m ? -1 : 1;
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 2 || argc > 3) {
    fprintf(stderr, "usage: %s N [r]\n", argv[0]);
    return 2;
  }
  uint64_t n = strtoull(argv[1], NULL, 10);
  uint64_t r = argc == 3 ? strtoull(argv[2], NULL, 10) : 2;
  if (n < 1 || n > 1000000 || r < 1 || r > 1000) {
    fprintf(stderr, "need 1 <= N <= 1000000 and 1 <= r <= 1000\n");
    return 2;
  }
  km_t *seen = malloc(sizeof(km_t) * MAX_SOLUTIONS);
  if (seen == NULL) return 2;
  size_t count = 0;
  int failures = 0;

  printf("# r = %" PRIu64 ", 1 <= a <= b <= %" PRIu64 "\n# a b k g m\n", r, n);
  for (uint64_t a = 1; a <= n; a++) {
    uint64_t fa = a * a + r * a;
    for (uint64_t b = a; b <= n; b++) {
      uint64_t num = fa + b * b + r * b;
      uint64_t ab = a * b;
      if (num % ab != 0) continue;
      uint64_t k = num / ab;
      uint64_t g = gcd_u64(a, b);
      uint64_t top = r * (a + b);
      if (top % (g * g) != 0) {
        printf("FAIL: value not an integer at a=%" PRIu64 " b=%" PRIu64 "\n", a, b);
        failures++;
        continue;
      }
      uint64_t m = top / (g * g);
      printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n", a, b, k, g, m);
      if ((r * (k + 2)) % m != 0 || k < 3 || k > 2 * r + 2) {
        printf("FAIL: m does not divide r(k+2), or k out of range\n");
        failures++;
      }
      if (r == 2) {
        int ok = (k == 3 && (m == 1 || m == 5)) || (k == 4 && (m == 2 || m == 3)) ||
                 (k == 6 && (m == 4 || m == 8));
        if (!ok) {
          printf("FAIL: (k, m) not allowed by Conjecture 4.2\n");
          failures++;
        }
      }
      if (count == MAX_SOLUTIONS) {
        fprintf(stderr, "too many solutions\n");
        return 2;
      }
      seen[count].k = k;
      seen[count].m = m;
      count++;
    }
  }

  qsort(seen, count, sizeof(km_t), cmp_km);
  printf("# %zu solutions\n# values of m for each k:\n", count);
  size_t distinct = 0;
  for (size_t i = 0; i < count; i++) {
    if (i == 0 || seen[i].k != seen[i - 1].k) {
      if (i > 0) printf("\n");
      printf("k=%" PRIu64 ":", seen[i].k);
    }
    if (i == 0 || cmp_km(&seen[i], &seen[i - 1]) != 0) {
      printf(" %" PRIu64, seen[i].m);
      distinct++;
    }
  }
  if (count > 0) printf("\n");
  if (r == 2 && n >= 6 && distinct != 6) {
    printf("FAIL: expected the six values of Conjecture 4.2, found %zu (k, m) pairs\n", distinct);
    failures++;
  }
  free(seen);
  printf("# failures: %d\n", failures);
  return failures == 0 ? 0 : 1;
}
