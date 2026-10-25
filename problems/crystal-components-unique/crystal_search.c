// Collision search for crystal factorizations n = a*b <= X (implementation A, C, u128).
//
// Parametrization (Lean: AgenticConjectures.CrystalComponentsUnique): the crystal pairs are
// exactly {2*k*p^2 - 1, 2*(p+r)^2 - 1} with p, r >= 1 and (p+r)^2 = k*p*r + 1, and the
// positive solutions (p, r) are consecutive terms of the Lucas sequence U(k-2):
// U_0 = 0, U_1 = 1, U_{i+1} = (k-2) U_i - U_{i-1}; (p, r) = (U_i, U_{i+1}) is family
// j = 2i-1 and (U_{i+1}, U_i) is family j = 2i.  Disjoint classes:
//   F3: k = 3          -> n = 35 only
//   F4: k = 4          -> n = (2s^2-1)(2(s+1)^2-1), s >= 2      (p, r consecutive integers)
//   F1: k >= 5, j = 1  -> n = (2k-1)(2(k-1)^2-1)
//   S : k >= 5, j >= 2 -> enumerated from the Lucas pairs, sorted
// Checks: S vs S (sort), S vs F1/F4/F3 and F4 vs F1/F3 (exact inversion).
// F1 vs F1 and F4 vs F4 cannot collide: both formulas are strictly increasing.
// Arithmetic saturates at 2^128-1 and X <= 2^127-1, so a saturated value is > X.
//
// Usage: crystal_search X [threads]   X decimal, or 1eNN, or max (= 2^127-1)
#include <math.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef unsigned __int128 u128;
typedef uint64_t u64;
static const u128 SAT = ~(u128)0;
static u128 X;

static inline u128 mulS(u128 a, u128 b) { u128 r; return __builtin_mul_overflow(a, b, &r) ? SAT : r; }
static inline u128 addS(u128 a, u128 b) { u128 r; return __builtin_add_overflow(a, b, &r) ? SAT : r; }
static inline u128 decS(u128 a) { return a == SAT ? SAT : a - 1; }  // a >= 1 always here

// 2*k*p^2 - 1 and 2*x^2 - 1, saturating
static inline u128 compA(u128 k, u128 p) { return decS(mulS(2, mulS(k, mulS(p, p)))); }
static inline u128 compB(u128 x) { return decS(mulS(2, mulS(x, x))); }
static inline u128 crystalN(u128 k, u128 p, u128 r) { return mulS(compA(k, p), compB(addS(p, r))); }

static inline u128 f1(u128 k) { return crystalN(k, 1, k - 2); }   // k >= 3
static inline u128 f4(u128 s) { return mulS(compB(s), compB(s + 1)); }

static void put128(u128 v, char *buf) {
  char t[48]; int i = 0;
  if (!v) { strcpy(buf, "0"); return; }
  while (v) { t[i++] = (char)('0' + (int)(v % 10)); v /= 10; }
  for (int j = 0; j < i; j++) buf[j] = t[i - 1 - j];
  buf[i] = 0;
}
static int parse128(const char *s, u128 *out) {
  if (!strcmp(s, "max")) { *out = (((u128)1) << 127) - 1; return 1; }
  if (s[0] == '1' && s[1] == 'e') {
    int e = atoi(s + 2); if (e < 0 || e > 38) return 0;
    u128 v = 1; for (int i = 0; i < e; i++) v *= 10; *out = v; return 1;
  }
  u128 v = 0;
  for (const char *c = s; *c; c++) {
    if (*c < '0' || *c > '9') return 0;
    v = mulS(v, 10); v = addS(v, (u128)(*c - '0'));
    if (v == SAT) return 0;
  }
  *out = v; return 1;
}

// exact inverses: return the index with f(index) == n, or 0
static u64 inv1(u128 n) {        // k >= 5 with f1(k) == n
  double est = cbrt((double)n / 4.0) + 1.0;
  u64 k = est < 3.0 ? 3 : (u64)est;
  while (k > 3 && f1(k) > n) k--;
  while (f1(k + 1) <= n) k++;
  return (k >= 5 && f1(k) == n) ? k : 0;
}
static u64 inv4(u128 n) {        // s >= 2 with f4(s) == n
  double est = pow((double)n / 4.0, 0.25);
  u64 s = est < 1.0 ? 1 : (u64)est;
  while (s > 1 && f4(s) > n) s--;
  while (f4(s + 1) <= n) s++;
  return (s >= 2 && f4(s) == n) ? s : 0;
}

typedef struct { u128 n; uint32_t k; uint16_t j; } rec_t;
static int cmp_rec(const void *a, const void *b) {
  u128 x = ((const rec_t *)a)->n, y = ((const rec_t *)b)->n;
  return x < y ? -1 : x > y ? 1 : 0;
}

static long long collisions = 0;
static pthread_mutex_t mtx = PTHREAD_MUTEX_INITIALIZER;
static void report(const char *what, u128 n) {
  char b[48]; put128(n, b);
  pthread_mutex_lock(&mtx); collisions++; printf("COLLISION %s n=%s\n", what, b); fflush(stdout);
  pthread_mutex_unlock(&mtx);
}

typedef struct { u64 lo, hi; u64 checked; } job_t;
static void *f4_worker(void *arg) {   // F4 members with s in [lo, hi) against F1 and F3
  job_t *jb = (job_t *)arg;
  for (u64 s = jb->lo; s < jb->hi; s++) {
    u128 n = f4(s);
    if (inv1(n)) report("F4 vs F1", n);
    if (n == 35) report("F4 vs F3", n);
    jb->checked++;
  }
  return NULL;
}

int main(int argc, char **argv) {
  if (argc < 2 || !parse128(argv[1], &X) || X > (((u128)1) << 127) - 1) {
    fprintf(stderr, "usage: %s X [threads]  (X <= 2^127-1; decimal, 1eNN or max)\n", argv[0]);
    return 2;
  }
  int threads = argc > 2 ? atoi(argv[2]) : 1;
  if (threads < 1) threads = 1;
  struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
  char bx[48]; put128(X, bx);

  // class sizes of F1, F4 and F3
  u64 kmax = 3; { double e = cbrt((double)X / 4.0) + 2.0; u64 k = (u64)e; if (k < 3) k = 3;
    while (k > 3 && f1(k) > X) k--; while (f1(k + 1) <= X) k++; kmax = f1(k) <= X ? k : 2; }
  u64 smax = 1; { double e = pow((double)X / 4.0, 0.25) + 2.0; u64 s = (u64)e; if (s < 1) s = 1;
    while (s > 1 && f4(s) > X) s--; while (f4(s + 1) <= X) s++; smax = f4(s) <= X ? s : 0; }
  u64 nF1 = kmax >= 5 ? kmax - 4 : 0, nF4 = smax >= 2 ? smax - 1 : 0, nF3 = X >= 35 ? 1 : 0;

  // S: k >= 5, j >= 2
  size_t cap = 1 << 20, cnt = 0;
  rec_t *A = malloc(cap * sizeof(rec_t));
  u64 sumlo = 0;  // sum of n over S, mod 2^64 (fingerprint shared with the Python implementation)
  int maxj = 0;
  for (u64 k = 5;; k++) {
    u128 c = k - 2, a = 1, b = c;  // (a, b) = (U_i, U_{i+1}), i = 1
    u128 last = 0;
    int any = 0;
    for (int i = 1;; i++) {
      for (int orient = 0; orient < 2; orient++) {
        int j = 2 * i - 1 + orient;
        if (j == 1) continue;
        u128 p = orient ? b : a, r = orient ? a : b;
        u128 n = crystalN(k, p, r);
        if (n > X) goto next_k;
        // invariant (p+r)^2 = k p r + 1 (no saturation here since n <= X)
        if ((p + r) * (p + r) != (u128)k * p * r + 1) { fprintf(stderr, "invariant fails\n"); return 1; }
        if (n <= last) { fprintf(stderr, "not increasing in j\n"); return 1; }
        last = n;
        if (cnt == cap) { cap *= 2; A = realloc(A, cap * sizeof(rec_t)); if (!A) return 3; }
        A[cnt].n = n; A[cnt].k = (uint32_t)k; A[cnt].j = (uint16_t)j; cnt++;
        sumlo += (u64)n;
        if (j > maxj) maxj = j;
        any = 1;
      }
      u128 cb = mulS(c, b), nb = cb == SAT ? SAT : cb - a;  // U_{i+2}; c*b > a as c >= 3, b > a
      a = b; b = nb;
    }
  next_k:
    if (!any) break;  // the j = 2 value already exceeds X, and it increases with k
  }
  qsort(A, cnt, sizeof(rec_t), cmp_rec);
  for (size_t i = 1; i < cnt; i++)
    if (A[i].n == A[i - 1].n) report("S vs S", A[i].n);
  for (size_t i = 0; i < cnt; i++) {
    if (inv1(A[i].n)) report("S vs F1", A[i].n);
    if (inv4(A[i].n)) report("S vs F4", A[i].n);
    if (A[i].n == 35) report("S vs F3", A[i].n);
  }

  // F4 vs F1 and F3, split over threads
  pthread_t th[64]; job_t jobs[64];
  if (threads > 64) threads = 64;
  u64 lo = 2, hi = smax + 1, span = (hi - lo + threads - 1) / threads;
  u64 f4checked = 0;
  for (int t = 0; t < threads; t++) {
    jobs[t].lo = lo + (u64)t * span; jobs[t].hi = jobs[t].lo + span;
    if (jobs[t].lo > hi) jobs[t].lo = hi;
    if (jobs[t].hi > hi) jobs[t].hi = hi;
    jobs[t].checked = 0;
    pthread_create(&th[t], NULL, f4_worker, &jobs[t]);
  }
  for (int t = 0; t < threads; t++) { pthread_join(th[t], NULL); f4checked += jobs[t].checked; }

  clock_gettime(CLOCK_MONOTONIC, &t1);
  double secs = (double)(t1.tv_sec - t0.tv_sec) + 1e-9 * (double)(t1.tv_nsec - t0.tv_nsec);
  printf("X=%s\n", bx);
  printf("F3 (k=3): %llu  F4 (k=4): %llu  F1 (k>=5, j=1): %llu  S (k>=5, j>=2): %zu  max j: %d\n",
         (unsigned long long)nF3, (unsigned long long)nF4, (unsigned long long)nF1, cnt, maxj);
  printf("total crystals <= X: %llu\n", (unsigned long long)(nF3 + nF4 + nF1 + cnt));
  printf("S fingerprint (sum of n mod 2^64): %llu\n", (unsigned long long)sumlo);
  printf("F4 members checked against F1: %llu\n", (unsigned long long)f4checked);
  printf("collisions: %lld\n", collisions);
  printf("seconds: %.2f (threads %d)\n", secs, threads);
  free(A);
  return collisions ? 1 : 0;
}
