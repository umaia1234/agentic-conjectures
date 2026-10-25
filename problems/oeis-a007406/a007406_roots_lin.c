/*
 * OEIS A007406 -- Boyd-tree root scan, implementation R2 (independent of R1).
 *
 * For every prime 5 <= q <= QMAX (q >= QMIN) this computes
 *     T_m = sum_{k=1}^{m} k^{-2}  (mod q^2),   1 <= m <= q-1,
 * using the linear-time inverse table inv[k] = -(M/k) * inv[M mod k] (mod M),
 * M = q^2 (valid because 1 <= M mod k < q for 2 <= k < q), and plain
 * 128-bit remainders.  It reports every root m with T_m = 0 (mod q^2),
 * i.e. v_q(H^(2)_m) >= 2.  The output format matches a007406_roots_mont.c
 * except that v is reported as 2 (meaning ">= 2").
 *
 * Build:  cc -O3 -std=c11 -pthread a007406_roots_lin.c -o roots_lin
 * Usage:  ./roots_lin QMIN QMAX THREADS
 */
#include <inttypes.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>

typedef uint64_t u64;
typedef unsigned __int128 u128;

typedef struct {
    u64 q, m;
} hit_t;

typedef struct {
    u64 qmax;
    hit_t *hits;
    size_t nhits, cap;
    u64 nq, sumq, roots_v1, nfail_last;
} targ_t;

static u64 *primes;
static size_t nprimes;
static atomic_size_t next_index;

static void add_hit(targ_t *ta, u64 q, u64 m) {
    if (ta->nhits == ta->cap) {
        ta->cap = ta->cap ? 2 * ta->cap : 64;
        ta->hits = realloc(ta->hits, ta->cap * sizeof(hit_t));
        if (!ta->hits) { perror("realloc"); exit(2); }
    }
    ta->hits[ta->nhits++] = (hit_t){q, m};
}

static void scan_prime(u64 q, u64 *inv, targ_t *ta) {
    u64 M = q * q;
    u64 T = 1 % M; /* k = 1 */
    inv[1] = 1;
    if (q - 1 == 1) { /* not reached for q >= 5 */ }
    if (T % q == 0) { ta->roots_v1++; if (T == 0) add_hit(ta, q, 1); }
    for (u64 k = 2; k < q; k++) {
        u64 r = M % k, d = M / k;
        u64 x = (u64)((u128)d * inv[r] % M);
        inv[k] = x ? M - x : 0;
        u64 sq = (u64)((u128)inv[k] * inv[k] % M);
        T += sq;
        if (T >= M) T -= M;
        if (T % q == 0) {
            if (k < q - 1) ta->roots_v1++;
            if (T == 0) add_hit(ta, q, k);
        } else if (k == q - 1) {
            ta->nfail_last++;
        }
    }
    ta->nq++;
    ta->sumq += q;
}

static void *worker(void *arg) {
    targ_t *ta = arg;
    u64 *inv = malloc((ta->qmax + 1) * sizeof(u64));
    if (!inv) { perror("malloc"); exit(2); }
    for (;;) {
        size_t i = atomic_fetch_add(&next_index, 1);
        if (i >= nprimes) break;
        scan_prime(primes[nprimes - 1 - i], inv, ta);
    }
    free(inv);
    return NULL;
}

static int cmp_hit(const void *a, const void *b) {
    const hit_t *x = a, *y = b;
    if (x->q != y->q) return x->q < y->q ? -1 : 1;
    if (x->m != y->m) return x->m < y->m ? -1 : 1;
    return 0;
}

int main(int argc, char **argv) {
    if (argc != 4) {
        fprintf(stderr, "usage: %s QMIN QMAX THREADS\n", argv[0]);
        return 2;
    }
    u64 qmin = strtoull(argv[1], 0, 10), qmax = strtoull(argv[2], 0, 10);
    int nth = atoi(argv[3]);
    if (qmax >= 4000000000ULL || nth < 1) {
        fprintf(stderr, "need QMAX < 4e9 and THREADS >= 1\n");
        return 2;
    }
    if (qmin < 5) qmin = 5;
    char *comp = calloc(qmax + 1, 1);
    primes = malloc((qmax + 1) * sizeof(u64));
    for (u64 i = 2; i <= qmax; i++) {
        if (comp[i]) continue;
        if (i >= qmin) primes[nprimes++] = i;
        for (u64 j = i * i; j <= qmax; j += i) comp[j] = 1;
    }
    free(comp);
    pthread_t *th = malloc(nth * sizeof(pthread_t));
    targ_t *ta = calloc(nth, sizeof(targ_t));
    for (int t = 0; t < nth; t++) {
        ta[t].qmax = qmax;
        pthread_create(&th[t], NULL, worker, &ta[t]);
    }
    targ_t tot = {0};
    for (int t = 0; t < nth; t++) {
        pthread_join(th[t], NULL);
        for (size_t h = 0; h < ta[t].nhits; h++) add_hit(&tot, ta[t].hits[h].q, ta[t].hits[h].m);
        tot.nq += ta[t].nq;
        tot.sumq += ta[t].sumq;
        tot.roots_v1 += ta[t].roots_v1;
        tot.nfail_last += ta[t].nfail_last;
    }
    qsort(tot.hits, tot.nhits, sizeof(hit_t), cmp_hit);
    for (size_t h = 0; h < tot.nhits; h++)
        printf("hit %" PRIu64 " %" PRIu64 " 2\n", tot.hits[h].q, tot.hits[h].m);
    printf("summary impl=R2-linear-inverse-table qmin=%" PRIu64 " qmax=%" PRIu64
           " primes=%" PRIu64 " sum_q=%" PRIu64 " roots_v>=1(m<q-1)=%" PRIu64
           " roots_v>=2=%zu wolstenholme_congruence_failures=%" PRIu64 "\n",
           qmin, qmax, tot.nq, tot.sumq, tot.roots_v1, tot.nhits, tot.nfail_last);
    return tot.nfail_last == 0 ? 0 : 1;
}
