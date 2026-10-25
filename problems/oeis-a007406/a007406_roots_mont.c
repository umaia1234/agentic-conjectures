/*
 * OEIS A007406 -- Boyd-tree root scan, implementation R1.
 *
 * For every prime 5 <= q <= QMAX (q >= QMIN) this computes the prefix sums
 *     S_m = sum_{k=1}^{m} k^{-2}  (mod q^3),   1 <= m <= q-1,
 * i.e. H^(2)_m mod q^3 (these H^(2)_m are q-integral), and reports every root
 * m with v_q(S_m) >= 2 (v capped at 3).  Arithmetic: Montgomery
 * multiplication modulo M = q^3 < 2^64 and Montgomery's batch-inversion
 * trick (one extended-Euclid inversion per prime).  Requires QMAX < 2642246.
 *
 * It also checks the classical congruence S_{q-1} = 0 (mod q) for each q
 * and counts the roots m <= q-2 with v_q(S_m) >= 1.
 *
 * Output: lines "hit q m v" (sorted), then a "summary" line.
 * Build:  cc -O3 -std=c11 -pthread a007406_roots_mont.c -o roots_mont
 * Usage:  ./roots_mont QMIN QMAX THREADS
 *
 * The independent implementation R2 is a007406_roots_lin.c.
 */
#include <inttypes.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t u64;
typedef unsigned __int128 u128;

typedef struct {
    u64 q, m;
    int v;
} hit_t;

static u64 *primes;
static size_t nprimes;
static atomic_size_t next_index;

typedef struct {
    hit_t *hits;
    size_t nhits, caphits;
    u64 sumq, nq, roots_v1, last_fail;
    u64 nfail_last;
} result_t;

/* REDC for odd M < 2^64 and T < M * 2^64; returns T * 2^-64 mod M. */
static inline u64 redc(u128 T, u64 M, u64 mneg) {
    u64 m = (u64)T * mneg;
    u128 mM = (u128)m * M;
    u64 lo = (u64)T + (u64)mM; /* = 0 by construction */
    u64 carry = lo < (u64)T;
    u128 t = (T >> 64) + (mM >> 64) + carry; /* < 2M */
    if (t >= M) t -= M;
    return (u64)t;
}

static inline u64 mmul(u64 a, u64 b, u64 M, u64 mneg) {
    return redc((u128)a * b, M, mneg);
}

static inline u64 addmod(u64 a, u64 b, u64 M) {
    u64 s = a + b;
    if (s < a || s >= M) s -= M;
    return s;
}

static inline u64 submod(u64 a, u64 b, u64 M) {
    return a >= b ? a - b : a + (M - b);
}

static u64 inv_mod(u64 a, u64 m) {
    __int128 t = 0, nt = 1, r = m, nr = a;
    while (nr != 0) {
        __int128 qq = r / nr, tmp;
        tmp = t - qq * nt; t = nt; nt = tmp;
        tmp = r - qq * nr; r = nr; nr = tmp;
    }
    if (r != 1) {
        fprintf(stderr, "inv_mod: not invertible\n");
        exit(2);
    }
    if (t < 0) t += m;
    return (u64)t;
}

/* d odd: x divisible by d iff x * d^{-1} (mod 2^64) <= (2^64-1)/d. */
static inline int divisible(u64 x, u64 dinv, u64 dlim) { return x * dinv <= dlim; }

static u64 inv64(u64 d) { /* d^{-1} mod 2^64, d odd */
    u64 x = d;
    for (int i = 0; i < 6; i++) x *= 2 - d * x;
    return x;
}

static void push_hit(result_t *res, u64 q, u64 m, int v) {
    if (res->nhits == res->caphits) {
        res->caphits = res->caphits ? 2 * res->caphits : 64;
        res->hits = realloc(res->hits, res->caphits * sizeof(hit_t));
        if (!res->hits) { perror("realloc"); exit(2); }
    }
    res->hits[res->nhits++] = (hit_t){q, m, v};
}

static void scan_prime(u64 q, u64 *buf, result_t *res) {
    u64 q2 = q * q, M = q2 * q;
    u64 mneg = (u64)0 - inv64(M);
    u64 R1 = (u64)(((u128)1 << 64) % M);
    u64 R2 = (u64)((u128)R1 * R1 % M);
    u64 qinv = inv64(q), qlim = UINT64_MAX / q;
    u64 q2inv = inv64(q2), q2lim = UINT64_MAX / q2;

    /* prefix products P[k] = k! in Montgomery form, buf[k] */
    u64 kt = 0; /* k in Montgomery form */
    buf[0] = R1;
    for (u64 k = 1; k < q; k++) {
        kt = addmod(kt, R1, M);
        buf[k] = mmul(buf[k - 1], kt, M, mneg);
    }
    /* invert (q-1)! */
    u64 Pn = redc((u128)buf[q - 1], M, mneg);
    u64 invP = mmul(inv_mod(Pn, M), R2, M, mneg); /* Montgomery form of ((k)!)^{-1}, k=q-1 */
    /* walk down: inv(k) = (k-1)! * (k!)^{-1}; store inv(k)^2 in buf[k] */
    for (u64 k = q - 1; k >= 1; k--) {
        u64 ik = mmul(buf[k - 1], invP, M, mneg);
        invP = mmul(invP, kt, M, mneg);
        kt = submod(kt, R1, M);
        buf[k] = mmul(ik, ik, M, mneg);
    }
    /* prefix sums */
    u64 S = 0;
    for (u64 m = 1; m < q; m++) {
        S = addmod(S, buf[m], M);
        if (divisible(S, qinv, qlim)) {
            if (m < q - 1) res->roots_v1++;
            if (divisible(S, q2inv, q2lim)) push_hit(res, q, m, S == 0 ? 3 : 2);
        } else if (m == q - 1) {
            res->nfail_last++;
            res->last_fail = q;
        }
    }
    res->sumq += q;
    res->nq++;
}

typedef struct {
    u64 qmax;
    result_t res;
} targ_t;

static void *worker(void *arg) {
    targ_t *ta = arg;
    u64 *buf = malloc((ta->qmax + 1) * sizeof(u64));
    if (!buf) { perror("malloc"); exit(2); }
    for (;;) {
        size_t i = atomic_fetch_add(&next_index, 1);
        if (i >= nprimes) break;
        scan_prime(primes[nprimes - 1 - i], buf, &ta->res); /* largest first */
    }
    free(buf);
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
    if (qmax >= 2642246 || nth < 1) {
        fprintf(stderr, "need QMAX < 2642246 (q^3 < 2^64) and THREADS >= 1\n");
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
    result_t tot = {0};
    for (int t = 0; t < nth; t++) {
        pthread_join(th[t], NULL);
        for (size_t h = 0; h < ta[t].res.nhits; h++) {
            hit_t *x = &ta[t].res.hits[h];
            push_hit(&tot, x->q, x->m, x->v);
        }
        tot.sumq += ta[t].res.sumq;
        tot.nq += ta[t].res.nq;
        tot.roots_v1 += ta[t].res.roots_v1;
        tot.nfail_last += ta[t].res.nfail_last;
    }
    qsort(tot.hits, tot.nhits, sizeof(hit_t), cmp_hit);
    size_t v3 = 0;
    for (size_t h = 0; h < tot.nhits; h++) {
        printf("hit %" PRIu64 " %" PRIu64 " %d\n", tot.hits[h].q, tot.hits[h].m, tot.hits[h].v);
        if (tot.hits[h].v >= 3) v3++;
    }
    printf("summary impl=R1-montgomery-batch qmin=%" PRIu64 " qmax=%" PRIu64 " primes=%" PRIu64
           " sum_q=%" PRIu64 " roots_v>=1(m<q-1)=%" PRIu64 " roots_v>=2=%zu roots_v>=3=%zu"
           " wolstenholme_congruence_failures=%" PRIu64 "\n",
           qmin, qmax, tot.nq, tot.sumq, tot.roots_v1, tot.nhits, v3, tot.nfail_last);
    return (v3 == 0 && tot.nfail_last == 0) ? 0 : 1;
}
