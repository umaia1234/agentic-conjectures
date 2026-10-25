/*
 * crim_check.c - independent C check of CRIM P/N positions, conj:main and
 * conj:bloby for hook stacks (CRIM; Basic, Gottlieb, Krnc, arXiv:2606.16828).
 *
 * Definitions.  A position is a partition l (weakly decreasing positive
 * parts; len(l) rows, largest part l1, l1 = 0 for []).  A move deletes one row
 * (one part) or one column j, 1 <= j <= l1 (every part >= j drops by 1, zero
 * parts vanish).  Normal play: [] is P; l is P iff no move reaches a P.
 *   rank(l) = |len(l) - l1|;  conj:main: every P-position has even rank.
 *   Hook G(r,c) = [c, 1^(r-1)].  Hook stack H(r,c,m) = [c, 1+m_1, ...,
 *   1+m_k, 1^(r-1-k)], defined iff k = len(m) <= r-1 and m_1 <= c-1.
 *   conj:bloby (hooks): if m and G(r,c) are P and H(r,c,m) is defined, then
 *   H(r,c,m) is P.
 *
 * Method (independent of crim_check.py).  The partitions of n are generated
 * in lexicographic order and a partition is identified with its index in
 * that order, its rank, computed from cnt[s][k] = #partitions of s with all
 * parts <= k.  P/N is one bit per (n, rank).  One move per distinct result is
 * tried: deleting any row of length v gives the same position, and deleting
 * column j gives the same position for all j with l_{t+1} < j <= l_t.
 * Every nonempty X equals H(r,c,m) for exactly one (r,c,m): r = len(X),
 * c = X_1, m = (X_2-1, X_3-1, ...) without zero parts.  So conj:bloby up to
 * N is checked by testing, for every X with |X| <= N, that G(r,c) P and m P
 * imply X P; the pairs counted are exactly those with |H(r,c,m)| <= N.
 *
 * Usage:  cc -O2 -std=c99 -o crim_check crim_check.c && ./crim_check N
 * Prints one line per n (partitions, P-positions, bloby pairs with
 * |H(r,c,m)| = n) and a summary line; exits 1 on any failure.
 */

#include <stdio.h>
#include <stdlib.h>

#define MAXN 120

typedef unsigned long long u64;

static u64 cnt[MAXN + 1][MAXN + 1];   /* cnt[s][k]: partitions of s, parts <= k */
static u64 below[MAXN + 1][MAXN + 2]; /* below[s][a]: partitions of s, first part < a */
static unsigned char *pbit[MAXN + 1]; /* bit q of pbit[s]: partition of s with rank q is P */
static unsigned char hookp[MAXN + 2][MAXN + 2]; /* hookp[r][c] = 1 iff G(r,c) is P */

static int cur_n;                     /* size of the partitions being generated */
static int part[MAXN + 1];            /* current partition part[0] >= part[1] >= ... */
static int rem[MAXN + 1];             /* rem[i] = part[i] + part[i+1] + ... */
static u64 pre[MAXN + 2];             /* pre[i] = sum_{j<i} below[rem[j]][part[j]] */
static u64 next_index;                /* lexicographic index of the next partition */

static u64 n_parts[MAXN + 1], n_p[MAXN + 1], n_bloby[MAXN + 1];
static u64 failures;

static int is_p(int s, u64 q) { return (pbit[s][q >> 3] >> (q & 7)) & 1; }

static void fail(const char *what, int len)
{
    if (failures++ < 20) {
        printf("FAIL: %s: [", what);
        for (int i = 0; i < len; i++)
            printf(i ? ",%d" : "%d", part[i]);
        printf("]\n");
    }
}

/* Decide P/N for the current partition part[0..len-1] and run the checks. */
static void visit(int len)
{
    int n = cur_n;
    u64 q = pre[len];
    int p = 1;

    if (q != next_index)
        fail("rank differs from enumeration index", len);
    next_index++;
    n_parts[n]++;

    /* t runs over the last row of each run of equal row lengths. */
    for (int t = 0; t < len && p; t++) {
        if (t + 1 < len && part[t + 1] == part[t])
            continue;
        int v = part[t];
        u64 tail = pre[len] - pre[t + 1]; /* rows after t are unchanged */
        u64 child = tail;
        /* Delete row t (length v): earlier rows keep their length, rem drops by v. */
        for (int i = 0; i < t; i++)
            child += below[rem[i] - v][part[i]];
        if (is_p(n - v, child)) {
            p = 0;
            break;
        }
        /* Delete column v: rows 0..t lose one cell each (zero rows add 0). */
        child = tail;
        for (int i = 0; i <= t; i++)
            child += below[rem[i] - (t + 1 - i)][part[i] - 1];
        if (is_p(n - (t + 1), child)) {
            p = 0;
            break;
        }
    }

    if (p) {
        pbit[n][q >> 3] |= (unsigned char)(1u << (q & 7));
        n_p[n]++;
        int l1 = len ? part[0] : 0;
        int rk = len > l1 ? len - l1 : l1 - len;
        if (rk % 2)
            fail("conj:main fails, P-position of odd rank", len);
    }
    if (len == 0)
        return;

    /* X = H(r,c,m) with r = len, c = part[0], m = (part[1]-1, ..., part[k]-1). */
    int r = len, c = part[0], k = 0;
    while (k + 1 < len && part[k + 1] >= 2)
        k++;
    if (k == 0)
        hookp[r][c] = (unsigned char)p; /* X is the hook G(r,c) itself */
    int s = n - c - (r - 1);            /* |m| */
    u64 mq = 0;
    for (int i = 1, left = s; i <= k; i++) {
        mq += below[left][part[i] - 1];
        left -= part[i] - 1;
    }
    if (hookp[r][c] && is_p(s, mq)) {
        n_bloby[n]++;
        if (!p)
            fail("conj:bloby fails, G(r,c) and m are P but H(r,c,m) is N", len);
    }
}

/* Generate partitions of cur_n in lexicographic order, parts <= maxpart. */
static void gen(int depth, int left, int maxpart)
{
    if (left == 0) {
        visit(depth);
        return;
    }
    int top = left < maxpart ? left : maxpart;
    rem[depth] = left;
    for (int a = 1; a <= top; a++) {
        part[depth] = a;
        pre[depth + 1] = pre[depth] + below[left][a];
        gen(depth + 1, left - a, a);
    }
}

int main(int argc, char **argv)
{
    if (argc != 2) {
        fprintf(stderr, "usage: %s N   (0 <= N <= %d)\n", argv[0], MAXN);
        return 2;
    }
    int N = atoi(argv[1]);
    if (N < 0 || N > MAXN) {
        fprintf(stderr, "N must be in 0..%d\n", MAXN);
        return 2;
    }

    for (int k = 0; k <= MAXN; k++)
        cnt[0][k] = 1;
    for (int s = 1; s <= MAXN; s++)
        for (int k = 1; k <= MAXN; k++)
            cnt[s][k] = cnt[s][k - 1] + (k <= s ? cnt[s - k][k] : 0);
    for (int s = 0; s <= MAXN; s++)
        for (int a = 2; a <= MAXN + 1; a++)
            below[s][a] = below[s][a - 1] + (a - 1 <= s ? cnt[s - (a - 1)][a - 1] : 0);

    u64 tot_parts = 0, tot_p = 0, tot_bloby = 0;
    for (int n = 0; n <= N; n++) {
        pbit[n] = calloc(cnt[n][n] / 8 + 1, 1);
        if (!pbit[n]) {
            fprintf(stderr, "out of memory at n=%d\n", n);
            return 2;
        }
        cur_n = n;
        next_index = 0;
        pre[0] = 0;
        gen(0, n, n);
        if (n_parts[n] != cnt[n][n]) {
            failures++;
            printf("FAIL: generated %llu partitions of %d, table gives %llu\n",
                   n_parts[n], n, cnt[n][n]);
        }
        printf("n=%d partitions=%llu P=%llu bloby_pairs=%llu\n", n, n_parts[n], n_p[n],
               n_bloby[n]);
        fflush(stdout);
        tot_parts += n_parts[n];
        tot_p += n_p[n];
        tot_bloby += n_bloby[n];
    }
    printf("summary: %s N=%d partitions=%llu P=%llu bloby_pairs=%llu failures=%llu\n",
           failures ? "FAIL" : "OK", N, tot_parts, tot_p, tot_bloby, failures);
    return failures ? 1 : 0;
}
