// colton_sieve.cpp -- pointwise check of Colton's conjecture pi(n) <= 2 T(n) for all n <= N.
//
// T(n) = #{1 <= k <= n : tau(k) | k} (refactorable / tau numbers), pi(n) = #{primes <= n}.
//
// Method (segmented sieve, independent of the structured counter tau_count.cpp):
//   * primes: odd-only Eratosthenes sieve per segment;
//   * tau numbers k = 0 (mod 4): tau(k) from a segmented factor sieve over k = 4m
//     (2-adic part from ctz, odd primes p <= sqrt(k) by sieving, one leftover prime > sqrt(k));
//   * tau numbers k odd or k = 2 (mod 4): k odd is refactorable only if k is a square
//     (tau(k) odd forces every exponent even), and k = 2u (u odd) is refactorable iff u is;
//     so these are 1, 2 and s^2, 2 s^2 for odd s with tau(s^2) | s^2, listed up front.
//   * every n is covered: for a segment [L, R) with offsets T0 = T(L-1), P0 = pi(L-1) we keep
//     the exact minimum of 2 T_loc(p) - pi_loc(p) over the primes p of the segment and check
//     2 T0 - P0 + min >= 0. This covers every n: between consecutive primes T can only grow
//     while pi stays constant, and for n < 2 both sides vanish or 2T(1) = 2 > 0 = pi(1).
//
// Usage: colton_sieve N [threads] [checkpoint_file] [from]
//   Prints T and pi at powers of ten and at the checkpoints, the global minimum of
//   2T(n) - pi(n) over primes, tail minima from each power of ten on, and the verdict.
//   With `from`, only the interval [L, N] is sieved, where L = from rounded down to a multiple of
//   the segment size, and the program prints T(n) - T(L-1) and pi(n) - pi(L-1) at the
//   checkpoints in [L, N] (used to spot-check tau_count far beyond the full run).
#include <algorithm>
#include <atomic>
#include <cinttypes>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <thread>
#include <vector>

typedef uint64_t u64;
typedef int64_t i64;

static u64 isqrt_u64(u64 n) {
    u64 r = (u64)sqrtl((long double)n);
    while (r * r > n) r--;
    while ((r + 1) * (r + 1) <= n) r++;
    return r;
}

static const u64 SEG = 1ULL << 21;  // numbers per segment (multiple of 64)

struct SegResult {
    i64 tl = 0, pl = 0;       // tau numbers / primes in the segment
    i64 minloc = INT64_MAX;   // min over primes p in the segment of 2 T_loc(p) - pi_loc(p)
    u64 argmin = 0;           // first prime attaining minloc
};

struct Ckpt {
    u64 n;
    i64 tl = 0, pl = 0;  // local counts at n within its segment
};

int main(int argc, char** argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: %s N [threads] [checkpoint_file] [from]\n", argv[0]);
        return 2;
    }
    const u64 N = strtoull(argv[1], nullptr, 10);
    const int threads = argc > 2 ? atoi(argv[2]) : 1;
    const u64 kstart = argc > 4 ? strtoull(argv[4], nullptr, 10) / SEG : 0;
    const u64 Ls = kstart * SEG;
    std::vector<Ckpt> ck;
    for (u64 p = 1; p <= N; p *= 10) {
        ck.push_back({p});
        if (p > N / 10) break;
    }
    ck.push_back({N});
    if (argc > 3) {
        FILE* f = fopen(argv[3], "r");
        if (!f) { perror("checkpoint file"); return 2; }
        unsigned long long v;
        while (fscanf(f, "%llu", &v) == 1)
            if (v >= 1 && v <= N) ck.push_back({(u64)v});
        fclose(f);
    }
    std::sort(ck.begin(), ck.end(), [](const Ckpt& a, const Ckpt& b) { return a.n < b.n; });
    ck.erase(std::unique(ck.begin(), ck.end(), [](const Ckpt& a, const Ckpt& b) { return a.n == b.n; }),
             ck.end());
    ck.erase(std::remove_if(ck.begin(), ck.end(), [&](const Ckpt& c) { return c.n < Ls; }), ck.end());

    // Base primes up to sqrt(N).
    const u64 r = isqrt_u64(N);
    std::vector<uint32_t> primes;
    {
        std::vector<char> comp(r + 2, 0);
        for (u64 i = 2; i <= r; i++)
            if (!comp[i]) {
                primes.push_back((uint32_t)i);
                for (u64 j = i * i; j <= r; j += i) comp[j] = 1;
            }
    }

    // Refactorable numbers that are odd or = 2 mod 4: 1, 2, s^2, 2 s^2 with s odd, tau(s^2) | s^2.
    std::vector<u64> special;
    {
        std::vector<uint32_t> spf(r + 2, 0);
        for (u64 i = 2; i <= r; i++)
            if (!spf[i])
                for (u64 j = i; j <= r; j += i)
                    if (!spf[j]) spf[j] = (uint32_t)i;
        for (u64 s = 1; s <= r; s += 2) {
            u64 t = 1, m = s;
            while (m > 1) {
                u64 p = spf[m];
                int e = 0;
                while (m % p == 0) { m /= p; e++; }
                t *= (u64)(2 * e + 1);
            }
            u64 sq = s * s;
            if (sq <= N && sq % t == 0) {
                special.push_back(sq);
                if (sq <= N / 2) special.push_back(2 * sq);
            }
        }
        std::sort(special.begin(), special.end());
    }

    const u64 nseg = N / SEG + 1;  // segments [k*SEG, (k+1)*SEG) intersected with [0, N]
    if (kstart >= nseg) { fprintf(stderr, "from > N\n"); return 2; }
    std::vector<SegResult> res(nseg - kstart);  // res[k - kstart] for segments k >= kstart
    std::atomic<u64> next{0};

    auto worker = [&]() {
        std::vector<uint32_t> tau(SEG / 4);
        std::vector<u64> prod(SEG / 4);
        std::vector<uint8_t> oddcomp(SEG / 2);
        std::vector<u64> pbits(SEG / 64), tbits(SEG / 64);
        for (;;) {
            u64 k = kstart + next.fetch_add(1);
            if (k >= nseg) break;
            const u64 L = k * SEG;
            const u64 R = std::min(L + SEG, N + 1);  // segment is [L, R)
            const u64 len = R - L;
            std::fill(pbits.begin(), pbits.end(), 0);
            std::fill(tbits.begin(), tbits.end(), 0);

            // ---- primes in [L, R): odd-only sieve; index i <-> n = L + 2i + 1 (L even).
            const u64 nodd = len / 2;  // odd n in [L, R) (L even): L+1, L+3, ..., count len/2
            std::memset(oddcomp.data(), 0, nodd);
            for (size_t i = 1; i < primes.size(); i++) {
                const u64 p = primes[i];
                if (p * p >= R) break;
                u64 st = std::max(p * p, (L + p - 1) / p * p);
                if (!(st & 1)) st += p;
                for (u64 n = st; n < R; n += 2 * p) oddcomp[(n - L - 1) >> 1] = 1;
            }
            for (u64 i = 0; i < nodd; i++) {
                const u64 n = L + 2 * i + 1;
                if (n >= 3 && !oddcomp[i]) pbits[(n - L) >> 6] |= 1ULL << ((n - L) & 63);
            }
            if (L <= 2 && 2 < R) pbits[(2 - L) >> 6] |= 1ULL << ((2 - L) & 63);

            // ---- tau numbers n = 4m in [L, R).
            const u64 m0 = std::max<u64>(1, (L + 3) / 4), m1 = (R + 3) / 4;  // m in [m0, m1)
            if (m1 > m0) {
                const u64 cnt = m1 - m0;
                for (u64 j = 0; j < cnt; j++) {
                    const u64 m = m0 + j;
                    const int e = 2 + __builtin_ctzll(m);
                    tau[j] = (uint32_t)(e + 1);
                    prod[j] = 1ULL << e;
                }
                const u64 nmax = 4 * (m1 - 1);
                for (size_t i = 1; i < primes.size(); i++) {
                    const u64 p = primes[i];
                    if (p * p > nmax) break;
                    u64 pk = p;  // runs over p^k dividing m (n = 4m, p odd)
                    for (uint32_t kk = 1;; kk++) {
                        for (u64 m = (m0 + pk - 1) / pk * pk; m < m1; m += pk) {
                            const u64 j = m - m0;
                            tau[j] = tau[j] / kk * (kk + 1);
                            prod[j] *= p;
                        }
                        if (pk > (m1 - 1) / p) break;
                        pk *= p;
                    }
                }
                for (u64 j = 0; j < cnt; j++) {
                    const u64 n = 4 * (m0 + j);
                    u64 t = tau[j];
                    if (prod[j] != n) t *= 2;  // one prime factor > sqrt(n) remains
                    const int v2n = __builtin_ctzll(n), v2t = __builtin_ctzll(t);
                    if (v2t <= v2n && n % (t >> v2t) == 0) tbits[(n - L) >> 6] |= 1ULL << ((n - L) & 63);
                }
            }
            // ---- odd / 2 mod 4 tau numbers.
            for (auto it = std::lower_bound(special.begin(), special.end(), L);
                 it != special.end() && *it < R; ++it)
                tbits[(*it - L) >> 6] |= 1ULL << ((*it - L) & 63);
            if (L == 0) tbits[0] &= ~1ULL;  // n = 0 is not counted

            // ---- scan: exact minimum of 2 T_loc - pi_loc (only primes can lower it).
            SegResult sr;
            i64 tl = 0, pl = 0;
            const u64 nw = (len + 63) / 64;
            for (u64 w = 0; w < nw; w++) {
                u64 pw = pbits[w], tw = tbits[w];
                while (pw) {
                    const int b = __builtin_ctzll(pw);
                    const u64 mask = (b == 63) ? ~0ULL : ((2ULL << b) - 1);  // bits 0..b
                    const i64 tcount = tl + __builtin_popcountll(tw & mask);
                    const i64 pcount = pl + __builtin_popcountll(pbits[w] & mask);
                    const i64 v = 2 * tcount - pcount;
                    if (v < sr.minloc) { sr.minloc = v; sr.argmin = L + 64 * w + b; }
                    pw &= pw - 1;
                }
                tl += __builtin_popcountll(tw);
                pl += __builtin_popcountll(pbits[w]);
            }
            sr.tl = tl;
            sr.pl = pl;
            res[k - kstart] = sr;
            // checkpoints in this segment
            for (auto it = std::lower_bound(ck.begin(), ck.end(), L, [](const Ckpt& c, u64 v) { return c.n < v; });
                 it != ck.end() && it->n < R; ++it) {
                const u64 off = it->n - L;  // count bits 0..off
                i64 a = 0, b = 0;
                for (u64 w = 0; w < off / 64; w++) {
                    a += __builtin_popcountll(tbits[w]);
                    b += __builtin_popcountll(pbits[w]);
                }
                const int bb = off % 64;
                const u64 mask = (bb == 63) ? ~0ULL : ((2ULL << bb) - 1);
                a += __builtin_popcountll(tbits[off / 64] & mask);
                b += __builtin_popcountll(pbits[off / 64] & mask);
                it->tl = a;
                it->pl = b;
            }
        }
    };
    std::vector<std::thread> pool;
    for (int t = 0; t < threads; t++) pool.emplace_back(worker);
    for (auto& t : pool) t.join();

    // ---- combine.
    i64 T0 = 0, P0 = 0;
    bool ok = true;
    i64 gmin = INT64_MAX;
    u64 gargmin = 0;
    if (kstart > 0) {  // interval mode: counts relative to L - 1
        std::vector<i64> segT0(nseg - kstart), segP0(nseg - kstart);
        for (u64 k = kstart; k < nseg; k++) {
            segT0[k - kstart] = T0;
            segP0[k - kstart] = P0;
            T0 += res[k - kstart].tl;
            P0 += res[k - kstart].pl;
        }
        for (auto& c : ck) {
            const u64 k = c.n / SEG - kstart;
            printf("DCKPT from=%" PRIu64 " n=%" PRIu64 " dT=%" PRId64 " dpi=%" PRId64 "\n", Ls, c.n,
                   segT0[k] + c.tl, segP0[k] + c.pl);
        }
        printf("INTERVAL [%" PRIu64 ", %" PRIu64 "]: dT=%" PRId64 " dpi=%" PRId64 "\n", Ls, N, T0, P0);
        return 0;
    }
    std::vector<i64> segT0(nseg), segP0(nseg);
    for (u64 k = 0; k < nseg; k++) {
        segT0[k] = T0;
        segP0[k] = P0;
        if (res[k].minloc != INT64_MAX) {
            const i64 v = 2 * T0 - P0 + res[k].minloc;  // = min over primes p in segment of 2T(p)-pi(p)
            if (v < 0) {
                ok = false;
                printf("VIOLATION in segment %" PRIu64 ": 2T-pi = %" PRId64 " at n=%" PRIu64 "\n", k, v,
                       res[k].argmin);
            }
            if (v < gmin) { gmin = v; gargmin = res[k].argmin; }
        }
        T0 += res[k].tl;
        P0 += res[k].pl;
    }
    printf("N = %" PRIu64 "  T(N) = %" PRId64 "  pi(N) = %" PRId64 "\n", N, T0, P0);
    for (auto& c : ck) {
        const u64 k = c.n / SEG;
        printf("CKPT n=%" PRIu64 " T=%" PRId64 " pi=%" PRId64 "\n", c.n, segT0[k] + c.tl, segP0[k] + c.pl);
    }
    // Tail statistics over the segments that start at or after 10^j (segment starts are multiples
    // of SEG): the exact minimum of 2T(p) - pi(p) over their primes, and the lower bound
    // 2T(p)/pi(p) >= 2 T(L-1) / pi(R-1) for p in a segment [L, R).
    u64 prevk0 = UINT64_MAX;
    for (u64 lo = 1; lo <= N; lo *= 10) {
        const u64 k0 = (lo + SEG - 1) / SEG;
        if (k0 == prevk0) continue;
        prevk0 = k0;
        i64 dmin = INT64_MAX;
        u64 darg = 0;
        double rlb = 1e300;
        for (u64 k = k0; k < nseg; k++) {
            if (res[k].minloc != INT64_MAX && 2 * segT0[k] - segP0[k] + res[k].minloc < dmin) {
                dmin = 2 * segT0[k] - segP0[k] + res[k].minloc;
                darg = res[k].argmin;
            }
            if (segP0[k] + res[k].pl > 0) rlb = std::min(rlb, 2.0 * segT0[k] / (double)(segP0[k] + res[k].pl));
        }
        if (dmin != INT64_MAX)
            printf("TAIL from %" PRIu64 ": min 2T(p)-pi(p) = %" PRId64 " at p=%" PRIu64
                   "; min 2T(p)/pi(p) >= %.6f\n", k0 * SEG, dmin, darg, rlb);
        if (lo > N / 10) break;
    }
    printf("GLOBAL min of 2T(p)-pi(p) over primes p<=N: %" PRId64 " (first at p=%" PRIu64 ")\n", gmin, gargmin);
    printf("RESULT: %s pi(n) <= 2T(n) for all n <= %" PRIu64 "\n", ok ? "VERIFIED" : "FAILED", N);
    return ok ? 0 : 1;
}
