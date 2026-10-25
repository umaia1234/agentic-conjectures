// tau_count.cpp -- exact T(x) = #{1 <= n <= x : tau(n) | n} by a structured count, together with
// pi(x) from the Lucy_Hedgehog table that the count uses. Independent of colton_sieve.cpp.
//
// Decomposition by the 2-adic valuation of n:
//   * n odd:      tau(n) | n forces tau(n) odd, so n = s^2 (s odd); count odd s <= sqrt(x) with
//                 tau(s^2) | s^2 directly (factor sieve up to sqrt(x)).
//   * n = 2u, u odd: tau(n) = 2 tau(u), so n is refactorable iff u is; count = T_odd(x/2).
//   * n = 0 mod 4: depth-first search over the factorisation n = 2^a p1^e1 ... pk^ek (a >= 2,
//                 p1 < ... < pk), in two layers:
//       - explicit layer: prefixes d whose odd primes are <= 61 (all primes that can divide a
//         divisor count tau(n) for n < 2^64, because every exponent is <= 63);
//       - generic layer: the part m of n built from primes > 61. Such primes never divide tau(n),
//         so for n = d*m we have tau(n) | n  <=>  tau(d) | d and tau(m) | d / tau(d).
//         gen(A, y, P) counts m in (1, y] with all prime factors > P and tau(m) | A, aggregating
//         the largest prime factor through pi.
//     At an explicit node d (largest prime P <= 61) the extensions n = d*m are partitioned as:
//       m = 1 (counted at d when d ends with an exponent >= 2; d ending with exponent 1 is
//       counted by its parent's aggregation), m = q prime in (P, 61] (aggregated), m whose
//       smallest prime p is in (P, 61] and m != p (explicit child d p^e), m with all primes > 61
//       (generic layer).
//     Pruning: with g = gcd(tau(d), d), every prime of tau(d)/g must divide m, so it must exceed P.
//
// pi(v) is needed only for v of the form floor(x/k) or v <= sqrt(x): Lucy_Hedgehog table.
//
// Usage: tau_count x1 [x2 ...]   or   tau_count -f file_with_x_values
//   prints "x=<x> T=<T(x)> pi=<pi(x)> secs=<time>" per value.
#include <algorithm>
#include <chrono>
#include <cinttypes>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <numeric>
#include <vector>

typedef uint64_t u64;
typedef unsigned __int128 u128;

static u64 X, R;                       // current x and isqrt(x)
static std::vector<u64> lo, hi;        // lo[v] = pi(v) (v <= R), hi[k] = pi(x/k) (k <= R)
static std::vector<uint32_t> primes;   // all primes <= max(R, 100)
static const u64 SMALL = 1 << 17;
static std::vector<uint32_t> smallpi;  // pi(v) for v < SMALL
static std::vector<uint8_t> smallisp;
static const u64 SP[18] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61};
static const int IDX61 = 17;           // primes[17] == 61

static u64 isqrt_u64(u64 n) {
    u64 r = (u64)sqrtl((long double)n);
    while (r * r > n) r--;
    while ((r + 1) * (r + 1) <= n) r++;
    return r;
}

static bool pow_gt(u64 b, int e, u64 y) {  // b^e > y
    u128 acc = 1;
    for (int i = 0; i < e; i++) {
        acc *= b;
        if (acc > y) return true;
    }
    return false;
}

static u64 iroot(u64 y, int e) {  // floor(y^(1/e))
    if (e == 1) return y;
    u64 r = (u64)powl((long double)y, 1.0L / e);
    while (r > 0 && pow_gt(r, e, y)) r--;
    while (!pow_gt(r + 1, e, y)) r++;
    return r;
}

static inline u64 pi(u64 v) {  // v < SMALL, or v <= R, or v = floor(X/k)
    if (v < SMALL) return smallpi[v];
    if (v <= R) return lo[v];
    return hi[X / v];
}

static void build_small() {
    smallisp.assign(SMALL, 1);
    smallisp[0] = smallisp[1] = 0;
    for (u64 i = 2; i * i < SMALL; i++)
        if (smallisp[i])
            for (u64 j = i * i; j < SMALL; j += i) smallisp[j] = 0;
    smallpi.assign(SMALL, 0);
    for (u64 i = 1; i < SMALL; i++) smallpi[i] = smallpi[i - 1] + smallisp[i];
}

static void build_lucy(u64 x) {
    X = x;
    R = isqrt_u64(x);
    lo.assign(R + 1, 0);
    hi.assign(R + 2, 0);
    for (u64 v = 1; v <= R; v++) lo[v] = v - 1;
    for (u64 k = 1; k <= R; k++) hi[k] = x / k - 1;
    for (u64 p = 2; p <= R; p++) {
        if (lo[p] == lo[p - 1]) continue;  // p composite
        const u64 sp = lo[p - 1], p2 = p * p;
        const u64 kmax = std::min(R, x / p2), lim1 = std::min(kmax, R / p);
        for (u64 k = 1; k <= lim1; k++) hi[k] -= hi[k * p] - sp;
        for (u64 k = lim1 + 1; k <= kmax; k++) hi[k] -= lo[x / (k * p)] - sp;
        // lo[v] -= lo[v / p] - sp for v = R down to p^2, in blocks of equal quotient q = v / p
        for (u64 q = R / p; q >= p; q--) {
            const u64 val = lo[q] - sp, vlo = q * p, vhi = std::min(q * p + p - 1, R);
            for (u64 v = vlo; v <= vhi; v++) lo[v] -= val;
        }
    }
    primes.clear();
    const u64 top = std::max<u64>(R, 100);
    for (u64 v = 2; v <= top; v++)
        if (v < SMALL ? smallisp[v] : (lo[v] != lo[v - 1])) primes.push_back((uint32_t)v);
}

// # m in (1, y] with every prime factor > P = primes[pidx] (P >= 61) and tau(m) | A.
static u64 gen(u64 A, u64 y, size_t pidx) {
    const u64 P = primes[pidx];
    if (y <= P) return 0;
    u64 c = 0;
    const u64 piP = pi(P);
    if (A % 2 == 0) c += pi(y) - piP;  // m = q
    for (int f = 3;; f++) {            // m = q^(f-1), f | A
        if (pow_gt(P + 1, f - 1, y)) break;
        if (A % f == 0) {
            const u64 rt = iroot(y, f - 1);
            if (rt > P) c += pi(rt) - piP;
        }
    }
    // m = p^e m' with p the smallest prime of m, f = e + 1 | A, m' > 1 (primes > p, tau(m') | A/f)
    for (int f = 2;; f++) {
        if (pow_gt(P + 1, f, y)) break;  // need p^e q^(s-1) <= y with P < p < q, s >= 2
        if (A % f) continue;
        const u64 A2 = A / f;
        int s = 0;
        for (int t = 2; t <= 64; t++)
            if (A2 % t == 0) { s = t; break; }
        if (!s) continue;
        const int e = f - 1;
        const u64 bound = iroot(y - 1, e + s - 1);  // p^(e+s-1) < y
        for (size_t j = pidx + 1; j < primes.size() && primes[j] <= bound; j++) {
            const u64 p = primes[j];
            u64 pe = p;
            for (int i = 1; i < e; i++) pe *= p;
            c += gen(A2, y / pe, j);
        }
    }
    return c;
}

static u64 spf_small(u64 m) {  // smallest prime factor of m > 1 whose primes are all <= 61
    for (int i = 0; i < 18; i++)
        if (m % SP[i] == 0) return SP[i];
    fprintf(stderr, "spf_small: unexpected %" PRIu64 "\n", m);
    exit(3);
}

// Count n = d*m <= X (m = 1 only if d ends with exponent >= 2) with tau(n) | n, where d has
// largest prime SP[ip] <= 61 and m has all primes > SP[ip].
static u64 dfs(u64 d, u64 td, int ip, bool last_ge2) {
    const u64 P = SP[ip];
    const u64 mis = td / std::gcd(td, d);
    const u64 smis = mis > 1 ? spf_small(mis) : UINT64_MAX;
    if (smis <= P) return 0;
    u64 c = 0;
    if (last_ge2 && mis == 1) c++;
    const u64 y = X / d;
    if (y > P) {  // n = d q, q prime in (P, min(y, 61)]
        const u64 top = std::min<u64>(y, 61);
        if (d % (2 * td) == 0) c += pi(top) - pi(P);
        else {
            const u64 m = 2 * td / std::gcd(2 * td, d);
            if (m > P && m <= top && smallisp[m]) c++;
        }
    }
    for (int j = ip + 1; j < 18; j++) {
        const u64 p = SP[j];
        if (p > smis || p * p > y) break;
        if (p * p < y) c += dfs(d * p, 2 * td, j, false);
        u64 pe = p * p;
        for (u64 e = 2;; e++) {
            c += dfs(d * pe, td * (e + 1), j, true);
            if (pe > y / p) break;
            pe *= p;
        }
    }
    if (mis == 1) c += gen(d / td, y, IDX61);
    return c;
}

static u64 T_odd(u64 x, const std::vector<uint32_t>& spf) {  // # odd n <= x with tau(n) | n
    const u64 r = isqrt_u64(x);
    u64 c = 0;
    for (u64 s = 1; s <= r; s += 2) {
        u64 t = 1, m = s;
        while (m > 1) {
            const u64 p = spf[m];
            int e = 0;
            while (m % p == 0) { m /= p; e++; }
            t *= (u64)(2 * e + 1);
        }
        if ((s * s) % t == 0) c++;
    }
    return c;
}

int main(int argc, char** argv) {
    std::vector<u64> xs;
    if (argc >= 3 && !strcmp(argv[1], "-f")) {
        FILE* f = fopen(argv[2], "r");
        if (!f) { perror("x file"); return 2; }
        unsigned long long v;
        while (fscanf(f, "%llu", &v) == 1) xs.push_back(v);
        fclose(f);
    } else {
        for (int i = 1; i < argc; i++) xs.push_back(strtoull(argv[i], nullptr, 10));
    }
    if (xs.empty()) {
        fprintf(stderr, "usage: %s x1 [x2 ...] | -f file\n", argv[0]);
        return 2;
    }
    build_small();
    for (u64 x : xs) {
        if (x < 1 || x > 4000000000000000000ULL) { fprintf(stderr, "x out of range\n"); return 2; }
        const auto t0 = std::chrono::steady_clock::now();
        build_lucy(x);
        std::vector<uint32_t> spf(R + 2, 0);
        for (u64 i = 2; i <= R; i++)
            if (!spf[i])
                for (u64 j = i; j <= R; j += i)
                    if (!spf[j]) spf[j] = (uint32_t)i;
        u64 T = T_odd(x, spf) + T_odd(x / 2, spf);
        for (int a = 2; a < 64 && (1ULL << a) <= x; a++) T += dfs(1ULL << a, a + 1, 0, true);
        const double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
        printf("x=%" PRIu64 " T=%" PRIu64 " pi=%" PRIu64 " secs=%.2f\n", x, T, pi(x), secs);
        fflush(stdout);
    }
    return 0;
}
